import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.CommRing.lt_of_kronQ_rel, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronQ_rel.h15.inst : Not
      (@Eq Prop
        (@LT.lt Rat Rat.instLT
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        (@LT.lt Rat Rat.instLT
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronQ_rel.h15.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronQ_rel.h15.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronQ_rel.h15.prem2 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degQOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.var
                (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronQ_rel.h15.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQOk_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.var
                (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronQ_rel.h15.prem4 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQEq_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.var
                (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronQ_rel.h15 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.LawfulOrderLT α inst_3 inst_2] [inst_5 : @Std.IsLinearOrder α inst_2]
        [inst_6 :
          @Lean.Grind.OrderedRing α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            inst_2 inst_3
            (@Std.IsLinearPreorder.toIsPreorder α inst_2 (@Std.IsLinearOrder.toIsLinearPreorder α inst_2 inst_5))]
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
                  @Eq Bool
                      (Lean.Grind.CommRing.Expr.kronQEq_k K B invs
                        ((lhs.sub rhs).mul (Lean.Grind.CommRing.Expr.num (@Nat.cast Int instNatCastInt d))) (lhs'.sub rhs'))
                      Bool.true →
                    @Eq Prop
                      (@LT.lt α inst_3
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx lhs)
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs))
                      (@LT.lt α inst_3
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx lhs')
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_of_kronQ_rel.h15.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (Rat.instLE) (Rat.instLT) _ _ _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.lt_of_kronQ_rel.h15.prem0 HypCheckProof.Lean.Grind.CommRing.lt_of_kronQ_rel.h15.prem1 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_of_kronQ_rel.h15.prem2 HypCheckProof.Lean.Grind.CommRing.lt_of_kronQ_rel.h15.prem3 HypCheckProof.Lean.Grind.CommRing.lt_of_kronQ_rel.h15.prem4)

-- Lean.Grind.CommRing.lt_norm_polyC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h3.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k)
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).toExpr_k))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h3.prem0 : @Eq Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).combineC_k
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (Lean.Grind.CommRing.Poly.mulConstC_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal (rhs.sub lhs) c) →
          @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
            @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
              @Eq Lean.Grind.CommRing.Poly p
                  (rp.combineC_k c
                    (Lean.Grind.CommRing.Poly.mulConstC_k
                      (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) lp c)) →
                @Eq Prop
                  (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                    (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                  (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                    (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) rfl rfl rfl HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h3.prem0)

-- Lean.Grind.CommRing.lt_norm_polyC, hypothesis 18: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h18.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k)
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h18 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.LawfulOrderLT α inst_3 inst_2] [inst_5 : @Std.IsPreorder α inst_2]
        [inst_6 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_2 inst_3 inst_5]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
          @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (rp.combineC_k c
                  (Lean.Grind.CommRing.Poly.mulConstC_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) lp c)) →
              @Eq Prop
                (@LT.lt α inst_3 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LT.lt α inst_3 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h18.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).combineC_k
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (Lean.Grind.CommRing.Poly.mulConstC_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl rfl)

-- Lean.Grind.CommRing.lt_norm_polyC, hypothesis 19: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h19.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h19.prem0 : @Eq Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).combineC_k
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Poly.mulConstC_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h19 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.LawfulOrderLT α inst_3 inst_2] [inst_5 : @Std.IsPreorder α inst_2]
        [inst_6 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_2 inst_3 inst_5]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal (rhs.sub lhs) c) →
          @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (rp.combineC_k c
                  (Lean.Grind.CommRing.Poly.mulConstC_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) lp c)) →
              @Eq Prop
                (@LT.lt α inst_3 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LT.lt α inst_3 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h19.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h19.prem0)

-- Lean.Grind.CommRing.lt_norm_polyC, hypothesis 20: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h20.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k)
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h20.prem0 : @Eq Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combineC_k
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Poly.mulConstC_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h20 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.LawfulOrderLT α inst_3 inst_2] [inst_5 : @Std.IsPreorder α inst_2]
        [inst_6 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_2 inst_3 inst_5]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal (rhs.sub lhs) c) →
          @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (rp.combineC_k c
                  (Lean.Grind.CommRing.Poly.mulConstC_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) lp c)) →
              @Eq Prop
                (@LT.lt α inst_3 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LT.lt α inst_3 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h20.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h20.prem0)

-- Lean.Grind.CommRing.lt_norm_polyC, hypothesis 21: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h21.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k)
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h21 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.LawfulOrderLT α inst_3 inst_2] [inst_5 : @Std.IsPreorder α inst_2]
        [inst_6 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_2 inst_3 inst_5]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal (rhs.sub lhs) c) →
          @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
            @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
              @Eq Prop
                (@LT.lt α inst_3 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LT.lt α inst_3 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm_polyC.h21.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl rfl)

-- Lean.Grind.CommRing.le_norm_poly, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h15.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k)
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h15 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
          @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (rp.combine_k
                  (Lean.Grind.CommRing.Poly.mulConst_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) lp)) →
              @Eq Prop
                (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h15.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combine_k
      (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl rfl)

-- Lean.Grind.CommRing.le_norm_poly, hypothesis 16: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h16.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h16.prem0 : @Eq Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combine_k
        (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h16 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (rhs.sub lhs)) →
          @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (rp.combine_k
                  (Lean.Grind.CommRing.Poly.mulConst_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) lp)) →
              @Eq Prop
                (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h16.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h16.prem0)

-- Lean.Grind.CommRing.le_norm_poly, hypothesis 17: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h17.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k)
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h17.prem0 : @Eq Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).combine_k
        (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h17 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (rhs.sub lhs)) →
          @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (rp.combine_k
                  (Lean.Grind.CommRing.Poly.mulConst_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) lp)) →
              @Eq Prop
                (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h17.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h17.prem0)

-- Lean.Grind.CommRing.le_norm_poly, hypothesis 18: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h18.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k)
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h18 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (rhs.sub lhs)) →
          @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
            @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
              @Eq Prop
                (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_poly.h18.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl rfl)

-- Lean.Grind.CommRing.eq_of_kronQ_rel, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQ_rel.h10.inst : Not
      (@Eq Prop
        (@Eq Rat
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        (@Eq Rat
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQ_rel.h10.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQ_rel.h10.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQ_rel.h10.prem2 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degQOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.var
                (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQ_rel.h10.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQOk_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.var
                (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQ_rel.h10.prem4 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQEq_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.var
                (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQ_rel.h10 : Not
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
                  @Eq Bool
                      (Lean.Grind.CommRing.Expr.kronQEq_k K B invs
                        ((lhs.sub rhs).mul (Lean.Grind.CommRing.Expr.num (@Nat.cast Int instNatCastInt d))) (lhs'.sub rhs'))
                      Bool.true →
                    @Eq Prop
                      (@Eq α
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx lhs)
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs))
                      (@Eq α
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx lhs')
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_of_kronQ_rel.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.eq_of_kronQ_rel.h10.prem0 HypCheckProof.Lean.Grind.CommRing.eq_of_kronQ_rel.h10.prem1 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_of_kronQ_rel.h10.prem2 HypCheckProof.Lean.Grind.CommRing.eq_of_kronQ_rel.h10.prem3 HypCheckProof.Lean.Grind.CommRing.eq_of_kronQ_rel.h10.prem4)

-- Lean.Grind.CommRing.Stepwise.d_stepsPC, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsPC.h15.inst : Not
      (@Eq Int
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsPC.h15.prem0 : @Eq Bool
      (@Bool.rec (fun (x : Bool) => Bool) Bool.false
        (@Bool.rec (fun (x : Bool) => Bool) Bool.false
          (@Bool.rec (fun (x : Bool) => Bool) Bool.false
            (Lean.Grind.CommRing.PSumTree.ok_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (Lean.Grind.CommRing.PSumTree.leaf (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
            ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).maxDeg_k.blt
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  (Lean.Grind.CommRing.Mon.mult
                    { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                      k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                    Lean.Grind.CommRing.Mon.unit)
                  (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).maxDeg_k.blt
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (Nat.blt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsPC.h15.prem1 : @Eq Lean.Grind.CommRing.PPoly
      (Lean.Grind.CommRing.Poly.toPP_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      (Lean.Grind.CommRing.PPoly.combineN_k
        (fun (k : Int) => k.emod_k (Int.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (Lean.Grind.CommRing.Poly.toPP_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (Lean.Grind.CommRing.PSumTree.eval_k
          (fun (k : Int) => k.emod_k (Int.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (Lean.Grind.CommRing.PSumTree.leaf (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsPC.h15.prem2 : @Eq Int
      (@HMul.hMul Int Int Int
        (@instHMul Int
          (@Lean.Grind.Semiring.toMul Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsPC.h15 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k : Int) (init : Lean.Grind.CommRing.Poly) (B : Nat)
        (p₁ p : Lean.Grind.CommRing.Poly) (P : Lean.Grind.CommRing.PPoly) (t : Lean.Grind.CommRing.PSumTree),
        @Eq Bool
            (@Bool.rec (fun (x : Bool) => Bool) Bool.false
              (@Bool.rec (fun (x : Bool) => Bool) Bool.false
                (@Bool.rec (fun (x : Bool) => Bool) Bool.false (Lean.Grind.CommRing.PSumTree.ok_k B t) (p₁.maxDeg_k.blt B))
                (p.maxDeg_k.blt B))
              (Nat.blt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) B))
            Bool.true →
          @Eq Lean.Grind.CommRing.PPoly P (Lean.Grind.CommRing.Poly.toPP_k B p) →
            @Eq Lean.Grind.CommRing.PPoly P
                (Lean.Grind.CommRing.PPoly.combineN_k (fun (k : Int) => k.emod_k (Int.ofNat c))
                  (Lean.Grind.CommRing.Poly.toPP_k B p₁)
                  (Lean.Grind.CommRing.PSumTree.eval_k (fun (k : Int) => k.emod_k (Int.ofNat c)) B t)) →
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
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsPC.h15.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.toPP_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (Lean.Grind.CommRing.PSumTree.leaf (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsPC.h15.prem0 rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsPC.h15.prem1 HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsPC.h15.prem2)

-- Lean.Grind.AC.superpose_ac, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_ac.h13.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_ac.h13.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_ac.h13.prem1 : Std.Commutative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Commutative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_ac.h13.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_ac.h13.prem3 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.superpose_ac.h13 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.Commutative ctx.op}
        (r₁ c r₂ lhs₁ rhs₁ lhs₂ rhs₂ lhs rhs : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₂ →
            Lean.Grind.AC.Seq.denote ctx lhs = Lean.Grind.AC.Seq.denote ctx rhs := fun hc_h => HypCheckProof.Lean.Grind.AC.superpose_ac.h13.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.superpose_ac.h13.prem0 HypCheckProof.Lean.Grind.AC.superpose_ac.h13.prem1 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.superpose_ac.h13.prem2 HypCheckProof.Lean.Grind.AC.superpose_ac.h13.prem3)

-- Lean.Grind.CommRing.lt_false_of_kronS, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h13.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        False) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h13.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h13.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.LawfulOrderLT α inst_3 inst_2] [inst_5 : @Std.IsPreorder α inst_2]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronEval_k K B a) (Lean.Grind.CommRing.Expr.kronEval_k K B b) →
            @Eq Prop
              (@LT.lt α inst_3 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h13.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h13.prem0 HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h13.prem1)

-- Lean.Grind.CommRing.lt_false_of_kronS, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h14.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        False) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h14.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h14.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h14 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.LawfulOrderLT α inst_3 inst_2] [inst_5 : @Std.IsPreorder α inst_2]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Prop
              (@LT.lt α inst_3 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h14.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h14.prem0 HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronS.h14.prem1)

-- Lean.Grind.CommRing.le_true_of_toPPX_eqS, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h13.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h13.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        [inst_2 : LE α] [inst_3 : @Std.IsPreorder α inst_2] (ctx : Lean.Grind.CommRing.Context α) (B : Nat)
        (bal₁ bal₂ : Bool) (a b : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.PPoly),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b) →
            @Eq Prop
              (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h13.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h13.prem0 rfl)

-- Lean.Grind.CommRing.le_true_of_toPPX_eqS, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h14.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h14.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h14 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        [inst_2 : LE α] [inst_3 : @Std.IsPreorder α inst_2] (ctx : Lean.Grind.CommRing.Context α) (B : Nat)
        (bal₁ bal₂ : Bool) (a b : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.PPoly),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a) →
            @Eq Prop
              (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h14.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Bool.false
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h14.prem0 rfl)

-- Lean.Grind.Linarith.lt_lt_combine, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h11.inst : Not
      (@LT.lt Int Int.instLTInt
        (@Lean.Grind.Linarith.Poly.denote' Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.IntModule.toNatModule Int
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h11.prem0 : @LT.lt Int Int.instLTInt
      (@Lean.Grind.Linarith.Poly.denote' Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h11.prem1 : @LT.lt Int Int.instLTInt
      (@Lean.Grind.Linarith.Poly.denote' Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 inst_4]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
        @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
          @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₃)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h11.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h11.prem0 HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h11.prem1)

-- Lean.Grind.Linarith.lt_lt_combine, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h12.inst : Not
      (@LT.lt Int Int.instLTInt
        (@Lean.Grind.Linarith.Poly.denote' Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.IntModule.toNatModule Int
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h12.prem0 : @Eq Bool
      (Lean.Grind.Linarith.lt_lt_combine_cert
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        Lean.Grind.Linarith.Poly.nil)
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h12.prem1 : @LT.lt Int Int.instLTInt
      (@Lean.Grind.Linarith.Poly.denote' Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 inst_4]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.lt_lt_combine_cert p₁ p₂ p₃) Bool.true →
          @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₃)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h12.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h12.prem0 HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h12.prem1)

-- Lean.Grind.Linarith.lt_lt_combine, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h13.inst : Not
      (@LT.lt Int Int.instLTInt
        (@Lean.Grind.Linarith.Poly.denote' Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.IntModule.toNatModule Int
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h13.prem0 : @Eq Bool
      (Lean.Grind.Linarith.lt_lt_combine_cert
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        Lean.Grind.Linarith.Poly.nil)
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h13.prem1 : @LT.lt Int Int.instLTInt
      (@Lean.Grind.Linarith.Poly.denote' Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 inst_4]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.lt_lt_combine_cert p₁ p₂ p₃) Bool.true →
          @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₃)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h13.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h13.prem0 HypCheckProof.Lean.Grind.Linarith.lt_lt_combine.h13.prem1)

-- Lean.Grind.CommRing.Expr.eq_of_kronQLin, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h11.inst : Not
      (@Eq Rat
        (@Lean.Grind.CommRing.Expr.denote Rat
          (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
          (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Rat
          (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
          (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h11.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h11.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h11.prem2 : @Eq Bool
      (Lean.Grind.CommRing.Expr.linQOk_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h11.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQLinEq_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (invs : Lean.Grind.CommRing.InvVars),
        @Lean.Grind.CommRing.InvVars.ok α inst ctx invs →
          @Eq Bool invs.nonzero_k Bool.true →
            ∀ (a b : Lean.Grind.CommRing.Expr),
              @Eq Bool (Lean.Grind.CommRing.Expr.linQOk_k invs a b) Bool.true →
                @Eq Bool (Lean.Grind.CommRing.Expr.kronQLinEq_k K invs a b) Bool.true →
                  @Eq α
                    (@Lean.Grind.CommRing.Expr.denote α
                      (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx a)
                    (@Lean.Grind.CommRing.Expr.denote α
                      (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h11.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h11.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h11.prem1 (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h11.prem2 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h11.prem3)

-- Lean.Grind.CommRing.Expr.eq_of_kronQLin, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h12.inst : Not
      (@Eq Rat
        (@Lean.Grind.CommRing.Expr.denote Rat
          (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
          (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Rat
          (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
          (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h12.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h12.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h12.prem2 : @Eq Bool
      (Lean.Grind.CommRing.Expr.linQOk_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h12.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (invs : Lean.Grind.CommRing.InvVars),
        @Lean.Grind.CommRing.InvVars.ok α inst ctx invs →
          @Eq Bool invs.nonzero_k Bool.true →
            ∀ (a b : Lean.Grind.CommRing.Expr),
              @Eq Bool (Lean.Grind.CommRing.Expr.linQOk_k invs a b) Bool.true →
                @Eq Bool (Lean.Grind.CommRing.Expr.kronQOk_k K invs a b) Bool.true →
                  @Eq α
                    (@Lean.Grind.CommRing.Expr.denote α
                      (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx a)
                    (@Lean.Grind.CommRing.Expr.denote α
                      (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h12.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h12.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h12.prem1 (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h12.prem2 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQLin.h12.prem3)

-- Lean.Grind.Order.le_eq_true_of_lt_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h6.inst : Not
      (@Eq Prop
        (@LE.le UInt8 instLEUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HAdd.hAdd UInt8 UInt8 UInt8
            (@instHAdd UInt8
              (@Lean.Grind.Semiring.toAdd UInt8
                (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
            (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Int.cast UInt8
              (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h6.prem0 : @Eq Bool
      ((@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).ble'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h6.prem1 : @LT.lt UInt8 instLTUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α] {a b : α} {k₁ k₂ : Int},
        @Eq Bool (k₁.ble' k₂) Bool.true →
          @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
            @Eq Prop
              (@LE.le α inst a
                (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
                  (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
              True) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h6.inst (@hc_h (UInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h6.prem0 HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h6.prem1)

-- Lean.Grind.Order.le_eq_true_of_lt_k, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h11.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@HAdd.hAdd Int Int Int
            (@instHAdd Int
              (@Lean.Grind.Semiring.toAdd Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h11.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h11 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b : α}
        {k₁ k₂ : Int},
        @LT.lt α inst_1 a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @Eq Prop
            (@LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
            True) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h11.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h11.prem0)

-- Lean.Grind.Order.le_eq_true_of_lt_k, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h12.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@HAdd.hAdd Int Int Int
            (@instHAdd Int
              (@Lean.Grind.Semiring.toAdd Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h12.prem0 : @Eq Bool
      (Int.ble' (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h12 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b : α}
        {k₁ k₂ : Int},
        @Eq Bool (k₁.ble' k₂) Bool.true →
          @Eq Prop
            (@LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
            True) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h12.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt_k.h12.prem0)

-- Lean.Grind.Order.le_eq_false_of_lt_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h6.inst : Not
      (@Eq Prop
        (@LE.le UInt8 instLEUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@HAdd.hAdd UInt8 UInt8 UInt8
            (@instHAdd UInt8
              (@Lean.Grind.Semiring.toAdd UInt8
                (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
            (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Int.cast UInt8
              (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        False) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h6.prem0 : @Eq Bool
      ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))).ble'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h6.prem1 : @LT.lt UInt8 instLTUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α] (a b : α) (k₁ k₂ : Int),
        @Eq Bool
            ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁).ble'
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
          @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
            @Eq Prop
              (@LE.le α inst b
                (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
                  (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
              False) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h6.inst (@hc_h (UInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h6.prem0 HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h6.prem1)

-- Lean.Grind.Order.le_eq_false_of_lt_k, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h11.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@HAdd.hAdd Int Int Int
            (@instHAdd Int
              (@Lean.Grind.Semiring.toAdd Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        False) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h11.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h11 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] (a b : α)
        (k₁ k₂ : Int),
        @LT.lt α inst_1 a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @Eq Prop
            (@LE.le α inst b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
            False) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h11.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h11.prem0)

-- Lean.Grind.Order.le_eq_false_of_lt_k, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h12.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@HAdd.hAdd Int Int Int
            (@instHAdd Int
              (@Lean.Grind.Semiring.toAdd Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        False) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h12.prem0 : @Eq Bool
      ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).ble'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h12 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] (a b : α)
        (k₁ k₂ : Int),
        @Eq Bool
            ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁).ble'
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
          @Eq Prop
            (@LE.le α inst b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
            False) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h12.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h12.prem0)

-- Lean.Grind.Order.le_eq_true_of_le_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h6.inst : Not
      (@Eq Prop
        (@LE.le UInt8 instLEUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HAdd.hAdd UInt8 UInt8 UInt8
            (@instHAdd UInt8
              (@Lean.Grind.Semiring.toAdd UInt8
                (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
            (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Int.cast UInt8
              (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h6.prem0 : @Eq Bool
      ((@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).ble'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h6.prem1 : @LE.le UInt8 instLEUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α] {a b : α} {k₁ k₂ : Int},
        @Eq Bool (k₁.ble' k₂) Bool.true →
          @LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
            @Eq Prop
              (@LE.le α inst a
                (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
                  (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
              True) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h6.inst (@hc_h (UInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h6.prem0 HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h6.prem1)

-- Lean.Grind.Order.le_eq_true_of_le_k, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h11.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@HAdd.hAdd Int Int Int
            (@instHAdd Int
              (@Lean.Grind.Semiring.toAdd Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h11.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h11 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b : α}
        {k₁ k₂ : Int},
        @LE.le α inst a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @Eq Prop
            (@LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
            True) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h11.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h11.prem0)

-- Lean.Grind.Order.le_eq_true_of_le_k, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h12.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@HAdd.hAdd Int Int Int
            (@instHAdd Int
              (@Lean.Grind.Semiring.toAdd Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h12.prem0 : @Eq Bool
      (Int.ble' (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h12 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b : α}
        {k₁ k₂ : Int},
        @Eq Bool (k₁.ble' k₂) Bool.true →
          @Eq Prop
            (@LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
            True) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h12.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h12.prem0)

-- Lean.Grind.AC.diseq_simp_rhs_ac, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_ac.h10.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_ac.h10.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_ac.h10.prem1 : Std.Commutative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Commutative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_ac.h10.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_ac.h10.prem3 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) ≠
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_ac.h10 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.Commutative ctx.op}
        (c lhs₁ rhs₁ lhs₂ rhs₂ rhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ ≠ Lean.Grind.AC.Seq.denote ctx rhs₂ →
            Lean.Grind.AC.Seq.denote ctx lhs₂ ≠ Lean.Grind.AC.Seq.denote ctx rhs₂' := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_ac.h10.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_ac.h10.prem0 HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_ac.h10.prem1 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_ac.h10.prem2 HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_ac.h10.prem3)

-- Lean.Grind.CommRing.le_norm_exprC_nc, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_exprC_nc.h3.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_exprC_nc.h3.prem0 : @Eq Bool
      (Lean.Grind.CommRing.norm_cnstrC_nc_cert
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_exprC_nc.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Ring α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst) inst_1 inst_2 inst_3]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.norm_cnstrC_nc_cert lhs rhs lhs' rhs' c) Bool.true →
          @Eq Prop
            (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α inst ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α inst ctx rhs))
            (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α inst ctx lhs')
              (@Lean.Grind.CommRing.Expr.denote α inst ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_exprC_nc.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_norm_exprC_nc.h3.prem0)

-- Lean.Grind.CommRing.le_norm_exprC_nc, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_exprC_nc.h13.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_exprC_nc.h13 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Ring α]
        [inst_1 : @Lean.Grind.IsCharP α (@Lean.Grind.Ring.toSemiring α inst) c] [inst_2 : LE α] [inst_3 : LT α]
        [inst_4 : @Std.IsPreorder α inst_2]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst) inst_2 inst_3 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
        @Eq Prop
          (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denote α inst ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α inst ctx rhs))
          (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denote α inst ctx lhs')
            (@Lean.Grind.CommRing.Expr.denote α inst ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_exprC_nc.h13.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))

-- Lean.Grind.CommRing.Stepwise.coreKC, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreKC.h11.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreKC.h11.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            ((Lean.Grind.CommRing.Expr.var
                  (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))).beq'
        ((Lean.Grind.CommRing.Poly.kron_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))).add_k
          ((Int.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).mul_k
            (Lean.Grind.CommRing.PPoly.kron_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreKC.h11.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreKC.h11 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (lhs rhs : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly) (E : Lean.Grind.CommRing.PPoly),
        @Eq Bool
            ((Lean.Grind.CommRing.Expr.kronEval_k K B (lhs.sub rhs)).beq'
              ((Lean.Grind.CommRing.Poly.kron_k K B p).add_k ((Int.ofNat c).mul_k (Lean.Grind.CommRing.PPoly.kron_k K E))))
            Bool.true →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs) →
            @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.coreKC.h11.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Stepwise.coreKC.h11.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.coreKC.h11.prem1)

-- Lean.Grind.CommRing.Stepwise.coreKC, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreKC.h12.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreKC.h12.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.impOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreKC.h12.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreKC.h12 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (lhs rhs : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly) (E : Lean.Grind.CommRing.PPoly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.impOk_k K B c (lhs.sub rhs) p E) Bool.true →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs) →
            @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.coreKC.h12.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Stepwise.coreKC.h12.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.coreKC.h12.prem1)

-- Lean.Grind.CommRing.lt_norm_expr_nc, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_expr_nc.h12.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_expr_nc.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.Ring α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1]
        [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst) inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
        @Eq Prop
          (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α inst ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α inst ctx rhs))
          (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α inst ctx lhs')
            (@Lean.Grind.CommRing.Expr.denote α inst ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm_expr_nc.h12.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))

-- Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h9.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k.add
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h9.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).nonneg_k.and
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).nonneg_k)
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (a b : Lean.Grind.CommRing.Expr) (p q r : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Expr b (q.toExpr_k.add r.toExpr_k) →
          @Eq Lean.Grind.CommRing.Poly p (q.combine_k r) →
            @Eq Bool (q.nonneg_k.and r.nonneg_k) Bool.true →
              @Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h9.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k.add
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combine_k
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h9.prem0)

-- Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h10.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h10.prem0 : @Eq Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Expr.toPolySX_k Bool.false
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combine_k
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h10.prem1 : @Eq Bool
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).nonneg_k.and
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).nonneg_k)
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (a b : Lean.Grind.CommRing.Expr) (p q r : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolySX_k bal a) →
          @Eq Lean.Grind.CommRing.Poly p (q.combine_k r) →
            @Eq Bool (q.nonneg_k.and r.nonneg_k) Bool.true →
              @Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h10.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolySX_k Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h10.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h10.prem1)

-- Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h11.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k.add
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h11.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).nonneg_k.and
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).nonneg_k)
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (a b : Lean.Grind.CommRing.Expr) (p q r : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolySX_k bal a) →
          @Eq Lean.Grind.CommRing.Expr b (q.toExpr_k.add r.toExpr_k) →
            @Eq Bool (q.nonneg_k.and r.nonneg_k) Bool.true →
              @Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h11.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k.add
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolySX_k Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h11.prem0)

-- Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h12.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).toExpr_k.add
            (Lean.Grind.CommRing.Poly.num
                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))).toExpr_k))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h12.prem0 : @Eq Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Expr.toPolySX_k Bool.false
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).combine_k
        (Lean.Grind.CommRing.Poly.num
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (a b : Lean.Grind.CommRing.Expr) (p q r : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolySX_k bal a) →
          @Eq Lean.Grind.CommRing.Expr b (q.toExpr_k.add r.toExpr_k) →
            @Eq Lean.Grind.CommRing.Poly p (q.combine_k r) →
              @Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h12.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).toExpr_k.add
      (Lean.Grind.CommRing.Poly.num
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolySX_k Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) rfl rfl HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyS_eq_add_toExpr.h12.prem0)

-- Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_right, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_right.h10.inst : Not
      (@LE.le Int Int.instLEInt
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_right.h10.prem0 : @LE.le Int Int.instLEInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_right.h10 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.IsPartialOrder R inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2
            (@Std.IsPartialOrder.toIsPreorder R inst_1 inst_3)]
        [inst_5 : @Std.LawfulOrderLT R inst_2 inst_1] {a b c : R},
        @LE.le R inst_1
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
            c →
          @LE.le R inst_1
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) a c)
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) b c)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_right.h10.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_right.h10.prem0)

-- Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_right, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_right.h11.inst : Not
      (@LE.le Int Int.instLEInt
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_right.h11.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_right.h11 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.IsPartialOrder R inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2
            (@Std.IsPartialOrder.toIsPreorder R inst_1 inst_3)]
        [inst_5 : @Std.LawfulOrderLT R inst_2 inst_1] {a b c : R},
        @LE.le R inst_1 a b →
          @LE.le R inst_1
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) a c)
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) b c)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_right.h11.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_right.h11.prem0)

-- Lean.Grind.CommRing.lt_false_of_poly, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_poly.h12.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        False) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_poly.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs : Lean.Grind.CommRing.Expr) (n : Nat),
        @Eq Prop
          (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
          False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_poly.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))

-- Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg, hypothesis 4: necessary
/- FAILED: 14:214: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 } | 60:123: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.inst : ¬1 • 1 % 2 ≤ 2 • 1 % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.prem0 : 1 ≤ 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.prem1 : 1 % 2 ≤ 1 % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.prem2 : 0 % 2 ≤ 1 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.NatModule M] {k₁ k₂ : Nat} {x y : M},
        k₁ ≤ k₂ → x ≤ y → 0 ≤ x → k₁ • x ≤ k₂ • y := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule) (1) (2) (1) (1) HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.prem0 HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.prem1 HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.prem2)
-/

-- Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg, hypothesis 11: necessary
/- FAILED: 11:259: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => b ≤ a } | 36:269: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => b ≤ a }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.inst : ¬1 • 1 ≤ 0 • 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.prem0 : 0 ≤ 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.prem1 : 1 ≤ 1 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.NatModule M]
        [inst_3 : Lean.Grind.OrderedAdd M] {k₁ k₂ : Nat} {x y : M}, k₁ ≤ k₂ → x ≤ y → k₁ • x ≤ k₂ • y := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => b ≤ a : LE Nat }) (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule) (@Lean.Grind.OrderedAdd.mk _ _ _ _ (by (try dsimp only);   (intros; omega))) (0) (1) (1) (1) HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.prem0 HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.prem1)
-/

-- Lean.Grind.CommRing.Stepwise.d_stepk, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h12.inst : Not
      (@Eq Int
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h12.prem0 : @Eq Int
      (@HMul.hMul Int Int Int
        (@instHMul Int
          (@Lean.Grind.Semiring.toMul Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h12.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k₁ k : Int)
        (init p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly)
        (hs : List Nat),
        @Eq α
            (@HMul.hMul α α α
              (@instHMul α
                (@Lean.Grind.Semiring.toMul α
                  (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
              (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁) →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
            @Eq α
              (@HMul.hMul α α α
                (@instHMul α
                  (@Lean.Grind.Semiring.toMul α
                    (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst))
                  (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) k₁ k))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@List.nil Nat) HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h12.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h12.prem1)

-- Lean.Grind.CommRing.Stepwise.d_stepk, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h13.inst : Not
      (@Eq Int
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.mergeHint (@List.nil Nat)
            (Lean.Grind.CommRing.Poly.mulConst_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
            (Lean.Grind.CommRing.Poly.mulMon_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              Lean.Grind.CommRing.Mon.unit
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h13.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k₁ k : Int)
        (init p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly)
        (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHint hs (Lean.Grind.CommRing.Poly.mulConst_k k₁ p₁)
              (Lean.Grind.CommRing.Poly.mulMon_k k₂ m₂ p₂)) →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
            @Eq α
              (@HMul.hMul α α α
                (@instHMul α
                  (@Lean.Grind.Semiring.toMul α
                    (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst))
                  (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) k₁ k))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h13.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.mergeHint (@List.nil Nat)
      (Lean.Grind.CommRing.Poly.mulConst_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      (Lean.Grind.CommRing.Poly.mulMon_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        Lean.Grind.CommRing.Mon.unit (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h13.prem0)

-- Lean.Grind.CommRing.Stepwise.d_stepk, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h14.inst : Not
      (@Eq Int
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.mergeHint (@List.nil Nat)
            (Lean.Grind.CommRing.Poly.mulConst_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
            (Lean.Grind.CommRing.Poly.mulMon_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              Lean.Grind.CommRing.Mon.unit
              (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h14.prem0 : @Eq Int
      (@HMul.hMul Int Int Int
        (@instHMul Int
          (@Lean.Grind.Semiring.toMul Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h14 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k₁ k : Int)
        (init p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly)
        (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHint hs (Lean.Grind.CommRing.Poly.mulConst_k k₁ p₁)
              (Lean.Grind.CommRing.Poly.mulMon_k k₂ m₂ p₂)) →
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
                (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst))
                  (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) k₁ k))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h14.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.mergeHint (@List.nil Nat)
      (Lean.Grind.CommRing.Poly.mulConst_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Poly.mulMon_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        Lean.Grind.CommRing.Mon.unit
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepk.h14.prem0)

-- Lean.Grind.AC.eq_simp_rhs_suffix, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h9.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h9.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h9.prem1 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h9.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h9 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op}
        (lhs₁ rhs₁ head lhs₂ rhs₂ rhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₂ →
            Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₂' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h9.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h9.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h9.prem1 HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h9.prem2)

-- Lean.Grind.AC.eq_simp_rhs_suffix, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h11.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h11.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h11.prem1 : Lean.Grind.AC.simp_suffix_cert (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0)
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h11.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h11 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op}
        (lhs₁ rhs₁ head lhs₂ rhs₂ rhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.simp_suffix_cert lhs₁ rhs₁ head rhs₂ rhs₂' = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
            Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₂' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h11.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h11.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h11.prem1 HypCheckProof.Lean.Grind.AC.eq_simp_rhs_suffix.h11.prem2)

-- Lean.Grind.AC.eq_simp_lhs_suffix, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h9.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h9.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h9.prem1 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h9.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h9 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op}
        (lhs₁ rhs₁ head lhs₂ rhs₂ lhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₂ →
            Lean.Grind.AC.Seq.denote ctx lhs₂' = Lean.Grind.AC.Seq.denote ctx rhs₂ := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h9.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h9.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h9.prem1 HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h9.prem2)

-- Lean.Grind.AC.eq_simp_lhs_suffix, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h11.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h11.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h11.prem1 : Lean.Grind.AC.simp_suffix_cert (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0)
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h11.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h11 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op}
        (lhs₁ rhs₁ head lhs₂ rhs₂ lhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.simp_suffix_cert lhs₁ rhs₁ head lhs₂ lhs₂' = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
            Lean.Grind.AC.Seq.denote ctx lhs₂' = Lean.Grind.AC.Seq.denote ctx rhs₂ := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h11.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h11.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h11.prem1 HypCheckProof.Lean.Grind.AC.eq_simp_lhs_suffix.h11.prem2)

-- Lean.Grind.AC.diseq_simp_lhs_suffix, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_suffix.h9.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_suffix.h9.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_suffix.h9.prem1 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_suffix.h9.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) ≠
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_suffix.h9 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op}
        (lhs₁ rhs₁ head lhs₂ rhs₂ lhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ ≠ Lean.Grind.AC.Seq.denote ctx rhs₂ →
            Lean.Grind.AC.Seq.denote ctx lhs₂' ≠ Lean.Grind.AC.Seq.denote ctx rhs₂ := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_suffix.h9.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_suffix.h9.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_suffix.h9.prem1 HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_suffix.h9.prem2)

-- Int.Internal.Linear.le_combine_coeff_rfl, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.div_k 1 (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h6.prem0 : (Int.blt' 0 1 &&
        Int.Internal.Linear.Poly.divCoeffs_k 1 (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h6.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h6.prem2 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p p₃ : Int.Internal.Linear.Poly) (k : Int),
        (Int.blt' 0 k && Int.Internal.Linear.Poly.divCoeffs_k k p) = Bool.true →
          p₃ = Int.Internal.Linear.Poly.div_k k p →
            Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 →
              Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h6.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.div_k 1 (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) (1) HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h6.prem0 rfl HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h6.prem1 HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h6.prem2)

-- Int.Internal.Linear.le_combine_coeff_rfl, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h7.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h7.prem0 : Int.Internal.Linear.Poly.num 1 =
      Int.Internal.Linear.Poly.div_k (-1)
        (Int.Internal.Linear.Poly.combine_mul_k (Int.ofNat (Int.Internal.Linear.Poly.num (-1)).leadCoeff_k.natAbs_k)
          (Int.ofNat (Int.Internal.Linear.Poly.num 0).leadCoeff_k.natAbs_k) (Int.Internal.Linear.Poly.num 0)
          (Int.Internal.Linear.Poly.num (-1))) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h7.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h7.prem2 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num (-1)) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p p₃ : Int.Internal.Linear.Poly) (k : Int),
        p =
            Int.Internal.Linear.Poly.combine_mul_k (Int.ofNat p₂.leadCoeff_k.natAbs_k) (Int.ofNat p₁.leadCoeff_k.natAbs_k)
              p₁ p₂ →
          p₃ = Int.Internal.Linear.Poly.div_k k p →
            Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 →
              Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h7.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num (-1)) (Int.Internal.Linear.Poly.combine_mul_k (Int.ofNat (Int.Internal.Linear.Poly.num (-1)).leadCoeff_k.natAbs_k)
      (Int.ofNat (Int.Internal.Linear.Poly.num 0).leadCoeff_k.natAbs_k) (Int.Internal.Linear.Poly.num 0)
      (Int.Internal.Linear.Poly.num (-1))) (Int.Internal.Linear.Poly.num 1) (-1) rfl HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h7.prem0 HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h7.prem1 HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h7.prem2)

-- Int.Internal.Linear.le_combine_coeff_rfl, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h8.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h8.prem0 : (Int.blt' 0 1 &&
        Int.Internal.Linear.Poly.divCoeffs_k 1
          (Int.Internal.Linear.Poly.combine_mul_k (Int.ofNat (Int.Internal.Linear.Poly.num 0).leadCoeff_k.natAbs_k)
            (Int.ofNat (Int.Internal.Linear.Poly.num 0).leadCoeff_k.natAbs_k) (Int.Internal.Linear.Poly.num 0)
            (Int.Internal.Linear.Poly.num 0))) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h8.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h8.prem2 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h8 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p p₃ : Int.Internal.Linear.Poly) (k : Int),
        p =
            Int.Internal.Linear.Poly.combine_mul_k (Int.ofNat p₂.leadCoeff_k.natAbs_k) (Int.ofNat p₁.leadCoeff_k.natAbs_k)
              p₁ p₂ →
          (Int.blt' 0 k && Int.Internal.Linear.Poly.divCoeffs_k k p) = Bool.true →
            Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 →
              Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h8.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.combine_mul_k (Int.ofNat (Int.Internal.Linear.Poly.num 0).leadCoeff_k.natAbs_k)
      (Int.ofNat (Int.Internal.Linear.Poly.num 0).leadCoeff_k.natAbs_k) (Int.Internal.Linear.Poly.num 0)
      (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (1) rfl HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h8.prem0 HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h8.prem1 HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h8.prem2)

-- Int.Internal.Linear.le_combine_coeff_rfl, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h9.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h9.prem0 : (Int.blt' 0 1 &&
        Int.Internal.Linear.Poly.divCoeffs_k 1
          (Int.Internal.Linear.Poly.combine_mul_k (Int.ofNat (Int.Internal.Linear.Poly.num 0).leadCoeff_k.natAbs_k)
            (Int.ofNat (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).leadCoeff_k.natAbs_k)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0))) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h9.prem1 : Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0) =
      Int.Internal.Linear.Poly.div_k 1
        (Int.Internal.Linear.Poly.combine_mul_k (Int.ofNat (Int.Internal.Linear.Poly.num 0).leadCoeff_k.natAbs_k)
          (Int.ofNat (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).leadCoeff_k.natAbs_k)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h9.prem2 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h9 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p p₃ : Int.Internal.Linear.Poly) (k : Int),
        p =
            Int.Internal.Linear.Poly.combine_mul_k (Int.ofNat p₂.leadCoeff_k.natAbs_k) (Int.ofNat p₁.leadCoeff_k.natAbs_k)
              p₁ p₂ →
          (Int.blt' 0 k && Int.Internal.Linear.Poly.divCoeffs_k k p) = Bool.true →
            p₃ = Int.Internal.Linear.Poly.div_k k p →
              Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h9.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.combine_mul_k (Int.ofNat (Int.Internal.Linear.Poly.num 0).leadCoeff_k.natAbs_k)
      (Int.ofNat (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).leadCoeff_k.natAbs_k)
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (1) rfl HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h9.prem0 HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h9.prem1 HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h9.prem2)

-- Int.Internal.Linear.le_combine_coeff_rfl, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h10.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h10.prem0 : (Int.blt' 0 1 &&
        Int.Internal.Linear.Poly.divCoeffs_k 1
          (Int.Internal.Linear.Poly.combine_mul_k
            (Int.ofNat (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).leadCoeff_k.natAbs_k)
            (Int.ofNat (Int.Internal.Linear.Poly.num 0).leadCoeff_k.natAbs_k) (Int.Internal.Linear.Poly.num 0)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)))) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h10.prem1 : Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0) =
      Int.Internal.Linear.Poly.div_k 1
        (Int.Internal.Linear.Poly.combine_mul_k
          (Int.ofNat (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).leadCoeff_k.natAbs_k)
          (Int.ofNat (Int.Internal.Linear.Poly.num 0).leadCoeff_k.natAbs_k) (Int.Internal.Linear.Poly.num 0)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h10.prem2 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h10 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p p₃ : Int.Internal.Linear.Poly) (k : Int),
        p =
            Int.Internal.Linear.Poly.combine_mul_k (Int.ofNat p₂.leadCoeff_k.natAbs_k) (Int.ofNat p₁.leadCoeff_k.natAbs_k)
              p₁ p₂ →
          (Int.blt' 0 k && Int.Internal.Linear.Poly.divCoeffs_k k p) = Bool.true →
            p₃ = Int.Internal.Linear.Poly.div_k k p →
              Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h10.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.combine_mul_k
      (Int.ofNat (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).leadCoeff_k.natAbs_k)
      (Int.ofNat (Int.Internal.Linear.Poly.num 0).leadCoeff_k.natAbs_k) (Int.Internal.Linear.Poly.num 0)
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (1) rfl HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h10.prem0 HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h10.prem1 HypCheckProof.Int.Internal.Linear.le_combine_coeff_rfl.h10.prem2)

-- Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h9.inst : ¬0 ≤ 1 * -1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h9.prem0 : -1 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h9 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Lean.Grind.OrderedRing R] [inst_5 : Std.LawfulOrderLT R] {a b : R}, b ≤ 0 → 0 ≤ a * b := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt.toRing) (Int.instLEInt) (Int.instLTInt) _ _ _ (1) (-1) HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h9.prem0)

-- Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h10.inst : ¬0 ≤ -1 * 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h10.prem0 : -1 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h10 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Lean.Grind.OrderedRing R] [inst_5 : Std.LawfulOrderLT R] {a b : R}, a ≤ 0 → 0 ≤ a * b := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt.toRing) (Int.instLEInt) (Int.instLTInt) _ _ _ (-1) (1) HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h10.prem0)

-- Lean.Grind.OrderedRing.mul_nonneg, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h9.inst : Not
      (@LE.le Int Int.instLEInt
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h9.prem0 : @LE.le Int Int.instLEInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h9 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.IsPartialOrder R inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2
            (@Std.IsPartialOrder.toIsPreorder R inst_1 inst_3)]
        [inst_5 : @Std.LawfulOrderLT R inst_2 inst_1] {a b : R},
        @LE.le R inst_1
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
            b →
          @LE.le R inst_1
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) a b)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h9.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h9.prem0)

-- Lean.Grind.OrderedRing.mul_nonneg, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h10.inst : Not
      (@LE.le Int Int.instLEInt
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h10.prem0 : @LE.le Int Int.instLEInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h10 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.IsPartialOrder R inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2
            (@Std.IsPartialOrder.toIsPreorder R inst_1 inst_3)]
        [inst_5 : @Std.LawfulOrderLT R inst_2 inst_1] {a b : R},
        @LE.le R inst_1
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
            a →
          @LE.le R inst_1
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) a b)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h10.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h10.prem0)

-- Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg.h9.inst : ¬0 * -1 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg.h9.prem0 : -1 < 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg.h9 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Lean.Grind.OrderedRing R] [inst_5 : Std.LawfulOrderLT R] {a b : R}, b < 0 → a * b < 0 := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt.toRing) (Int.instLEInt) (Int.instLTInt) _ _ _ (0) (-1) HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg.h9.prem0)

-- Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg.h10.inst : Not
      (@LT.lt Int Int.instLTInt
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg.h10.prem0 : @LT.lt Int Int.instLTInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg.h10 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.IsPartialOrder R inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2
            (@Std.IsPartialOrder.toIsPreorder R inst_1 inst_3)]
        [inst_5 : @Std.LawfulOrderLT R inst_2 inst_1] {a b : R},
        @LT.lt R inst_2
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
            a →
          @LT.lt R inst_2
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) a b)
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg.h10.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_pos_of_neg.h10.prem0)

-- Lean.Grind.Field.IsOrdered.mul_inv_lt_iff_lt_mul, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_inv_lt_iff_lt_mul.h10.inst : Not
      (Iff
        (@LT.lt Rat Rat.instLT
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
              (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
        (@LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_inv_lt_iff_lt_mul.h10 : Not
      (∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R]
        [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1] [inst_4 : @Std.IsLinearOrder R inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing R
            (@Lean.Grind.CommSemiring.toSemiring R
              (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))
            inst_1 inst_2
            (@Std.IsLinearPreorder.toIsPreorder R inst_1 (@Std.IsLinearOrder.toIsLinearPreorder R inst_1 inst_4))]
        (a c : R) {b : R},
        Iff
          (@LT.lt R inst_2
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              a (@Inv.inv R (@Lean.Grind.Field.toInv R inst) b))
            c)
          (@LT.lt R inst_2 a
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              c b))) := fun hc_h => HypCheckProof.Lean.Grind.Field.IsOrdered.mul_inv_lt_iff_lt_mul.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.Field.IsOrdered.lt_mul_inv_iff_mul_lt, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.lt_mul_inv_iff_mul_lt.h10.inst : Not
      (Iff
        (@LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
            (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
              (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))))
        (@LT.lt Rat Rat.instLT
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.lt_mul_inv_iff_mul_lt.h10 : Not
      (∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R]
        [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1] [inst_4 : @Std.IsLinearOrder R inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing R
            (@Lean.Grind.CommSemiring.toSemiring R
              (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))
            inst_1 inst_2
            (@Std.IsLinearPreorder.toIsPreorder R inst_1 (@Std.IsLinearOrder.toIsLinearPreorder R inst_1 inst_4))]
        (a b : R) {c : R},
        Iff
          (@LT.lt R inst_2 a
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              b (@Inv.inv R (@Lean.Grind.Field.toInv R inst) c)))
          (@LT.lt R inst_2
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              a c)
            b)) := fun hc_h => HypCheckProof.Lean.Grind.Field.IsOrdered.lt_mul_inv_iff_mul_lt.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.OrderedAdd.add_lt_right, hypothesis 4: necessary
/- FAILED: 8:218: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 } | 40:123: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right.h4.inst : ¬(1 + 0) % 2 < (1 + 1) % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right.h4.prem0 : 0 % 2 < 1 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M] [inst_3 : LT M]
        [inst : Std.LawfulOrderLT M] {a b : M} (c : M), a < b → c + a < c + b := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) ({ lt := fun (a b : Nat) => a % 2 < b % 2 : LT Nat }) (@Std.LawfulOrderLT.mk _ _ _ (by (try dsimp only);   (intros; omega))) (0) (1) (1) HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right.h4.prem0)
-/

-- Lean.Grind.OrderedAdd.add_lt_right, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right.h6.inst : ¬(1 + 0) % 2 < (1 + 1) % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right.h6.prem0 : 0 % 2 < 1 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right.h6 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M]
        [inst : Lean.Grind.OrderedAdd M] [inst : LT M] {a b : M} (c : M), a < b → c + a < c + b := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right.h6.inst (@hc_h (Nat) (instLENat) _ (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) _ ({ lt := fun (a b : Nat) => a % 2 < b % 2 : LT Nat }) (0) (1) (1) HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right.h6.prem0)

-- Lean.Grind.CommRing.Expr.eq_of_kronS, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronS.h9.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronS.h9.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronS.h9.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronS.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronEval_k K B a) (Lean.Grind.CommRing.Expr.kronEval_k K B b) →
            @Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronS.h9.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronS.h9.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronS.h9.prem1)

-- Lean.Grind.CommRing.Expr.eq_of_kronS, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronS.h10.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronS.h10.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronS.h10.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronS.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronS.h10.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronS.h10.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronS.h10.prem1)

-- Lean.Grind.Field.NormNum.sub_eq, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.sub_eq.h8.inst : Not
      (@Eq Rat
        (@HSub.hSub Rat Rat Rat
          (@instHSub Rat
            (@Lean.Grind.Ring.toSub Rat
              (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.sub_eq.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (a b : α) (v₁ v₂ v : Rat),
        @Eq α a (@Lean.Grind.Field.NormNum.ofRat α inst v₁) →
          @Eq α b (@Lean.Grind.Field.NormNum.ofRat α inst v₂) →
            @Eq α
              (@HSub.hSub α α α
                (@instHSub α
                  (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))))
                a b)
              (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.sub_eq.h8.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) rfl rfl)

-- Lean.Grind.Field.NormNum.sub_eq, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.sub_eq.h9.inst : Not
      (@Eq Rat
        (@HSub.hSub Rat Rat Rat
          (@instHSub Rat
            (@Lean.Grind.Ring.toSub Rat
              (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.sub_eq.h9.prem0 : @Eq Bool
      (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat)
        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
      Bool.true := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.sub_eq.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (a b : α) (v₁ v₂ v : Rat),
        @Eq Bool
            (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat) v
              (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) v₁ v₂))
            Bool.true →
          @Eq α b (@Lean.Grind.Field.NormNum.ofRat α inst v₂) →
            @Eq α
              (@HSub.hSub α α α
                (@instHSub α
                  (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))))
                a b)
              (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.sub_eq.h9.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Field.NormNum.sub_eq.h9.prem0 rfl)

-- Lean.Grind.Field.NormNum.sub_eq, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.sub_eq.h10.inst : Not
      (@Eq Rat
        (@HSub.hSub Rat Rat Rat
          (@instHSub Rat
            (@Lean.Grind.Ring.toSub Rat
              (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.sub_eq.h10.prem0 : @Eq Bool
      (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat)
        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
      Bool.true := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.sub_eq.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (a b : α) (v₁ v₂ v : Rat),
        @Eq Bool
            (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat) v
              (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) v₁ v₂))
            Bool.true →
          @Eq α a (@Lean.Grind.Field.NormNum.ofRat α inst v₁) →
            @Eq α
              (@HSub.hSub α α α
                (@instHSub α
                  (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))))
                a b)
              (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.sub_eq.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Field.NormNum.sub_eq.h10.prem0 rfl)

-- Lean.Grind.CommRing.eq_true_of_toPPX_eq, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eq.h9.inst : Not
      (@Eq Prop
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.branch Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.branch Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eq.h9.prem0 : @Eq Lean.Grind.CommRing.PPoly
      (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Bool.false
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Bool.false
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eq.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool)
        (a b : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.PPoly),
        @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a) →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b) →
            @Eq Prop
              (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eq.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.branch Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Bool.false
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) rfl HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eq.h9.prem0)

-- Lean.Grind.CommRing.eq_true_of_toPPX_eq, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eq.h10.inst : Not
      (@Eq Prop
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eq.h10.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eq.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool)
        (a b : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.PPoly),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b) →
            @Eq Prop
              (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eq.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Bool.false
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eq.h10.prem0 rfl)

-- Lean.Grind.CommRing.eq_true_of_toPPX_eq, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eq.h11.inst : Not
      (@Eq Prop
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eq.h11.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eq.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool)
        (a b : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.PPoly),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a) →
            @Eq Prop
              (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eq.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPPX_eq.h11.prem0 rfl)

-- Lean.Grind.CommRing.le_true_of_toPolyS, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPolyS.h10.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        True) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPolyS.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (bal₁ bal₂ : Bool) (lhs rhs : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolySX_k bal₂ rhs) →
          @Eq Prop
            (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx rhs))
            True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_toPolyS.h10.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolySX_k Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl)

-- Lean.Grind.CommRing.le_true_of_toPolyS, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPolyS.h11.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        True) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPolyS.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (bal₁ bal₂ : Bool) (lhs rhs : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolySX_k bal₁ lhs) →
          @Eq Prop
            (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx rhs))
            True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_toPolyS.h11.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolySX_k Bool.false
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) rfl)

-- Lean.Grind.CommRing.Stepwise.simp1, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h9.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h9.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h9.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly)
        (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
            @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@List.nil Nat) HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h9.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h9.prem1)

-- Lean.Grind.CommRing.Stepwise.simp1, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h10.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.mergeHint (@List.nil Nat)
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
            (Lean.Grind.CommRing.Poly.mulMon_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              Lean.Grind.CommRing.Mon.unit
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h10.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly)
        (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHint hs p₁ (Lean.Grind.CommRing.Poly.mulMon_k k₂ m₂ p₂)) →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
            @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.mergeHint (@List.nil Nat)
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Poly.mulMon_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        Lean.Grind.CommRing.Mon.unit (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h10.prem0)

-- Lean.Grind.CommRing.Stepwise.simp1, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h11.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.mergeHint (@List.nil Nat)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Poly.mulMon_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              Lean.Grind.CommRing.Mon.unit
              (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h11.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly)
        (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHint hs p₁ (Lean.Grind.CommRing.Poly.mulMon_k k₂ m₂ p₂)) →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
            @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.mergeHint (@List.nil Nat)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.mulMon_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        Lean.Grind.CommRing.Mon.unit
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1.h11.prem0)

-- Lean.Grind.Preorder.lt_trans, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Preorder.lt_trans.h3.inst : ¬0 ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Preorder.lt_trans.h3.prem0 : 0 ≠ 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Preorder.lt_trans.h3.prem1 : 1 ≠ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.Preorder.lt_trans.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst : Std.IsPreorder α] {a b c : α}, a < b → b < c → a < c := fun hc_h => HypCheckProof.Lean.Grind.Preorder.lt_trans.h3.inst (@hc_h (Nat) (instLENat) ({ lt := fun (a b : Nat) => a ≠ b : LT Nat }) _ (0) (1) (0) HypCheckProof.Lean.Grind.Preorder.lt_trans.h3.prem0 HypCheckProof.Lean.Grind.Preorder.lt_trans.h3.prem1)

-- Lean.Grind.CommRing.Expr.eq_of_kronLinS, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLinS.h8.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLinS.h8.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).linSOk_k
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLinS.h8.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLinS.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K a) (Lean.Grind.CommRing.Expr.kronLinEval_k K b) →
            @Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLinS.h8.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLinS.h8.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLinS.h8.prem1)

-- Lean.Grind.CommRing.Expr.eq_of_kronLinS, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLinS.h9.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLinS.h9.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linSOk_k
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLinS.h9.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLinS.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLinS.h9.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLinS.h9.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLinS.h9.prem1)

-- Lean.Grind.OrderedRing.lt_of_intCast_lt_intCast, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.lt_of_intCast_lt_intCast.h6.inst : Not
      (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.lt_of_intCast_lt_intCast.h6.prem0 : @LT.lt UInt8 instLTUInt8
      (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.lt_of_intCast_lt_intCast.h6 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1] (a b : Int),
        @LT.lt R inst_2 (@Int.cast R (@Lean.Grind.Ring.intCast R inst) a)
            (@Int.cast R (@Lean.Grind.Ring.intCast R inst) b) →
          @LT.lt Int Int.instLTInt a b) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.lt_of_intCast_lt_intCast.h6.inst (@hc_h (UInt8) (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (instLEUInt8) (instLTUInt8) _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.OrderedRing.lt_of_intCast_lt_intCast.h6.prem0)

-- Lean.Grind.OrderedRing.lt_of_intCast_lt_intCast, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.lt_of_intCast_lt_intCast.h9.inst : Not
      (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.lt_of_intCast_lt_intCast.h9 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1]
        [inst : @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2 inst_4] (a b : Int),
        @LT.lt Int Int.instLTInt a b) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.lt_of_intCast_lt_intCast.h9.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Lean.Grind.OrderedRing.le_of_intCast_le_intCast, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.le_of_intCast_le_intCast.h6.inst : Not
      (@LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.le_of_intCast_le_intCast.h6.prem0 : @LE.le UInt8 instLEUInt8
      (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.le_of_intCast_le_intCast.h6 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1] (a b : Int),
        @LE.le R inst_1 (@Int.cast R (@Lean.Grind.Ring.intCast R inst) a)
            (@Int.cast R (@Lean.Grind.Ring.intCast R inst) b) →
          @LE.le Int Int.instLEInt a b) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.le_of_intCast_le_intCast.h6.inst (@hc_h (UInt8) (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (instLEUInt8) (instLTUInt8) _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.OrderedRing.le_of_intCast_le_intCast.h6.prem0)

-- Lean.Grind.OrderedRing.le_of_intCast_le_intCast, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.le_of_intCast_le_intCast.h9.inst : Not
      (@LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.le_of_intCast_le_intCast.h9 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1]
        [inst : @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2 inst_4] (a b : Int),
        @LE.le Int Int.instLEInt a b) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.le_of_intCast_le_intCast.h9.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Lean.Grind.AC.superpose_tail_idempotent, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h3.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h3.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h3.prem1 : Lean.Grind.AC.superpose_tail_idempotent_cert 0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0)
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h3.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op} (x : Lean.Grind.AC.Var)
        (lhs₁ rhs₁ rhs : Lean.Grind.AC.Seq),
        Lean.Grind.AC.superpose_tail_idempotent_cert x lhs₁ rhs₁ rhs = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
            Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs := fun hc_h => HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h3.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h3.prem0 (0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h3.prem1 HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h3.prem2)

-- Lean.Grind.AC.superpose_tail_idempotent, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h8.inst : ¬Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 1) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h8.prem0 : Std.Associative
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   (intros; simp_all; done)))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h8.prem1 : Std.IdempotentOp
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }.op := (@Std.IdempotentOp.mk _ _ (by (try dsimp only);   (intros; simp_all; done)))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h8.prem2 : Lean.Grind.AC.Seq.denote
        {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h8 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.IdempotentOp ctx.op}
        (x : Lean.Grind.AC.Var) (lhs₁ rhs₁ rhs : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs := fun hc_h => HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h8.inst (@hc_h (Nat) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
      op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h8.prem0 HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h8.prem1 (0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 1) HypCheckProof.Lean.Grind.AC.superpose_tail_idempotent.h8.prem2)

-- Lean.Grind.Order.lt_eq_true_k, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_true_k.h9.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@HAdd.hAdd Int Int Int
            (@instHAdd Int
              (@Lean.Grind.Semiring.toAdd Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        True) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_eq_true_k.h9 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a : α} {k : Int},
        @Eq Prop
          (@LT.lt α inst_1 a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k)))
          True) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_eq_true_k.h9.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Lean.Grind.Order.lt_eq_false_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_k.h6.inst : Not
      (@Eq Prop
        (@LT.lt UInt8 instLTUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@HAdd.hAdd UInt8 UInt8 UInt8
            (@instHAdd UInt8
              (@Lean.Grind.Semiring.toAdd UInt8
                (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
            (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Int.cast UInt8
              (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))))
        False) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_k.h6.prem0 : @Eq Bool
      ((@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).ble'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_k.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst : @Std.IsPreorder α inst] [inst : Lean.Grind.Ring α] {a : α} {k : Int},
        @Eq Bool (k.ble' (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) Bool.true →
          @Eq Prop
            (@LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst))) a
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst) k)))
            False) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_eq_false_k.h6.inst (@hc_h (UInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.Order.lt_eq_false_k.h6.prem0)

-- Lean.Grind.Order.lt_eq_false_k, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_k.h9.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@HAdd.hAdd Int Int Int
            (@instHAdd Int
              (@Lean.Grind.Semiring.toAdd Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        False) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_k.h9 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a : α} {k : Int},
        @Eq Prop
          (@LT.lt α inst_1 a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k)))
          False) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_eq_false_k.h9.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))

-- Lean.Grind.CommRing.eq_of_kronLin_rel, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronLin_rel.h9.inst : Not
      (@Eq Prop
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronLin_rel.h9.prem0 : @Eq Bool
      (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).linOk_k
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronLin_rel.h9.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronLin_rel.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K : Nat)
        (l r l' r' : Lean.Grind.CommRing.Expr),
        @Eq Bool ((l.sub r).linOk_k (l'.sub r')) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K (l.sub r))
              (Lean.Grind.CommRing.Expr.kronLinEval_k K (l'.sub r')) →
            @Eq Prop
              (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r))
              (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l')
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_of_kronLin_rel.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.eq_of_kronLin_rel.h9.prem0 HypCheckProof.Lean.Grind.CommRing.eq_of_kronLin_rel.h9.prem1)

-- Lean.Grind.CommRing.eq_of_kronLin_rel, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronLin_rel.h10.inst : Not
      (@Eq Prop
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronLin_rel.h10.prem0 : @Eq Bool
      (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).linOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronLin_rel.h10.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronLin_rel.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K : Nat)
        (l r l' r' : Lean.Grind.CommRing.Expr),
        @Eq Bool ((l.sub r).linOk_k (l'.sub r')) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K (l.sub r) (l'.sub r')) Bool.true →
            @Eq Prop
              (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r))
              (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l')
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_of_kronLin_rel.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_of_kronLin_rel.h10.prem0 HypCheckProof.Lean.Grind.CommRing.eq_of_kronLin_rel.h10.prem1)

-- Lean.Grind.CommRing.lt_cancel_var, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h8.inst : Not
      (@LT.lt Int Int.instLTInt
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h8.prem0 : @Eq Int
      (@HMul.hMul Int Int Int
        (@instHMul Int
          (@Lean.Grind.Semiring.toMul Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@Lean.Grind.CommRing.Var.denote Int (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@OfNat.ofNat Int (nat_lit 1)
        (@Lean.Grind.Semiring.ofNat Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (nat_lit 1))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h8.prem1 : @LT.lt Int Int.instLTInt
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LT α] (ctx : Lean.Grind.CommRing.Context α) (c : Int)
        (x : Lean.Grind.CommRing.Var) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq α
            (@HMul.hMul α α α
              (@instHMul α
                (@Lean.Grind.Semiring.toMul α
                  (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
              (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) c)
              (@Lean.Grind.CommRing.Var.denote α ctx x))
            (@OfNat.ofNat α (nat_lit 1)
              (@Lean.Grind.Semiring.ofNat α
                (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) (nat_lit 1))) →
          @LT.lt α inst_1 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
            @LT.lt α inst_1 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLTInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h8.prem0 HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h8.prem1)

-- Lean.Grind.CommRing.lt_cancel_var, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h9.inst : ¬Lean.Grind.CommRing.Poly.denote (Lean.RArray.leaf (-1)) (Lean.Grind.CommRing.Poly.num 1) < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h9.prem0 : Lean.Grind.CommRing.cancel_var_cert 1 0
        (Lean.Grind.CommRing.Poly.add 1
          (Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num 0))
        (Lean.Grind.CommRing.Poly.num 1) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h9.prem1 : Lean.Grind.CommRing.Poly.denote (Lean.RArray.leaf (-1))
        (Lean.Grind.CommRing.Poly.add 1
          (Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num 0)) <
      0 := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h9 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LT α] (ctx : Lean.Grind.CommRing.Context α) (c : Int)
        (x : Lean.Grind.CommRing.Var) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        Lean.Grind.CommRing.cancel_var_cert c x p₁ p₂ = Bool.true →
          Lean.Grind.CommRing.Poly.denote ctx p₁ < 0 → Lean.Grind.CommRing.Poly.denote ctx p₂ < 0 := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLTInt) (Lean.RArray.leaf (-1)) (1) (0) (Lean.Grind.CommRing.Poly.add 1
      (Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num 0)) (Lean.Grind.CommRing.Poly.num 1) HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h9.prem0 HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h9.prem1)

-- Lean.Grind.CommRing.lt_cancel_var, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h10.inst : Not
      (@LT.lt Int Int.instLTInt
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h10.prem0 : @Eq Bool
      (Lean.Grind.CommRing.cancel_var_cert (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h10.prem1 : @Eq Int
      (@HMul.hMul Int Int Int
        (@instHMul Int
          (@Lean.Grind.Semiring.toMul Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@Lean.Grind.CommRing.Var.denote Int (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@OfNat.ofNat Int (nat_lit 1)
        (@Lean.Grind.Semiring.ofNat Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LT α] (ctx : Lean.Grind.CommRing.Context α) (c : Int)
        (x : Lean.Grind.CommRing.Var) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.cancel_var_cert c x p₁ p₂) Bool.true →
          @Eq α
              (@HMul.hMul α α α
                (@instHMul α
                  (@Lean.Grind.Semiring.toMul α
                    (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) c)
                (@Lean.Grind.CommRing.Var.denote α ctx x))
              (@OfNat.ofNat α (nat_lit 1)
                (@Lean.Grind.Semiring.ofNat α
                  (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) (nat_lit 1))) →
            @LT.lt α inst_1 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLTInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h10.prem0 HypCheckProof.Lean.Grind.CommRing.lt_cancel_var.h10.prem1)

-- Lean.Grind.CommRing.Expr.eq_of_kron, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kron.h8.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kron.h8.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kron.h8.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kron.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronEval_k K B a) (Lean.Grind.CommRing.Expr.kronEval_k K B b) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kron.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kron.h8.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kron.h8.prem1)

-- Lean.Grind.CommRing.Expr.eq_of_kron, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kron.h9.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kron.h9.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kron.h9.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kron.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kron.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kron.h9.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kron.h9.prem1)

-- Lean.Grind.OrderedAdd.add_lt_left_iff, hypothesis 4: necessary
/- FAILED: 5:221: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 } | 39:123: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left_iff.h4.inst : ¬(0 % 2 < 1 % 2 ↔ (0 + 1) % 2 < (1 + 1) % 2) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M] [inst_3 : LT M]
        [inst : Std.LawfulOrderLT M] {a b : M} (c : M), a < b ↔ a + c < b + c := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left_iff.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) ({ lt := fun (a b : Nat) => a % 2 < b % 2 : LT Nat }) (@Std.LawfulOrderLT.mk _ _ _ (by (try dsimp only);   (intros; omega))) (0) (1) (1))
-/

-- Lean.Grind.OrderedAdd.add_lt_left_iff, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left_iff.h6.inst : ¬(0 % 2 < 1 % 2 ↔ (0 + 1) % 2 < (1 + 1) % 2) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left_iff.h6 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M]
        [inst : Lean.Grind.OrderedAdd M] [inst : LT M] {a b : M} (c : M), a < b ↔ a + c < b + c := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left_iff.h6.inst (@hc_h (Nat) (instLENat) _ (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) _ ({ lt := fun (a b : Nat) => a % 2 < b % 2 : LT Nat }) (0) (1) (1))

-- Lean.Grind.OrderedAdd.zsmul_nonpos, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h7.inst : ¬-1 • -1 ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h7.prem0 : -1 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h7 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.IntModule M]
        [inst_3 : Lean.Grind.OrderedAdd M] {k : Int} {a : M}, a ≤ 0 → k • a ≤ 0 := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h7.inst (@hc_h (Int) (Int.instLEInt) _ (Lean.Grind.Ring.toIntModule) _ (-1) (-1) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h7.prem0)

-- Lean.Grind.OrderedAdd.zsmul_nonpos, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h8.inst : Not
      (@LE.le Int Int.instLEInt
        (@HSMul.hSMul Int Int Int
          (@instHSMul Int Int
            (@Lean.Grind.IntModule.zsmul Int
              (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.IntModule.toNatModule Int
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h8.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h8 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : @Std.IsPreorder M inst] [inst_2 : Lean.Grind.IntModule M]
        [inst_3 :
          @Lean.Grind.OrderedAdd M
            (@instHAdd M
              (@Lean.Grind.AddCommMonoid.toAdd M
                (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2))))
            inst inst_1]
        {k : Int} {a : M},
        @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k →
          @LE.le M inst (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k a)
            (@OfNat.ofNat M (nat_lit 0)
              (@Zero.toOfNat0 M
                (@Lean.Grind.AddCommMonoid.toZero M
                  (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2)))))) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h8.inst (@hc_h (Int) (Int.instLEInt) _ (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h8.prem0)

-- Lean.Grind.Linarith.eq_diseq_subst1, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h7.inst : Not
      (@Ne Int
        (@Lean.Grind.Linarith.Poly.denote' Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.IntModule.toNatModule Int
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h7.prem0 : @Eq Int
      (@Lean.Grind.Linarith.Poly.denote' Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h7.prem1 : @Ne Int
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
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] (ctx : Lean.Grind.Linarith.Context α) (k : Int)
        (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
        @Eq α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
          @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₃)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h7.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h7.prem0 HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h7.prem1)

-- Lean.Grind.Linarith.eq_diseq_subst1, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h8.inst : Not
      (@Ne Int
        (@Lean.Grind.Linarith.Poly.denote' Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.IntModule.toNatModule Int
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h8.prem0 : @Eq Bool
      (Lean.Grind.Linarith.eq_diseq_subst1_cert (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        Lean.Grind.Linarith.Poly.nil)
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h8.prem1 : @Ne Int
      (@Lean.Grind.Linarith.Poly.denote' Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] (ctx : Lean.Grind.Linarith.Context α) (k : Int)
        (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.eq_diseq_subst1_cert k p₁ p₂ p₃) Bool.true →
          @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₃)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h8.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h8.prem0 HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h8.prem1)

-- Lean.Grind.Linarith.eq_diseq_subst1, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h9.inst : Not
      (@Ne Int
        (@Lean.Grind.Linarith.Poly.denote' Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.IntModule.toNatModule Int
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h9.prem0 : @Eq Bool
      (Lean.Grind.Linarith.eq_diseq_subst1_cert (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        Lean.Grind.Linarith.Poly.nil Lean.Grind.Linarith.Poly.nil Lean.Grind.Linarith.Poly.nil)
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h9.prem1 : @Eq Int
      (@Lean.Grind.Linarith.Poly.denote' Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] (ctx : Lean.Grind.Linarith.Context α) (k : Int)
        (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.eq_diseq_subst1_cert k p₁ p₂ p₃) Bool.true →
          @Eq α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₃)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h9.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h9.prem0 HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst1.h9.prem1)

-- Lean.Grind.CommRing.eq_false_of_poly, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_false_of_poly.h8.inst : Not
      (@Eq Prop
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        False) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_false_of_poly.h8.prem0 : @Eq Bool (Int.beqZero_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Bool.false := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_false_of_poly.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs : Lean.Grind.CommRing.Expr) (k : Int),
        @Eq Bool k.beqZero_k Bool.false →
          @Eq Prop
            (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_false_of_poly.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.CommRing.eq_false_of_poly.h8.prem0)

-- Lean.Grind.CommRing.eq_false_of_poly, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_false_of_poly.h9.inst : Not
      (@Eq Prop
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        False) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_false_of_poly.h9.prem0 : @Eq Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.eq_false_of_poly.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs : Lean.Grind.CommRing.Expr) (k : Int),
        @Eq Lean.Grind.CommRing.Poly (Lean.Grind.CommRing.Expr.toPolyX_k bal (lhs.sub rhs))
            (Lean.Grind.CommRing.Poly.num k) →
          @Eq Prop
            (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_false_of_poly.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.CommRing.eq_false_of_poly.h9.prem0)

-- Lean.Grind.OrderedRing.neg_intCast_of_neg, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.neg_intCast_of_neg.h6.inst : Not
      (@LT.lt UInt8 instLTUInt8
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@OfNat.ofNat UInt8 (nat_lit 0)
          (@Zero.toOfNat0 UInt8
            (@Lean.Grind.AddCommMonoid.toZero UInt8
              (@Lean.Grind.NatModule.toAddCommMonoid UInt8
                (@Lean.Grind.Semiring.toNatModule UInt8
                  (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.neg_intCast_of_neg.h6.prem0 : @LT.lt Int Int.instLTInt (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.neg_intCast_of_neg.h6 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1] (a : Int),
        @LT.lt Int Int.instLTInt a (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          @LT.lt R inst_2 (@Int.cast R (@Lean.Grind.Ring.intCast R inst) a)
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.neg_intCast_of_neg.h6.inst (@hc_h (UInt8) (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (instLEUInt8) (instLTUInt8) _ _ (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.OrderedRing.neg_intCast_of_neg.h6.prem0)

-- Lean.Grind.OrderedRing.neg_intCast_of_neg, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.neg_intCast_of_neg.h8.inst : Not
      (@LT.lt Int Int.instLTInt
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.neg_intCast_of_neg.h8 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1]
        [inst_5 : @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2 inst_4] (a : Int),
        @LT.lt R inst_2 (@Int.cast R (@Lean.Grind.Ring.intCast R inst) a)
          (@OfNat.ofNat R (nat_lit 0)
            (@Zero.toOfNat0 R
              (@Lean.Grind.AddCommMonoid.toZero R
                (@Lean.Grind.NatModule.toAddCommMonoid R
                  (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.neg_intCast_of_neg.h8.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Lean.Grind.OrderedRing.nonneg_intCast_of_nonneg, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.nonneg_intCast_of_nonneg.h8.inst : Not
      (@LE.le Int Int.instLEInt
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.nonneg_intCast_of_nonneg.h8 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1]
        [inst_5 : @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2 inst_4] (a : Int),
        @LE.le R inst_1
          (@OfNat.ofNat R (nat_lit 0)
            (@Zero.toOfNat0 R
              (@Lean.Grind.AddCommMonoid.toZero R
                (@Lean.Grind.NatModule.toAddCommMonoid R
                  (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
          (@Int.cast R (@Lean.Grind.Ring.intCast R inst) a)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.nonneg_intCast_of_nonneg.h8.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))

-- Lean.Grind.AC.eq_erase_dup_rhs, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h3.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h3.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h3.prem1 : (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)).eraseDup.beq' (Lean.Grind.AC.Seq.var 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h3.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} (lhs rhs rhs' : Lean.Grind.AC.Seq),
        rhs.eraseDup.beq' rhs' = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs = Lean.Grind.AC.Seq.denote ctx rhs →
            Lean.Grind.AC.Seq.denote ctx lhs = Lean.Grind.AC.Seq.denote ctx rhs' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h3.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h3.prem0 (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h3.prem1 HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h3.prem2)

-- Lean.Grind.AC.eq_erase_dup_rhs, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h7.inst : ¬Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 1) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h7.prem0 : Std.Associative
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   (intros; simp_all; done)))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h7.prem1 : Std.IdempotentOp
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }.op := (@Std.IdempotentOp.mk _ _ (by (try dsimp only);   (intros; simp_all; done)))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h7.prem2 : Lean.Grind.AC.Seq.denote
        {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h7 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} {x : Std.IdempotentOp ctx.op}
        (lhs rhs rhs' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs = Lean.Grind.AC.Seq.denote ctx rhs →
          Lean.Grind.AC.Seq.denote ctx lhs = Lean.Grind.AC.Seq.denote ctx rhs' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h7.inst (@hc_h (Nat) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
      op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h7.prem0 HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h7.prem1 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 1) HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h7.prem2)

-- Lean.Grind.AC.eq_erase_dup_rhs, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h8.inst : ¬Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 1) =
        Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h8.prem0 : Std.Associative
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   (intros; simp_all; done)))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h8.prem1 : Std.IdempotentOp
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }.op := (@Std.IdempotentOp.mk _ _ (by (try dsimp only);   (intros; simp_all; done)))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h8.prem2 : (Lean.Grind.AC.Seq.var 0).eraseDup.beq' (Lean.Grind.AC.Seq.var 0) = Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h8 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} {x : Std.IdempotentOp ctx.op}
        (lhs rhs rhs' : Lean.Grind.AC.Seq),
        rhs.eraseDup.beq' rhs' = Bool.true → Lean.Grind.AC.Seq.denote ctx lhs = Lean.Grind.AC.Seq.denote ctx rhs' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h8.inst (@hc_h (Nat) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
      op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h8.prem0 HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h8.prem1 (Lean.Grind.AC.Seq.var 1) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.eq_erase_dup_rhs.h8.prem2)

-- Lean.Grind.Linarith.eq_coeff, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_coeff.h7.inst : Not
      (@Eq Int
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
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_coeff.h7.prem0 : @Eq Int
      (@Lean.Grind.Linarith.Poly.denote' Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.eq_coeff.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α]
        [inst_1 : @Lean.Grind.NoNatZeroDivisors α (@Lean.Grind.IntModule.toNatModule α inst)]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ : Lean.Grind.Linarith.Poly) (k : Nat),
        @Eq α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
          @Eq α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.eq_coeff.h7.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Lean.Grind.Linarith.eq_coeff.h7.prem0)

-- Lean.Grind.Linarith.eq_coeff, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_coeff.h8.inst : Not
      (@Eq Int
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
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_coeff.h8.prem0 : @Eq Bool
      (Lean.Grind.Linarith.eq_coeff_cert
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.eq_coeff.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α]
        [inst_1 : @Lean.Grind.NoNatZeroDivisors α (@Lean.Grind.IntModule.toNatModule α inst)]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ : Lean.Grind.Linarith.Poly) (k : Nat),
        @Eq Bool (Lean.Grind.Linarith.eq_coeff_cert p₁ p₂ k) Bool.true →
          @Eq α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.eq_coeff.h8.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Lean.Grind.Linarith.eq_coeff.h8.prem0)

-- Lean.Grind.OrderedAdd.add_le_right, hypothesis 4: necessary
/- FAILED: 8:170: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 } | 39:123: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_right.h4.inst : ¬(1 + 0) % 2 ≤ (1 + 1) % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_right.h4.prem0 : 0 % 2 ≤ 1 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_right.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M] {a b : M} (c : M),
        a ≤ b → c + a ≤ c + b := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_le_right.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) (0) (1) (1) HypCheckProof.Lean.Grind.OrderedAdd.add_le_right.h4.prem0)
-/

-- Lean.Grind.OrderedAdd.neg_lt_iff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.neg_lt_iff.h4.inst : ¬(-UInt8.ofNat 0 < UInt8.ofNat 1 ↔ -UInt8.ofNat 1 < UInt8.ofNat 0) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.neg_lt_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommGroup M] [inst_3 : LT M]
        [inst : Std.LawfulOrderLT M] {a b : M}, -a < b ↔ -b < a := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.neg_lt_iff.h4.inst (@hc_h (UInt8) (instLEUInt8) _ (Lean.Grind.Ring.toAddCommGroup) (instLTUInt8) _ (UInt8.ofNat 0) (UInt8.ofNat 1))

-- Lean.Grind.Order.le_of_not_lt, hypothesis 3: necessary
/- FAILED: 7:338: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 } | 19:165: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_of_not_lt.h3.inst : ¬1 % 2 ≤ 2 % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_of_not_lt.h3.prem0 : ¬2 < 1 := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_of_not_lt.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.IsLinearPreorder α] {a b : α}, ¬a < b → b ≤ a := fun hc_h => HypCheckProof.Lean.Grind.Order.le_of_not_lt.h3.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (instLTNat) (@Std.IsLinearPreorder.mk _ _ (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (2) (1) HypCheckProof.Lean.Grind.Order.le_of_not_lt.h3.prem0)
-/

-- Lean.Grind.Order.le_of_not_lt, hypothesis 4: necessary
/- FAILED: 7:297: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a < b } | 13:205: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a < b }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_of_not_lt.h4.inst : ¬0 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_of_not_lt.h4.prem0 : ¬0 < 0 := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_of_not_lt.h4 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α] {a b : α}, ¬a < b → b ≤ a := fun hc_h => HypCheckProof.Lean.Grind.Order.le_of_not_lt.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a < b : LE Nat }) (instLTNat) (@Std.LawfulOrderLT.mk _ _ _ (by (try dsimp only);   (intros; omega))) (0) (0) HypCheckProof.Lean.Grind.Order.le_of_not_lt.h4.prem0)
-/

-- Lean.Grind.Order.lt_of_not_le, hypothesis 3: necessary
/- FAILED: 7:338: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 } | 19:165: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le.h3.inst : ¬2 < 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le.h3.prem0 : ¬1 % 2 ≤ 2 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.IsLinearPreorder α] {a b : α}, ¬a ≤ b → b < a := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_of_not_le.h3.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (instLTNat) (@Std.IsLinearPreorder.mk _ _ (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (1) (2) HypCheckProof.Lean.Grind.Order.lt_of_not_le.h3.prem0)
-/

-- Lean.Grind.Order.lt_of_not_le, hypothesis 4: necessary
/- FAILED: 7:297: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a < b } | 13:205: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a < b }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le.h4.inst : ¬0 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le.h4.prem0 : ¬0 < 0 := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le.h4 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α] {a b : α}, ¬a ≤ b → b < a := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_of_not_le.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a < b : LE Nat }) (instLTNat) (@Std.LawfulOrderLT.mk _ _ _ (by (try dsimp only);   (intros; omega))) (0) (0) HypCheckProof.Lean.Grind.Order.lt_of_not_le.h4.prem0)
-/

-- Lean.Grind.CommRing.Stepwise.unsat_eq, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eq.h6.inst : Not False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eq.h6.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eq.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (p : Lean.Grind.CommRing.Poly) (k : Int),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
          False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eq.h6.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) _ (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eq.h6.prem0)

-- Lean.Grind.CommRing.Stepwise.unsat_eq, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eq.h7.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eq.h7.prem0 : Lean.Grind.CommRing.Stepwise.unsat_eq_cert (Lean.Grind.CommRing.Poly.num 1) 1 = Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eq.h7 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) [inst : Lean.Grind.IsCharP α 0]
        (p : Lean.Grind.CommRing.Poly) (k : Int), Lean.Grind.CommRing.Stepwise.unsat_eq_cert p k = Bool.true → False := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eq.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Lean.RArray.leaf 1) _ (Lean.Grind.CommRing.Poly.num 1) (1) HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eq.h7.prem0)

-- Lean.Grind.Order.lt_eq_false_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt.h3.inst : ¬(0 ≤ 0) = False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt.h3.prem0 : 0 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst : Std.IsPreorder α] {a b : α}, a < b → (b < a) = False := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt.h3.inst (@hc_h (Nat) (instLENat) ({ lt := fun (a b : Nat) => a ≤ b : LT Nat }) _ (0) (0) HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt.h3.prem0)

-- Int.Internal.Linear.le_of_le_diseq, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h4.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≠
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≠ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h4.prem0 HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h4.prem1)

-- Int.Internal.Linear.le_of_le_diseq, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 2) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h5.prem0 : Int.Internal.Linear.le_of_le_diseq_cert (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.num 1)
        (Int.Internal.Linear.Poly.num 2) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h5.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) ≠ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.le_of_le_diseq_cert p₁ p₂ p₃ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≠ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.num 2) HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h5.prem0 HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h5.prem1)

-- Int.Internal.Linear.le_of_le_diseq, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h6.prem0 : Int.Internal.Linear.le_of_le_diseq_cert (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0)
        (Int.Internal.Linear.Poly.num 1) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h6.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.le_of_le_diseq_cert p₁ p₂ p₃ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h6.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h6.prem0 HypCheckProof.Int.Internal.Linear.le_of_le_diseq.h6.prem1)

-- Lean.Grind.AC.Seq.denote_concat_of_startsWithVar, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_concat_of_startsWithVar.h3.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          ((Lean.Grind.AC.Seq.var 0).concat_k (Lean.Grind.AC.Seq.var 0)) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_concat_of_startsWithVar.h3.prem0 : (Lean.Grind.AC.Seq.var 0).startsWithVar_k 0 = Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_concat_of_startsWithVar.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) [inst₁ : Std.Associative ctx.op] (s : Lean.Grind.AC.Seq)
        (x : Lean.Grind.AC.Var),
        s.startsWithVar_k x = Bool.true →
          Lean.Grind.AC.Seq.denote ctx ((Lean.Grind.AC.Seq.var x).concat_k s) = Lean.Grind.AC.Seq.denote ctx s := fun hc_h => HypCheckProof.Lean.Grind.AC.Seq.denote_concat_of_startsWithVar.h3.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) _ (Lean.Grind.AC.Seq.var 0) (0) HypCheckProof.Lean.Grind.AC.Seq.denote_concat_of_startsWithVar.h3.prem0)

-- Lean.Grind.AC.Seq.denote_concat_of_startsWithVar, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_concat_of_startsWithVar.h6.inst : ¬Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          ((Lean.Grind.AC.Seq.var 1).concat_k (Lean.Grind.AC.Seq.var 0)) =
        Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_concat_of_startsWithVar.h6 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) [inst₁ : Std.Associative ctx.op] [inst₂ : Std.IdempotentOp ctx.op]
        (s : Lean.Grind.AC.Seq) (x : Lean.Grind.AC.Var),
        Lean.Grind.AC.Seq.denote ctx ((Lean.Grind.AC.Seq.var x).concat_k s) = Lean.Grind.AC.Seq.denote ctx s := fun hc_h => HypCheckProof.Lean.Grind.AC.Seq.denote_concat_of_startsWithVar.h6.inst (@hc_h (Nat) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
      op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }) (@Std.Associative.mk _ _ (by (try dsimp only);   (intros; simp_all; done))) (@Std.IdempotentOp.mk _ _ (by (try dsimp only);   (intros; simp_all; done))) (Lean.Grind.AC.Seq.var 0) (1))

-- Lean.Grind.CommRing.PPoly.denoteSN_addConst, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denoteSN_addConst.h6.inst : Not
      (@Eq Nat
        (@Lean.Grind.CommRing.PPoly.denoteSN Nat (@Lean.Grind.CommSemiring.toSemiring Nat Lean.Grind.instCommSemiringNat)
          (fun (n : Nat) =>
            @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (Lean.Grind.CommRing.PPoly.append.addConst
            (Lean.Grind.CommRing.PPoly.num
              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@HAdd.hAdd Nat Nat Nat
          (@instHAdd Nat
            (@Lean.Grind.Semiring.toAdd Nat (@Lean.Grind.CommSemiring.toSemiring Nat Lean.Grind.instCommSemiringNat)))
          (@Lean.Grind.CommRing.PPoly.denoteSN Nat (@Lean.Grind.CommSemiring.toSemiring Nat Lean.Grind.instCommSemiringNat)
            (fun (n : Nat) =>
              @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (Lean.Grind.CommRing.PPoly.num
              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
          (@Nat.cast Nat
            (@Lean.Grind.Semiring.natCast Nat (@Lean.Grind.CommSemiring.toSemiring Nat Lean.Grind.instCommSemiringNat))
            (Int.toNat (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denoteSN_addConst.h6.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denoteSN_addConst.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.Semiring α] (f : Nat → α) (B : Nat) {q : Lean.Grind.CommRing.PPoly} {k : Int},
        @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k →
          @Eq α (@Lean.Grind.CommRing.PPoly.denoteSN α inst f B (Lean.Grind.CommRing.PPoly.append.addConst q k))
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α inst))
              (@Lean.Grind.CommRing.PPoly.denoteSN α inst f B q)
              (@Nat.cast α (@Lean.Grind.Semiring.natCast α inst) k.toNat))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.PPoly.denoteSN_addConst.h6.inst (@hc_h (Nat) (@Lean.Grind.CommSemiring.toSemiring Nat Lean.Grind.instCommSemiringNat) (fun (n : Nat) =>
      @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.PPoly.num (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.CommRing.PPoly.denoteSN_addConst.h6.prem0)

-- Lean.Grind.CommRing.PPoly.coeff_eq_zero_of_kron, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.coeff_eq_zero_of_kron.h4.inst : Not
      (@Eq Int
        (Lean.Grind.CommRing.PPoly.coeff (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.coeff_eq_zero_of_kron.h4.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 3) (@instOfNat (nat_lit 3))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.coeff_eq_zero_of_kron.h4.prem1 : @LT.lt Int Int.instLTInt
      (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))
        (@Nat.cast Int instNatCastInt
          (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).norm1))
      (@OfNat.ofNat Int (nat_lit 3) (@instOfNat (nat_lit 3))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.coeff_eq_zero_of_kron.h4 : Not
      (∀ (X : Int),
        @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) X →
          ∀ (c : Nat) (p : Lean.Grind.CommRing.PPoly),
            @LT.lt Int Int.instLTInt
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                  (@Nat.cast Int instNatCastInt p.norm1))
                X →
              @Eq Int (Lean.Grind.CommRing.PPoly.coeff c p) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.PPoly.coeff_eq_zero_of_kron.h4.inst (@hc_h (@OfNat.ofNat Int (nat_lit 3) (@instOfNat (nat_lit 3))) HypCheckProof.Lean.Grind.CommRing.PPoly.coeff_eq_zero_of_kron.h4.prem0 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.PPoly.coeff_eq_zero_of_kron.h4.prem1)

-- Lean.Grind.CommRing.Stepwise.inv, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.inv.h5.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.inv.h5.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.inv.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (p₁ p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.inv.h5.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.inv.h5.prem0)

-- Lean.Grind.CommRing.Stepwise.inv, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.inv.h6.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.inv.h6.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.mul_cert
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.inv.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (p₁ p : Lean.Grind.CommRing.Poly),
        @Eq Bool
            (Lean.Grind.CommRing.Stepwise.mul_cert p₁
              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) p)
            Bool.true →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.inv.h6.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.inv.h6.prem0)

-- Lean.Grind.Linarith.diseq_neg, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_neg.h5.inst : Not
      (@Ne Int
        (@Lean.Grind.Linarith.Poly.denote' Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.IntModule.toNatModule Int
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_neg.h5.prem0 : @Ne Int
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
theorem HypCheckProof.Lean.Grind.Linarith.diseq_neg.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] (ctx : Lean.Grind.Linarith.Context α) (p p' : Lean.Grind.Linarith.Poly),
        @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
          @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p')
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.diseq_neg.h5.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.diseq_neg.h5.prem0)

-- Lean.Grind.Linarith.diseq_neg, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_neg.h6.inst : Not
      (@Ne Int
        (@Lean.Grind.Linarith.Poly.denote' Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.IntModule.toNatModule Int
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_neg.h6.prem0 : @Eq Bool
      (Lean.Grind.Linarith.Poly.nil.beq'
        (Lean.Grind.Linarith.Poly.nil.mul_k
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.diseq_neg.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] (ctx : Lean.Grind.Linarith.Context α) (p p' : Lean.Grind.Linarith.Poly),
        @Eq Bool (p'.beq' (p.mul_k (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
            Bool.true →
          @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p')
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.diseq_neg.h6.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.diseq_neg.h6.prem0)

-- Lean.Grind.Linarith.eq_neg, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_neg.h5.inst : Not
      (@Eq Int
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
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_neg.h5.prem0 : @Eq Int
      (@Lean.Grind.Linarith.Poly.denote' Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.eq_neg.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] (ctx : Lean.Grind.Linarith.Context α)
        (p₁ p₂ : Lean.Grind.Linarith.Poly),
        @Eq α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
          @Eq α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.eq_neg.h5.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.eq_neg.h5.prem0)

-- Lean.Grind.Linarith.eq_neg, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_neg.h6.inst : Not
      (@Eq Int
        (@Lean.Grind.Linarith.Poly.denote' Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.Linarith.Poly.add
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.IntModule.toNatModule Int
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_neg.h6.prem0 : @Eq Bool
      (Lean.Grind.Linarith.eq_neg_cert
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.eq_neg.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] (ctx : Lean.Grind.Linarith.Context α)
        (p₁ p₂ : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.eq_neg_cert p₁ p₂) Bool.true →
          @Eq α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.eq_neg.h6.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.eq_neg.h6.prem0)

-- Lean.Grind.AC.eq_simp_rhs_exact, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_exact.h5.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_exact.h5.prem0 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_exact.h5 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (lhs₁ rhs₁ lhs₂ : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx lhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₁ := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_simp_rhs_exact.h5.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_exact.h5.prem0)

-- Lean.Grind.AC.eq_simp_rhs_exact, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_exact.h6.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_exact.h6.prem0 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_exact.h6 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (lhs₁ rhs₁ lhs₂ : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₁ := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_simp_rhs_exact.h6.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_exact.h6.prem0)

-- Lean.Grind.AC.eq_expr_seq_seq, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_expr_seq_seq.h5.inst : ¬Lean.Grind.AC.Expr.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_expr_seq_seq.h5.prem0 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_expr_seq_seq.h5 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (e : Lean.Grind.AC.Expr) (s₁ s₂ : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx s₁ = Lean.Grind.AC.Seq.denote ctx s₂ →
          Lean.Grind.AC.Expr.denote ctx e = Lean.Grind.AC.Seq.denote ctx s₂ := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_expr_seq_seq.h5.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.eq_expr_seq_seq.h5.prem0)

-- Lean.Grind.AC.eq_expr_seq_seq, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_expr_seq_seq.h6.inst : ¬Lean.Grind.AC.Expr.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Expr.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_expr_seq_seq.h6.prem0 : Lean.Grind.AC.Expr.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Expr.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.eq_expr_seq_seq.h6 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (e : Lean.Grind.AC.Expr) (s₁ s₂ : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Expr.denote ctx e = Lean.Grind.AC.Seq.denote ctx s₁ →
          Lean.Grind.AC.Expr.denote ctx e = Lean.Grind.AC.Seq.denote ctx s₂ := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_expr_seq_seq.h6.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (Lean.Grind.AC.Expr.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_expr_seq_seq.h6.prem0)

-- Lean.Grind.AC.Seq.denote_unionFuel, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_unionFuel.h2.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a b : Bool) => !(a && b) :
            Lean.Grind.AC.Context Bool }
          (Lean.Grind.AC.Seq.unionFuel 0 (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0))
            (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0))) =
        { vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a b : Bool) => !(a && b) :
              Lean.Grind.AC.Context Bool }.op
          (Lean.Grind.AC.Seq.denote
            { vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a b : Bool) => !(a && b) :
              Lean.Grind.AC.Context Bool }
            (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)))
          (Lean.Grind.AC.Seq.denote
            { vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a b : Bool) => !(a && b) :
              Lean.Grind.AC.Context Bool }
            (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_unionFuel.h2.prem0 : Std.Commutative
      { vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a b : Bool) => !(a && b) :
          Lean.Grind.AC.Context Bool }.op := (@Std.Commutative.mk _ _ (by (try dsimp only);   decide))
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_unionFuel.h2 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₂ : Std.Commutative ctx.op} (fuel : Nat) (s₁ s₂ : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx (Lean.Grind.AC.Seq.unionFuel fuel s₁ s₂) =
          ctx.op (Lean.Grind.AC.Seq.denote ctx s₁) (Lean.Grind.AC.Seq.denote ctx s₂) := fun hc_h => HypCheckProof.Lean.Grind.AC.Seq.denote_unionFuel.h2.inst (@hc_h (Bool) ({ vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a b : Bool) => !(a && b) :
      Lean.Grind.AC.Context Bool }) HypCheckProof.Lean.Grind.AC.Seq.denote_unionFuel.h2.prem0 (0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)))

-- Lean.Grind.AC.Seq.denote_unionFuel, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_unionFuel.h3.inst : ¬Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.unionFuel 1 (Lean.Grind.AC.Seq.var 1) (Lean.Grind.AC.Seq.var 0)) =
        {
              vars :=
                Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                  (Lean.RArray.leaf { down := 2 : PLift Nat }),
              op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }.op
          (Lean.Grind.AC.Seq.denote
            {
              vars :=
                Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                  (Lean.RArray.leaf { down := 2 : PLift Nat }),
              op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
            (Lean.Grind.AC.Seq.var 1))
          (Lean.Grind.AC.Seq.denote
            {
              vars :=
                Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                  (Lean.RArray.leaf { down := 2 : PLift Nat }),
              op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
            (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_unionFuel.h3.prem0 : Std.Associative
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   (intros; simp_all; done)))
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_unionFuel.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op} (fuel : Nat) (s₁ s₂ : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx (Lean.Grind.AC.Seq.unionFuel fuel s₁ s₂) =
          ctx.op (Lean.Grind.AC.Seq.denote ctx s₁) (Lean.Grind.AC.Seq.denote ctx s₂) := fun hc_h => HypCheckProof.Lean.Grind.AC.Seq.denote_unionFuel.h3.inst (@hc_h (Nat) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
      op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.Seq.denote_unionFuel.h3.prem0 (1) (Lean.Grind.AC.Seq.var 1) (Lean.Grind.AC.Seq.var 0))

-- Lean.Grind.AC.diseq_simp_lhs_exact, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_exact.h5.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_exact.h5.prem0 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) ≠
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_exact.h5 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (lhs₁ rhs₁ rhs₂ : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ ≠ Lean.Grind.AC.Seq.denote ctx rhs₂ →
          Lean.Grind.AC.Seq.denote ctx rhs₁ ≠ Lean.Grind.AC.Seq.denote ctx rhs₂ := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_exact.h5.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_exact.h5.prem0)

-- Lean.Grind.AC.diseq_simp_lhs_exact, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_exact.h6.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_exact.h6.prem0 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_exact.h6 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (lhs₁ rhs₁ rhs₂ : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx rhs₁ ≠ Lean.Grind.AC.Seq.denote ctx rhs₂ := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_exact.h6.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_exact.h6.prem0)

-- Lean.Grind.Preorder.ne_of_gt, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Preorder.ne_of_gt.h3.inst : Not
      (@Ne Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Preorder.ne_of_gt.h3.prem0 : @GT.gt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := by
  simp
theorem HypCheckProof.Lean.Grind.Preorder.ne_of_gt.h3 : Not (∀ {α : Type} [inst : LE α] [inst : LT α] {a b : α}, @GT.gt α inst a b → @Ne α a b) := fun hc_h => HypCheckProof.Lean.Grind.Preorder.ne_of_gt.h3.inst (@hc_h (Nat) (instLENat) (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Lean.Grind.Preorder.ne_of_gt.h3.prem0)

-- Lean.Grind.Preorder.ne_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Preorder.ne_of_lt.h3.inst : ¬0 ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Preorder.ne_of_lt.h3.prem0 : 0 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.Preorder.ne_of_lt.h3 : ¬∀ {α : Type} [inst : LE α] [inst : LT α] {a b : α}, a < b → a ≠ b := fun hc_h => HypCheckProof.Lean.Grind.Preorder.ne_of_lt.h3.inst (@hc_h (Nat) (instLENat) ({ lt := fun (a b : Nat) => a ≤ b : LT Nat }) (0) (0) HypCheckProof.Lean.Grind.Preorder.ne_of_lt.h3.prem0)

-- Lean.Grind.OrderedAdd.sub_nonneg_iff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.sub_nonneg_iff.h4.inst : ¬(0 ≤ UInt8.ofNat 0 - UInt8.ofNat 1 ↔ UInt8.ofNat 1 ≤ UInt8.ofNat 0) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.sub_nonneg_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommGroup M] {a b : M},
        0 ≤ a - b ↔ b ≤ a := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.sub_nonneg_iff.h4.inst (@hc_h (UInt8) (instLEUInt8) _ (Lean.Grind.Ring.toAddCommGroup) (UInt8.ofNat 0) (UInt8.ofNat 1))

-- Lean.Grind.AC.eq_simp_lhs_exact, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_exact.h5.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_exact.h5.prem0 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_exact.h5 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (lhs₁ rhs₁ rhs₂ : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₂ →
          Lean.Grind.AC.Seq.denote ctx rhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₂ := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_simp_lhs_exact.h5.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.eq_simp_lhs_exact.h5.prem0)

-- Lean.Grind.AC.eq_simp_lhs_exact, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_exact.h6.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_exact.h6.prem0 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_exact.h6 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (lhs₁ rhs₁ rhs₂ : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx rhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₂ := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_simp_lhs_exact.h6.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_simp_lhs_exact.h6.prem0)

-- Lean.Grind.AC.diseq_simp_rhs_exact, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_exact.h5.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_exact.h5.prem0 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) ≠
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_exact.h5 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (lhs₁ rhs₁ lhs₂ : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₂ ≠ Lean.Grind.AC.Seq.denote ctx lhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ ≠ Lean.Grind.AC.Seq.denote ctx rhs₁ := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_exact.h5.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_exact.h5.prem0)

-- Lean.Grind.AC.diseq_simp_rhs_exact, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_exact.h6.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_exact.h6.prem0 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_exact.h6 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (lhs₁ rhs₁ lhs₂ : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ ≠ Lean.Grind.AC.Seq.denote ctx rhs₁ := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_exact.h6.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_exact.h6.prem0)

-- Lean.Grind.Order.le_of_eq_2, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_of_eq_2.h2.inst : ¬False := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_of_eq_2.h2 : ¬∀ {α : Type} [inst : LE α] {a b : α}, a = b → b ≤ a := fun hc_h => HypCheckProof.Lean.Grind.Order.le_of_eq_2.h2.inst (@hc_h (Bool) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (Bool.false) (Bool.false) rfl)

-- Lean.Grind.Order.le_of_not_le, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_of_not_le.h2.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_of_not_le.h2.prem0 : ¬False := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_of_not_le.h2 : ¬∀ {α : Type} [inst : LE α] {a b : α}, ¬a ≤ b → b ≤ a := fun hc_h => HypCheckProof.Lean.Grind.Order.le_of_not_le.h2.inst (@hc_h (Bool) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (Bool.false) (Bool.false) HypCheckProof.Lean.Grind.Order.le_of_not_le.h2.prem0)

-- Lean.Grind.Order.le_of_eq_1, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_of_eq_1.h2.inst : ¬False := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_of_eq_1.h2 : ¬∀ {α : Type} [inst : LE α] {a b : α}, a = b → a ≤ b := fun hc_h => HypCheckProof.Lean.Grind.Order.le_of_eq_1.h2.inst (@hc_h (Bool) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (Bool.false) (Bool.false) rfl)

-- Lean.Grind.CommRing.one_eq_zero_unsat, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.one_eq_zero_unsat.h4.inst : Not False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.one_eq_zero_unsat.h4.prem0 : @Eq Rat
      (@Lean.Grind.CommRing.Poly.denote Rat
        (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
        (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Rat (nat_lit 0)
        (@Zero.toOfNat0 Rat
          (@Lean.Grind.AddCommMonoid.toZero Rat
            (@Lean.Grind.NatModule.toAddCommMonoid Rat
              (@Lean.Grind.Semiring.toNatModule Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.one_eq_zero_unsat.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (ctx : Lean.Grind.CommRing.Context α) (p : Lean.Grind.CommRing.Poly),
        @Eq α
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α
                        (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))))) →
          False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.one_eq_zero_unsat.h4.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.one_eq_zero_unsat.h4.prem0)

-- Lean.Grind.CommRing.inv_int_eqC, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.inv_int_eqC.h5.inst : Not
      (@Eq Rat
        (@HMul.hMul Rat Rat Rat
          (@instHMul Rat
            (@Lean.Grind.Semiring.toMul Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@Lean.Grind.CommRing.denoteInt Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
            (@Lean.Grind.CommRing.denoteInt Rat
              (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@OfNat.ofNat Rat (nat_lit 1)
          (@Lean.Grind.Semiring.ofNat Rat
            (@Lean.Grind.CommSemiring.toSemiring Rat
              (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))
            (nat_lit 1)))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.CommRing.inv_int_eqC.h5 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            c]
        (b : Int),
        @Eq α
          (@HMul.hMul α α α
            (@instHMul α
              (@Lean.Grind.Semiring.toMul α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
            (@Lean.Grind.CommRing.denoteInt α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) b)
            (@Inv.inv α (@Lean.Grind.Field.toInv α inst)
              (@Lean.Grind.CommRing.denoteInt α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) b)))
          (@OfNat.ofNat α (nat_lit 1)
            (@Lean.Grind.Semiring.ofNat α
              (@Lean.Grind.CommSemiring.toSemiring α
                (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
              (nat_lit 1)))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.inv_int_eqC.h5.inst (@hc_h (Rat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instFieldRat) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Int.Internal.Linear.eq_le_weaken, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_weaken.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_weaken.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_weaken.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly) (k : Int),
        Int.Internal.Linear.Poly.denote' ctx p₁ = 0 → Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_weaken.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) HypCheckProof.Int.Internal.Linear.eq_le_weaken.h4.prem0)

-- Int.Internal.Linear.eq_le_weaken, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_weaken.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_weaken.h5.prem0 : Int.Internal.Linear.le_weaken_cert (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) 0 =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_weaken.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly) (k : Int),
        Int.Internal.Linear.le_weaken_cert p₁ p₂ k = Bool.true → Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_weaken.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) HypCheckProof.Int.Internal.Linear.eq_le_weaken.h5.prem0)

-- Int.Internal.Linear.le_norm_expr_rfl, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm_expr_rfl.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm_expr_rfl.h4.prem0 : Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) ≤
      Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_norm_expr_rfl.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Expr.denote_k ctx lhs ≤ Int.Internal.Linear.Expr.denote_k ctx rhs →
          Int.Internal.Linear.Poly.denote' ctx p ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_norm_expr_rfl.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.le_norm_expr_rfl.h4.prem0)

-- Int.Internal.Linear.le_norm_expr_rfl, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm_expr_rfl.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          ((Int.Internal.Linear.Expr.var 0).sub (Int.Internal.Linear.Expr.num 0)).norm_k ≤
        0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_norm_expr_rfl.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        p = (lhs.sub rhs).norm_k → Int.Internal.Linear.Poly.denote' ctx p ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_norm_expr_rfl.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0) (Int.Internal.Linear.Expr.num 0) (((Int.Internal.Linear.Expr.var 0).sub (Int.Internal.Linear.Expr.num 0)).norm_k) rfl)

-- Int.Internal.Linear.var_eq, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.var_eq.h4.inst : ¬Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0 = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.var_eq.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.var_eq.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (k : Int) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p = 0 → Int.Internal.Linear.Var.denote ctx x = k := fun hc_h => HypCheckProof.Int.Internal.Linear.var_eq.h4.inst (@hc_h (Lean.RArray.leaf 1) (0) (0) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.var_eq.h4.prem0)

-- Int.Internal.Linear.var_eq, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.var_eq.h5.inst : ¬Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0 = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.var_eq.h5.prem0 : Int.Internal.Linear.var_eq_cert 0 0 (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) = Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.var_eq.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (k : Int) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.var_eq_cert x k p = Bool.true → Int.Internal.Linear.Var.denote ctx x = k := fun hc_h => HypCheckProof.Int.Internal.Linear.var_eq.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.var_eq.h5.prem0)

-- Int.Internal.Linear.dvd_norm_expr, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_norm_expr.h4.inst : ¬0 ∣
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_norm_expr.h4.prem0 : 0 ∣ Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_norm_expr.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (d : Int) (e : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        d ∣ Int.Internal.Linear.Expr.denote_k ctx e → d ∣ Int.Internal.Linear.Poly.denote' ctx p := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_norm_expr.h4.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.dvd_norm_expr.h4.prem0)

-- Int.Internal.Linear.dvd_norm_expr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_norm_expr.h5.inst : ¬0 ∣
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_norm_expr.h5.prem0 : (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).beq' (Int.Internal.Linear.Expr.var 0).norm_k =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_norm_expr.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (d : Int) (e : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        p.beq' e.norm_k = Bool.true → d ∣ Int.Internal.Linear.Poly.denote' ctx p := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_norm_expr.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Expr.var 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.dvd_norm_expr.h5.prem0)

-- Int.Internal.Linear.eq_norm_expr_rfl, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm_expr_rfl.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm_expr_rfl.h4.prem0 : Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
      Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Int.Internal.Linear.eq_norm_expr_rfl.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Expr.denote_k ctx lhs = Int.Internal.Linear.Expr.denote_k ctx rhs →
          Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_norm_expr_rfl.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_norm_expr_rfl.h4.prem0)

-- Int.Internal.Linear.eq_norm_expr_rfl, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm_expr_rfl.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          ((Int.Internal.Linear.Expr.num 0).sub (Int.Internal.Linear.Expr.var 0)).norm_k =
        0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_norm_expr_rfl.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        p = (lhs.sub rhs).norm_k → Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_norm_expr_rfl.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.var 0) (((Int.Internal.Linear.Expr.num 0).sub (Int.Internal.Linear.Expr.var 0)).norm_k) rfl)

-- Int.Internal.Linear.eq_def', hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def'.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def'.h4.prem0 : Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0 =
      Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_def'.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (e : Int.Internal.Linear.Expr)
        (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Var.denote ctx x = Int.Internal.Linear.Expr.denote_k ctx e →
          Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_def'.h4.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Expr.var 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_def'.h4.prem0)

-- Int.Internal.Linear.eq_def', hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def'.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add (-1) 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def'.h5.prem0 : Int.Internal.Linear.eq_def'_cert 0 (Int.Internal.Linear.Expr.num 0)
        (Int.Internal.Linear.Poly.add (-1) 0 (Int.Internal.Linear.Poly.num 0)) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_def'.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (e : Int.Internal.Linear.Expr)
        (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.eq_def'_cert x e p = Bool.true → Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_def'.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add (-1) 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_def'.h5.prem0)

-- Lean.Grind.CommRing.Poly.denote_mulConstC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulConstC.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.mulConstC (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulConstC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α inst ctx (Lean.Grind.CommRing.Poly.mulConstC k p c))
          (@HMul.hMul α α α (@instHMul α (@Lean.Grind.Semiring.toMul α (@Lean.Grind.Ring.toSemiring α inst)))
            (@Int.cast α (@Lean.Grind.Ring.intCast α inst) k) (@Lean.Grind.CommRing.Poly.denote α inst ctx p))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulConstC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))

-- Lean.Grind.CommRing.Poly.denote_addConstC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_addConstC.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).addConstC
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_addConstC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α)
        (p : Lean.Grind.CommRing.Poly) (k : Int),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α inst ctx (p.addConstC k c))
          (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst)))
            (@Lean.Grind.CommRing.Poly.denote α inst ctx p) (@Int.cast α (@Lean.Grind.Ring.intCast α inst) k))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_addConstC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))

-- Lean.Grind.CommRing.Poly.denote_mulC_nc, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulC_nc.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mulC_nc
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulC_nc.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α)
        (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α inst ctx (p₁.mulC_nc p₂ c))
          (@HMul.hMul α α α (@instHMul α (@Lean.Grind.Semiring.toMul α (@Lean.Grind.Ring.toSemiring α inst)))
            (@Lean.Grind.CommRing.Poly.denote α inst ctx p₁) (@Lean.Grind.CommRing.Poly.denote α inst ctx p₂))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulC_nc.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))

-- Lean.Grind.CommRing.Expr.denote_toPolyXC_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPolyXC_k.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPolyXC_k.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (e : Lean.Grind.CommRing.Expr),
        @Eq α
          (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
            (Lean.Grind.CommRing.Expr.toPolyXC_k bal e c))
          (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx e)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPolyXC_k.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))

-- Lean.Grind.CommRing.Poly.denote_combineC_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_combineC_k.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combineC_k
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_combineC_k.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (a b : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.combineC_k c b))
          (@HAdd.hAdd α α α
            (@instHAdd α
              (@Lean.Grind.Semiring.toAdd α
                (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_combineC_k.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))

-- Lean.Grind.CommRing.Mon.denote_cancelInv, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Mon.denote_cancelInv.h6.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Mon.denote Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Mon.cancelInv (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit))))
        (@Lean.Grind.CommRing.Mon.denote Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Mon.denote_cancelInv.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (m : Lean.Grind.CommRing.Mon)
        (x y : Lean.Grind.CommRing.Var),
        @Eq α
          (@Lean.Grind.CommRing.Mon.denote α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx
            (Lean.Grind.CommRing.Mon.cancelInv x y m))
          (@Lean.Grind.CommRing.Mon.denote α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx m)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Mon.denote_cancelInv.h6.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Mon.mult
      { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
        k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))

-- Int.Internal.Linear.eq_unsat, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_unsat.h2.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_unsat.h2.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_unsat.h2 : ¬∀ (ctx : Int.Internal.Linear.Context) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p = 0 → False := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_unsat.h2.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.eq_unsat.h2.prem0)

-- Int.Internal.Linear.eq_unsat, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_unsat.h3.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_unsat.h3.prem0 : (Int.Internal.Linear.Poly.num 1).isUnsatEq_k = Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_unsat.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p : Int.Internal.Linear.Poly), p.isUnsatEq_k = Bool.true → False := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_unsat.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.eq_unsat.h3.prem0)

-- Int.Internal.Linear.norm_eq_coeff, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.norm_eq_coeff.h5.inst : ¬(Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
          Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        (Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
          0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.norm_eq_coeff.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly) (k : Int),
        (Int.Internal.Linear.Expr.denote ctx lhs = Int.Internal.Linear.Expr.denote ctx rhs) =
          (Int.Internal.Linear.Poly.denote' ctx p = 0) := fun hc_h => HypCheckProof.Int.Internal.Linear.norm_eq_coeff.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0))

