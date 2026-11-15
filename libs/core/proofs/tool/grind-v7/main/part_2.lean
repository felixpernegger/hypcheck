import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.CommRing.le_of_kronQ_rel, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQ_rel.h15.inst : Not
      (@Eq Prop
        (@LE.le Rat Rat.instLE
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LE.le Rat Rat.instLE
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
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQ_rel.h15.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQ_rel.h15.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQ_rel.h15.prem2 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degQOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQ_rel.h15.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQOk_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQ_rel.h15.prem4 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQEq_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQ_rel.h15 : Not
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
                      (@LE.le α inst_2
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx lhs)
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs))
                      (@LE.le α inst_2
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx lhs')
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_of_kronQ_rel.h15.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (Rat.instLE) (Rat.instLT) _ _ _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.le_of_kronQ_rel.h15.prem0 HypCheckProof.Lean.Grind.CommRing.le_of_kronQ_rel.h15.prem1 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_of_kronQ_rel.h15.prem2 HypCheckProof.Lean.Grind.CommRing.le_of_kronQ_rel.h15.prem3 HypCheckProof.Lean.Grind.CommRing.le_of_kronQ_rel.h15.prem4)

-- Lean.Grind.CommRing.le_norm_polyC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h3.inst : Not
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
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h3.prem0 : @Eq Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combineC_k
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (Lean.Grind.CommRing.Poly.mulConstC_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
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
                  (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                    (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                  (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                    (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl rfl HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h3.prem0)

-- Lean.Grind.CommRing.le_norm_polyC, hypothesis 17: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h17.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h17 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.IsPreorder α inst_2]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_2 inst_3 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
          @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (rp.combineC_k c
                  (Lean.Grind.CommRing.Poly.mulConstC_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) lp c)) →
              @Eq Prop
                (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h17.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combineC_k
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (Lean.Grind.CommRing.Poly.mulConstC_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl rfl)

-- Lean.Grind.CommRing.le_norm_polyC, hypothesis 18: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h18.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h18.prem0 : @Eq Lean.Grind.CommRing.Poly
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
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h18 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.IsPreorder α inst_2]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_2 inst_3 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal (rhs.sub lhs) c) →
          @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (rp.combineC_k c
                  (Lean.Grind.CommRing.Poly.mulConstC_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) lp c)) →
              @Eq Prop
                (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h18.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h18.prem0)

-- Lean.Grind.CommRing.le_norm_polyC, hypothesis 19: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h19.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h19.prem0 : @Eq Lean.Grind.CommRing.Poly
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
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h19 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.IsPreorder α inst_2]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_2 inst_3 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal (rhs.sub lhs) c) →
          @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (rp.combineC_k c
                  (Lean.Grind.CommRing.Poly.mulConstC_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) lp c)) →
              @Eq Prop
                (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h19.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
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
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h19.prem0)

-- Lean.Grind.CommRing.le_norm_polyC, hypothesis 20: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h20.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h20 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.IsPreorder α inst_2]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_2 inst_3 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal (rhs.sub lhs) c) →
          @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
            @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
              @Eq Prop
                (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h20.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl rfl)

-- Lean.Grind.CommRing.lt_norm_poly, hypothesis 16: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h16.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h16 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
          @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (rp.combine_k
                  (Lean.Grind.CommRing.Poly.mulConst_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) lp)) →
              @Eq Prop
                (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h16.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).combine_k
      (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl rfl)

-- Lean.Grind.CommRing.lt_norm_poly, hypothesis 17: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h17.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h17.prem0 : @Eq Lean.Grind.CommRing.Poly
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h17 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (rhs.sub lhs)) →
          @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (rp.combine_k
                  (Lean.Grind.CommRing.Poly.mulConst_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) lp)) →
              @Eq Prop
                (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h17.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
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
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h17.prem0)

-- Lean.Grind.CommRing.lt_norm_poly, hypothesis 18: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h18.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h18.prem0 : @Eq Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combine_k
        (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h18 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (rhs.sub lhs)) →
          @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (rp.combine_k
                  (Lean.Grind.CommRing.Poly.mulConst_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) lp)) →
              @Eq Prop
                (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h18.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h18.prem0)

-- Lean.Grind.CommRing.lt_norm_poly, hypothesis 19: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h19.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h19 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (rhs.sub lhs)) →
          @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
            @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
              @Eq Prop
                (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h19.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl rfl)

-- Lean.Grind.CommRing.lt_of_kron_rel, hypothesis 16: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kron_rel.h16.inst : Not
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
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kron_rel.h16.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kron_rel.h16.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kron_rel.h16 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
        [inst_5 : @Std.LawfulOrderLT α inst_2 inst_1] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (l r l' r' : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B (l.sub r) (l'.sub r')) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K (l.sub r) (l'.sub r')) Bool.true →
            @Eq Prop
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r))
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l')
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_of_kron_rel.h16.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_of_kron_rel.h16.prem0 HypCheckProof.Lean.Grind.CommRing.lt_of_kron_rel.h16.prem1)

-- Lean.Grind.Order.lt_trans_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h6.inst : Not
      (@LT.lt UInt8 instLTUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@HAdd.hAdd UInt8 UInt8 UInt8
          (@instHAdd UInt8
            (@Lean.Grind.Semiring.toAdd UInt8
              (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
          (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h6.prem0 : @LT.lt UInt8 instLTUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h6.prem1 : @LT.lt UInt8 instLTUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h6.prem2 : @Eq Bool
      (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst : @Std.IsPreorder α inst] [inst : Lean.Grind.Ring α] {a b c : α} {k₁ k₂ : Int} (k : Int),
        @LT.lt α inst_1 a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst) k₁)) →
          @LT.lt α inst_1 b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst) k₂)) →
            @Eq Bool
                (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k
                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁))
                Bool.true →
              @LT.lt α inst_1 a
                (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst))) c
                  (@Int.cast α (@Lean.Grind.Ring.intCast α inst) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_trans_k.h6.inst (@hc_h (UInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_trans_k.h6.prem0 HypCheckProof.Lean.Grind.Order.lt_trans_k.h6.prem1 HypCheckProof.Lean.Grind.Order.lt_trans_k.h6.prem2)

-- Lean.Grind.Order.lt_trans_k, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h13.inst : Not
      (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h13.prem0 : @LT.lt Int Int.instLTInt (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h13.prem1 : @Eq Bool
      (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h13 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b c : α}
        {k₁ k₂ : Int} (k : Int),
        @LT.lt α inst_1 b
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)) →
          @Eq Bool
              (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k
                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁))
              Bool.true →
            @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_trans_k.h13.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_trans_k.h13.prem0 HypCheckProof.Lean.Grind.Order.lt_trans_k.h13.prem1)

-- Lean.Grind.Order.lt_trans_k, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h14.inst : Not
      (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h14.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h14.prem1 : @Eq Bool
      (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h14 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b c : α}
        {k₁ k₂ : Int} (k : Int),
        @LT.lt α inst_1 a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @Eq Bool
              (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k
                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁))
              Bool.true →
            @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_trans_k.h14.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_trans_k.h14.prem0 HypCheckProof.Lean.Grind.Order.lt_trans_k.h14.prem1)

-- Lean.Grind.Order.lt_trans_k, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h15.inst : Not
      (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h15.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h15.prem1 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_trans_k.h15 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b c : α}
        {k₁ k₂ : Int} (k : Int),
        @LT.lt α inst_1 a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @LT.lt α inst_1 b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)) →
            @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_trans_k.h15.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_trans_k.h15.prem0 HypCheckProof.Lean.Grind.Order.lt_trans_k.h15.prem1)

-- Lean.Grind.Order.lt_le_trans_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h6.inst : Not
      (@LT.lt UInt8 instLTUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@HAdd.hAdd UInt8 UInt8 UInt8
          (@instHAdd UInt8
            (@Lean.Grind.Semiring.toAdd UInt8
              (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
          (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h6.prem0 : @LT.lt UInt8 instLTUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h6.prem1 : @LE.le UInt8 instLEUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h6.prem2 : @Eq Bool
      (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α] {a b c : α} {k₁ k₂ : Int} (k : Int),
        @LT.lt α inst_1 a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @LE.le α inst b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)) →
            @Eq Bool
                (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k
                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁))
                Bool.true →
              @LT.lt α inst_1 a
                (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                  (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h6.inst (@hc_h (UInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h6.prem0 HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h6.prem1 HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h6.prem2)

-- Lean.Grind.Order.lt_le_trans_k, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h13.inst : Not
      (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h13.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h13.prem1 : @Eq Bool
      (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h13 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b c : α}
        {k₁ k₂ : Int} (k : Int),
        @LE.le α inst b
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)) →
          @Eq Bool
              (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k
                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁))
              Bool.true →
            @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h13.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h13.prem0 HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h13.prem1)

-- Lean.Grind.Order.lt_le_trans_k, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h14.inst : Not
      (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h14.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h14.prem1 : @Eq Bool
      (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h14 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b c : α}
        {k₁ k₂ : Int} (k : Int),
        @LT.lt α inst_1 a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @Eq Bool
              (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k
                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁))
              Bool.true →
            @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h14.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h14.prem0 HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h14.prem1)

-- Lean.Grind.Order.lt_le_trans_k, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h15.inst : Not
      (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h15.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h15.prem1 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h15 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b c : α}
        {k₁ k₂ : Int} (k : Int),
        @LT.lt α inst_1 a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @LE.le α inst b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)) →
            @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h15.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h15.prem0 HypCheckProof.Lean.Grind.Order.lt_le_trans_k.h15.prem1)

-- Lean.Grind.CommRing.eq_norm_polyC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h3.inst : Not
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
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h3.prem0 : @Eq Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combineC_k
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (Lean.Grind.CommRing.Poly.mulConstC_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr) (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal (lhs.sub rhs) c) →
          @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
            @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
              @Eq Lean.Grind.CommRing.Poly p
                  (lp.combineC_k c
                    (Lean.Grind.CommRing.Poly.mulConstC_k
                      (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) rp c)) →
                @Eq Prop
                  (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                    (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                  (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                    (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl rfl HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h3.prem0)

-- Lean.Grind.CommRing.eq_norm_polyC, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h13.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h13 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
          @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (lp.combineC_k c
                  (Lean.Grind.CommRing.Poly.mulConstC_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) rp c)) →
              @Eq Prop
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h13.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combineC_k
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (Lean.Grind.CommRing.Poly.mulConstC_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl rfl)

-- Lean.Grind.CommRing.eq_norm_polyC, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h14.inst : Not
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
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h14.prem0 : @Eq Lean.Grind.CommRing.Poly
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h14 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal (lhs.sub rhs) c) →
          @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (lp.combineC_k c
                  (Lean.Grind.CommRing.Poly.mulConstC_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) rp c)) →
              @Eq Prop
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h14.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h14.prem0)

-- Lean.Grind.CommRing.eq_norm_polyC, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h15.inst : Not
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
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k)
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h15.prem0 : @Eq Lean.Grind.CommRing.Poly
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h15 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal (lhs.sub rhs) c) →
          @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (lp.combineC_k c
                  (Lean.Grind.CommRing.Poly.mulConstC_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) rp c)) →
              @Eq Prop
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h15.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h15.prem0)

-- Lean.Grind.CommRing.eq_norm_polyC, hypothesis 16: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h16.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h16 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal (lhs.sub rhs) c) →
          @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
            @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
              @Eq Prop
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_norm_polyC.h16.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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

-- Lean.Grind.CommRing.lt_false_of_toPPX_eq, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h13.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
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
        False) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h13.prem0 : @Eq Lean.Grind.CommRing.PPoly
      (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Bool.false
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Bool.false
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.PPoly),
        @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a) →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b) →
            @Eq Prop
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h13.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.branch Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Bool.false
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) rfl HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h13.prem0)

-- Lean.Grind.CommRing.lt_false_of_toPPX_eq, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h14.inst : Not
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
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h14.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h14 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.PPoly),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b) →
            @Eq Prop
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h14.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Bool.false
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h14.prem0 rfl)

-- Lean.Grind.CommRing.lt_false_of_toPPX_eq, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h15.inst : Not
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
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h15.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h15 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.PPoly),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a) →
            @Eq Prop
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h15.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h15.prem0 rfl)

-- Lean.Grind.CommRing.Stepwise.imp_1eqKC, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqKC.h12.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqKC.h12.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            ((Lean.Grind.CommRing.Expr.var
                  (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))).beq'
        ((Lean.Grind.CommRing.Poly.kron_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).add_k
          ((Int.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).mul_k
            (Lean.Grind.CommRing.PPoly.kron_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqKC.h12.prem1 : @Eq Int
      (@HMul.hMul Int Int Int
        (@instHMul Int
          (@Lean.Grind.Semiring.toMul Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqKC.h12 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (lhs rhs : Lean.Grind.CommRing.Expr)
        (p₁ p₂ : Lean.Grind.CommRing.Poly) (E : Lean.Grind.CommRing.PPoly),
        @Eq Bool
            ((Lean.Grind.CommRing.Expr.kronEval_k K B (lhs.sub rhs)).beq'
              ((Lean.Grind.CommRing.Poly.kron_k K B p₁).add_k ((Int.ofNat c).mul_k (Lean.Grind.CommRing.PPoly.kron_k K E))))
            Bool.true →
          @Eq Lean.Grind.CommRing.Poly p₂
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) →
            @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst))
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂) →
              @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqKC.h12.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqKC.h12.prem0 rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqKC.h12.prem1)

-- Lean.Grind.CommRing.Stepwise.imp_1eqKC, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqKC.h13.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqKC.h13.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.impOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqKC.h13.prem1 : @Eq Int
      (@HMul.hMul Int Int Int
        (@instHMul Int
          (@Lean.Grind.Semiring.toMul Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqKC.h13 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (lhs rhs : Lean.Grind.CommRing.Expr)
        (p₁ p₂ : Lean.Grind.CommRing.Poly) (E : Lean.Grind.CommRing.PPoly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.impOk_k K B c (lhs.sub rhs) p₁ E) Bool.true →
          @Eq Lean.Grind.CommRing.Poly p₂
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) →
            @Eq α
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst))
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂) →
              @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqKC.h13.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqKC.h13.prem0 rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqKC.h13.prem1)

-- Lean.Grind.CommRing.Expr.denote_mul_of_termsC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).mul
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h3.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h3.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h3.prem2 : @Eq Lean.Grind.CommRing.Poly (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.sumB_k
        (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) b)
        ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mulTermsC_k
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (a b : Lean.Grind.CommRing.Expr) (pa pb : Lean.Grind.CommRing.Poly) (ts : List Lean.Grind.CommRing.Poly)
        (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pb) →
            @Eq (List Lean.Grind.CommRing.Poly) ts (pa.mulTermsC_k pb c) →
              @Eq Lean.Grind.CommRing.Poly p
                  (Lean.Grind.CommRing.Poly.sumB_k (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k c b) ts) →
                @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.mul b))
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mulTermsC_k
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h3.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h3.prem1 rfl HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h3.prem2)

-- Lean.Grind.CommRing.Expr.denote_mul_of_termsC, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h11.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).mul
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h11.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h11.prem1 : @Eq Lean.Grind.CommRing.Poly (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.sumB_k
        (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b)
        ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).mulTermsC_k
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h11 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr) (pa pb : Lean.Grind.CommRing.Poly)
        (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pb) →
          @Eq (List Lean.Grind.CommRing.Poly) ts (pa.mulTermsC_k pb c) →
            @Eq Lean.Grind.CommRing.Poly p
                (Lean.Grind.CommRing.Poly.sumB_k (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k c b) ts) →
              @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.mul b))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h11.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).mulTermsC_k
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h11.prem0 rfl HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h11.prem1)

-- Lean.Grind.CommRing.Expr.denote_mul_of_termsC, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h12.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).mul
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h12.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h12.prem1 : @Eq Lean.Grind.CommRing.Poly (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.sumB_k
        (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b)
        ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mulTermsC_k
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h12 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr) (pa pb : Lean.Grind.CommRing.Poly)
        (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq (List Lean.Grind.CommRing.Poly) ts (pa.mulTermsC_k pb c) →
            @Eq Lean.Grind.CommRing.Poly p
                (Lean.Grind.CommRing.Poly.sumB_k (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k c b) ts) →
              @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.mul b))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h12.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mulTermsC_k
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h12.prem0 rfl HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h12.prem1)

-- Lean.Grind.CommRing.Expr.denote_mul_of_termsC, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h13.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).mul
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.sumB_k
            (fun (a b : Lean.Grind.CommRing.Poly) =>
              a.combineC_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b)
            (@List.cons Lean.Grind.CommRing.Poly
              (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
              (@List.nil Lean.Grind.CommRing.Poly))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h13.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h13.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h13 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr) (pa pb : Lean.Grind.CommRing.Poly)
        (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pb) →
            @Eq Lean.Grind.CommRing.Poly p
                (Lean.Grind.CommRing.Poly.sumB_k (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k c b) ts) →
              @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.mul b))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h13.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@List.cons Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@List.nil Lean.Grind.CommRing.Poly)) (Lean.Grind.CommRing.Poly.sumB_k
      (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b)
      (@List.cons Lean.Grind.CommRing.Poly
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@List.nil Lean.Grind.CommRing.Poly))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h13.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h13.prem1 rfl)

-- Lean.Grind.CommRing.Expr.denote_mul_of_termsC, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h14.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).mul
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h14.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h14.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h14 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr) (pa pb : Lean.Grind.CommRing.Poly)
        (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pb) →
            @Eq (List Lean.Grind.CommRing.Poly) ts (pa.mulTermsC_k pb c) →
              @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.mul b))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h14.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).mulTermsC_k
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h14.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_termsC.h14.prem1 rfl)

-- Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).pow
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h3.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h3.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).pow
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h3.prem2 : @Eq Lean.Grind.CommRing.Poly (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.sumB_k
        (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) b)
        ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mulTermsC_k
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (a : Lean.Grind.CommRing.Expr) (k : Nat) (pa q : Lean.Grind.CommRing.Poly) (ts : List Lean.Grind.CommRing.Poly)
        (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.pow k))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx q) →
            @Eq (List Lean.Grind.CommRing.Poly) ts (pa.mulTermsC_k q c) →
              @Eq Lean.Grind.CommRing.Poly p
                  (Lean.Grind.CommRing.Poly.sumB_k (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k c b) ts) →
                @Eq α
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
                    (a.pow
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mulTermsC_k
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h3.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h3.prem1 rfl HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h3.prem2)

-- Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h11.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).pow
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h11.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).pow
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h11.prem1 : @Eq Lean.Grind.CommRing.Poly (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.sumB_k
        (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b)
        ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).mulTermsC_k
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h11 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr) (k : Nat) (pa q : Lean.Grind.CommRing.Poly)
        (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.pow k))
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx q) →
          @Eq (List Lean.Grind.CommRing.Poly) ts (pa.mulTermsC_k q c) →
            @Eq Lean.Grind.CommRing.Poly p
                (Lean.Grind.CommRing.Poly.sumB_k (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k c b) ts) →
              @Eq α
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
                  (a.pow
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h11.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).mulTermsC_k
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h11.prem0 rfl HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h11.prem1)

-- Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h12.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).pow
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h12.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h12.prem1 : @Eq Lean.Grind.CommRing.Poly (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.sumB_k
        (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b)
        ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mulTermsC_k
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h12 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr) (k : Nat) (pa q : Lean.Grind.CommRing.Poly)
        (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq (List Lean.Grind.CommRing.Poly) ts (pa.mulTermsC_k q c) →
            @Eq Lean.Grind.CommRing.Poly p
                (Lean.Grind.CommRing.Poly.sumB_k (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k c b) ts) →
              @Eq α
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
                  (a.pow
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h12.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mulTermsC_k
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h12.prem0 rfl HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h12.prem1)

-- Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h13.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).pow
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.sumB_k
            (fun (a b : Lean.Grind.CommRing.Poly) =>
              a.combineC_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b)
            (@List.cons Lean.Grind.CommRing.Poly
              (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
              (@List.nil Lean.Grind.CommRing.Poly))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h13.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h13.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).pow
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h13 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr) (k : Nat) (pa q : Lean.Grind.CommRing.Poly)
        (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.pow k))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx q) →
            @Eq Lean.Grind.CommRing.Poly p
                (Lean.Grind.CommRing.Poly.sumB_k (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k c b) ts) →
              @Eq α
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
                  (a.pow
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h13.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@List.cons Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@List.nil Lean.Grind.CommRing.Poly)) (Lean.Grind.CommRing.Poly.sumB_k
      (fun (a b : Lean.Grind.CommRing.Poly) => a.combineC_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b)
      (@List.cons Lean.Grind.CommRing.Poly
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@List.nil Lean.Grind.CommRing.Poly))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h13.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h13.prem1 rfl)

-- Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h14.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).pow
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h14.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h14.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).pow
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h14 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr) (k : Nat) (pa q : Lean.Grind.CommRing.Poly)
        (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.pow k))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx q) →
            @Eq (List Lean.Grind.CommRing.Poly) ts (pa.mulTermsC_k q c) →
              @Eq α
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
                  (a.pow
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h14.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).mulTermsC_k
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h14.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_succ_of_termsC.h14.prem1 rfl)

-- Lean.Grind.CommRing.lt_false_of_kronLinS, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLinS.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLinS.h12.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).linSOk_k
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLinS.h12.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLinS.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.LawfulOrderLT α inst_3 inst_2] [inst_5 : @Std.IsPreorder α inst_2]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K a) (Lean.Grind.CommRing.Expr.kronLinEval_k K b) →
            @Eq Prop
              (@LT.lt α inst_3 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLinS.h12.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLinS.h12.prem0 HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLinS.h12.prem1)

-- Lean.Grind.CommRing.lt_false_of_kronLinS, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLinS.h13.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLinS.h13.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linSOk_k
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLinS.h13.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLinS.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.LawfulOrderLT α inst_3 inst_2] [inst_5 : @Std.IsPreorder α inst_2]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Prop
              (@LT.lt α inst_3 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLinS.h13.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLinS.h13.prem0 HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLinS.h13.prem1)

-- Lean.Grind.CommRing.Stepwise.superposeC, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h13.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h13.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h13.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h13 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k₁ : Int) (m₁ : Lean.Grind.CommRing.Mon) (p₁ : Lean.Grind.CommRing.Poly)
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h13.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@List.nil Nat) HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h13.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h13.prem1)

-- Lean.Grind.CommRing.Stepwise.superposeC, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h14.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.mergeHintC (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)
            (Lean.Grind.CommRing.Poly.mulMonC_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              Lean.Grind.CommRing.Mon.unit
              (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (Lean.Grind.CommRing.Poly.mulMonC_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              Lean.Grind.CommRing.Mon.unit
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h14.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h14 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k₁ : Int) (m₁ : Lean.Grind.CommRing.Mon) (p₁ : Lean.Grind.CommRing.Poly)
        (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHintC c hs (Lean.Grind.CommRing.Poly.mulMonC_k k₁ m₁ p₁ c)
              (Lean.Grind.CommRing.Poly.mulMonC_k k₂ m₂ p₂ c)) →
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h14.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.mergeHintC (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)
      (Lean.Grind.CommRing.Poly.mulMonC_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        Lean.Grind.CommRing.Mon.unit
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.mulMonC_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        Lean.Grind.CommRing.Mon.unit (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h14.prem0)

-- Lean.Grind.CommRing.Stepwise.superposeC, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h15.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.mergeHintC (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)
            (Lean.Grind.CommRing.Poly.mulMonC_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              Lean.Grind.CommRing.Mon.unit
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (Lean.Grind.CommRing.Poly.mulMonC_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              Lean.Grind.CommRing.Mon.unit
              (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h15.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h15 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k₁ : Int) (m₁ : Lean.Grind.CommRing.Mon) (p₁ : Lean.Grind.CommRing.Poly)
        (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHintC c hs (Lean.Grind.CommRing.Poly.mulMonC_k k₁ m₁ p₁ c)
              (Lean.Grind.CommRing.Poly.mulMonC_k k₂ m₂ p₂ c)) →
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h15.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.mergeHintC (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)
      (Lean.Grind.CommRing.Poly.mulMonC_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        Lean.Grind.CommRing.Mon.unit (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.mulMonC_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        Lean.Grind.CommRing.Mon.unit
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.superposeC.h15.prem0)

-- Lean.Grind.CommRing.lt_false_of_kronSN, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h12.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h12.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronEval_k K B a) (Lean.Grind.CommRing.Expr.kronEval_k K B b) →
            @Eq Prop
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h12.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h12.prem0 HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h12.prem1)

-- Lean.Grind.CommRing.lt_false_of_kronSN, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h13.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h13.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h13.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Prop
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h13.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h13.prem0 HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronSN.h13.prem1)

-- Lean.Grind.Linarith.diseq_split_resolve, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h6.inst : Not
      (@LT.lt UInt8 instLTUInt8
        (@Lean.Grind.Linarith.Poly.denote' UInt8
          (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
          (Lean.Grind.Linarith.Poly.add
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
        (@OfNat.ofNat UInt8 (nat_lit 0)
          (@Zero.toOfNat0 UInt8
            (@Lean.Grind.AddCommMonoid.toZero UInt8
              (@Lean.Grind.NatModule.toAddCommMonoid UInt8
                (@Lean.Grind.IntModule.toNatModule UInt8
                  (@Lean.Grind.Ring.toIntModule UInt8
                    (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h6.prem0 : @Eq Bool
      (Lean.Grind.Linarith.diseq_split_cert
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h6.prem1 : @Ne UInt8
      (@Lean.Grind.Linarith.Poly.denote' UInt8
        (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
        (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      (@OfNat.ofNat UInt8 (nat_lit 0)
        (@Zero.toOfNat0 UInt8
          (@Lean.Grind.AddCommMonoid.toZero UInt8
            (@Lean.Grind.NatModule.toAddCommMonoid UInt8
              (@Lean.Grind.IntModule.toNatModule UInt8
                (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h6.prem2 : Not
      (@LT.lt UInt8 instLTUInt8
        (@Lean.Grind.Linarith.Poly.denote' UInt8
          (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
          (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
        (@OfNat.ofNat UInt8 (nat_lit 0)
          (@Zero.toOfNat0 UInt8
            (@Lean.Grind.AddCommMonoid.toZero UInt8
              (@Lean.Grind.NatModule.toAddCommMonoid UInt8
                (@Lean.Grind.IntModule.toNatModule UInt8
                  (@Lean.Grind.Ring.toIntModule UInt8
                    (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsLinearOrder α inst_1]
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
                      (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h6.inst (@hc_h (UInt8) (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)) (instLEUInt8) (instLTUInt8) _ _ (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h6.prem0 HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h6.prem1 HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h6.prem2)

-- Lean.Grind.Linarith.diseq_split_resolve, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h10.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h10.prem0 : @Ne Int
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
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h10.prem1 : Not
      (@LT.lt Int Int.instLTInt
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
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsLinearOrder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 (@Std.IsLinearPreorder.toIsPreorder α inst_1 (@Std.IsLinearOrder.toIsLinearPreorder α inst_1 inst_4))]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ : Lean.Grind.Linarith.Poly),
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
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h10.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h10.prem0 HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h10.prem1)

-- Lean.Grind.Linarith.diseq_split_resolve, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h11.prem0 : @Eq Bool (Lean.Grind.Linarith.diseq_split_cert Lean.Grind.Linarith.Poly.nil Lean.Grind.Linarith.Poly.nil) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h11.prem1 : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsLinearOrder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 (@Std.IsLinearPreorder.toIsPreorder α inst_1 (@Std.IsLinearOrder.toIsLinearPreorder α inst_1 inst_4))]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.diseq_split_cert p₁ p₂) Bool.true →
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
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h11.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h11.prem0 HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h11.prem1)

-- Lean.Grind.Linarith.diseq_split_resolve, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h12.inst : Not
      (@LT.lt Int Int.instLTInt
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
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h12.prem0 : @Eq Bool
      (Lean.Grind.Linarith.diseq_split_cert
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h12.prem1 : @Ne Int
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
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsLinearOrder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 (@Std.IsLinearPreorder.toIsPreorder α inst_1 (@Std.IsLinearOrder.toIsLinearPreorder α inst_1 inst_4))]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.diseq_split_cert p₁ p₂) Bool.true →
          @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h12.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h12.prem0 HypCheckProof.Lean.Grind.Linarith.diseq_split_resolve.h12.prem1)

-- Lean.Grind.AC.eq_simp_rhs_ac, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h10.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h10.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h10.prem1 : Std.Commutative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Commutative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h10.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h10.prem3 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h10 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.Commutative ctx.op}
        (c lhs₁ rhs₁ lhs₂ rhs₂ rhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₂ →
            Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₂' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h10.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h10.prem0 HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h10.prem1 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h10.prem2 HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h10.prem3)

-- Lean.Grind.AC.eq_simp_rhs_ac, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h12.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h12.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h12.prem1 : Std.Commutative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Commutative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h12.prem2 : Lean.Grind.AC.simp_ac_cert (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0)
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h12.prem3 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h12 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.Commutative ctx.op}
        (c lhs₁ rhs₁ lhs₂ rhs₂ rhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.simp_ac_cert c lhs₁ rhs₁ rhs₂ rhs₂' = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
            Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₂' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h12.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h12.prem0 HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h12.prem1 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h12.prem2 HypCheckProof.Lean.Grind.AC.eq_simp_rhs_ac.h12.prem3)

-- Lean.Grind.CommRing.lt_mul, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_mul.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_mul.h11.prem0 : @LT.lt Int Int.instLTInt
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_mul.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly) (k : Int) (p : Lean.Grind.CommRing.Poly),
        @LT.lt α inst_2 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
          @LT.lt α inst_2 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_mul.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_mul.h11.prem0)

-- Lean.Grind.CommRing.lt_mul, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_mul.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_mul.h12.prem0 : @Eq Bool
      (Lean.Grind.CommRing.mul_ineq_cert
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_mul.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly) (k : Int) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.mul_ineq_cert p₁ k p) Bool.true →
          @LT.lt α inst_2 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_mul.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_mul.h12.prem0)

-- Lean.Grind.AC.diseq_simp_lhs_ac, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_ac.h10.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_ac.h10.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_ac.h10.prem1 : Std.Commutative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Commutative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_ac.h10.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_ac.h10.prem3 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) ≠
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_ac.h10 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.Commutative ctx.op}
        (c lhs₁ rhs₁ lhs₂ rhs₂ lhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ ≠ Lean.Grind.AC.Seq.denote ctx rhs₂ →
            Lean.Grind.AC.Seq.denote ctx lhs₂' ≠ Lean.Grind.AC.Seq.denote ctx rhs₂ := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_ac.h10.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_ac.h10.prem0 HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_ac.h10.prem1 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_ac.h10.prem2 HypCheckProof.Lean.Grind.AC.diseq_simp_lhs_ac.h10.prem3)

-- Lean.Grind.CommRing.le_norm_poly0, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly0.h5.inst : Not
      (@Eq Prop
        (@LE.le UInt8 instLEUInt8
          (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
            (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
            (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var
                (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).neg))
        (@LE.le UInt8 instLEUInt8
          (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
            (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
            (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly0.h5.prem0 : @Eq Lean.Grind.CommRing.Expr
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
            (Lean.Grind.CommRing.Expr.var
                (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).neg)).toExpr_k := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly0.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (lhs.sub rhs)) →
          @Eq Lean.Grind.CommRing.Expr lhs' p.toExpr_k →
            @Eq Prop
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
                  (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_poly0.h5.inst (@hc_h (UInt8) (Lean.Grind.instCommRingUInt8) (instLEUInt8) (instLTUInt8) _ (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).neg) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).neg)) rfl HypCheckProof.Lean.Grind.CommRing.le_norm_poly0.h5.prem0)

-- Lean.Grind.CommRing.le_norm_poly0, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly0.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly0.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Expr lhs' p.toExpr_k →
          @Eq Prop
            (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
                (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_poly0.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl)

-- Lean.Grind.CommRing.le_norm_poly0, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly0.h13.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_poly0.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (lhs.sub rhs)) →
          @Eq Prop
            (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
                (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_poly0.h13.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) rfl)

-- Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h10.inst : Not
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
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h10.prem0 : @LE.le Int Int.instLEInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h10 : Not
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
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) c a)
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) c b)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h10.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h10.prem0)

-- Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h11.inst : Not
      (@LE.le Int Int.instLEInt
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h11.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h11 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.IsPartialOrder R inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2
            (@Std.IsPartialOrder.toIsPreorder R inst_1 inst_3)]
        [inst_5 : @Std.LawfulOrderLT R inst_2 inst_1] {a b c : R},
        @LE.le R inst_1 a b →
          @LE.le R inst_1
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) c a)
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) c b)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h11.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h11.prem0)

-- Lean.Grind.Linarith.le_le_combine, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_le_combine.h9.inst : Not
      (@LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.Linarith.le_le_combine.h9.prem0 : @LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.Linarith.le_le_combine.h9.prem1 : @LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.Linarith.le_le_combine.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        [inst_3 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 inst_2]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
        @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
          @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₃)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.le_le_combine.h9.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.le_le_combine.h9.prem0 HypCheckProof.Lean.Grind.Linarith.le_le_combine.h9.prem1)

-- Lean.Grind.Linarith.le_le_combine, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_le_combine.h10.inst : Not
      (@LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.Linarith.le_le_combine.h10.prem0 : @Eq Bool
      (Lean.Grind.Linarith.le_le_combine_cert
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        Lean.Grind.Linarith.Poly.nil
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_le_combine.h10.prem1 : @LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.Linarith.le_le_combine.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        [inst_3 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 inst_2]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.le_le_combine_cert p₁ p₂ p₃) Bool.true →
          @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₃)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.le_le_combine.h10.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.le_le_combine.h10.prem0 HypCheckProof.Lean.Grind.Linarith.le_le_combine.h10.prem1)

-- Lean.Grind.Linarith.le_le_combine, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_le_combine.h11.inst : Not
      (@LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.Linarith.le_le_combine.h11.prem0 : @Eq Bool
      (Lean.Grind.Linarith.le_le_combine_cert Lean.Grind.Linarith.Poly.nil
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_le_combine.h11.prem1 : @LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.Linarith.le_le_combine.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        [inst_3 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 inst_2]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.le_le_combine_cert p₁ p₂ p₃) Bool.true →
          @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₃)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.le_le_combine.h11.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.le_le_combine.h11.prem0 HypCheckProof.Lean.Grind.Linarith.le_le_combine.h11.prem1)

-- Lean.Grind.AC.eq_simp_rhs_middle, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_middle.h10.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_middle.h10.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_middle.h10.prem1 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_middle.h10.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_middle.h10 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op}
        (lhs₁ rhs₁ head tail lhs₂ rhs₂ rhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₂ →
            Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₂' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_simp_rhs_middle.h10.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_middle.h10.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_middle.h10.prem1 HypCheckProof.Lean.Grind.AC.eq_simp_rhs_middle.h10.prem2)

-- Lean.Grind.CommRing.Expr.denote_add_ofC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combineC_k
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h3.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h3.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (a b : Lean.Grind.CommRing.Expr) (pa pb p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pb) →
            @Eq Lean.Grind.CommRing.Poly p (pa.combineC_k c pb) →
              @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.add b))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combineC_k
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h3.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h3.prem1 rfl)

-- Lean.Grind.CommRing.Expr.denote_add_ofC, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h10.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).combineC_k
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h10.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h10 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr) (pa pb p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pb) →
          @Eq Lean.Grind.CommRing.Poly p (pa.combineC_k c pb) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.add b))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h10.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).combineC_k
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h10.prem0 rfl)

-- Lean.Grind.CommRing.Expr.denote_add_ofC, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h11.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combineC_k
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h11.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h11 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr) (pa pb p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq Lean.Grind.CommRing.Poly p (pa.combineC_k c pb) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.add b))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h11.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combineC_k
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h11.prem0 rfl)

-- Lean.Grind.CommRing.Expr.denote_add_ofC, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h12.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h12.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h12.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h12 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr) (pa pb p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pb) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.add b))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h12.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h12.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_ofC.h12.prem1)

-- Lean.Grind.CommRing.le_true_of_kronLinS, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h10.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h10.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).linSOk_k
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h10.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        [inst_2 : LE α] [inst_3 : @Std.IsPreorder α inst_2] (ctx : Lean.Grind.CommRing.Context α) (K : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K a) (Lean.Grind.CommRing.Expr.kronLinEval_k K b) →
            @Eq Prop
              (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h10.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h10.prem0 HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h10.prem1)

-- Lean.Grind.CommRing.le_true_of_kronLinS, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h11.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).linSOk_k
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h11.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        [inst_2 : LE α] [inst_3 : @Std.IsPreorder α inst_2] (ctx : Lean.Grind.CommRing.Context α) (K : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Prop
              (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h11.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h11.prem0 HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h11.prem1)

-- Lean.Grind.CommRing.le_true_of_sub, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_sub.h6.inst : Not
      (@Eq Prop
        (@LE.le UInt8 instLEUInt8
          (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
            (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 255) (@UInt8.instOfNat (nat_lit 255))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
            (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 255) (@UInt8.instOfNat (nat_lit 255))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_sub.h6.prem0 : @Eq UInt8
      (@HSub.hSub UInt8 UInt8 UInt8
        (@instHSub UInt8 (@Lean.Grind.Ring.toSub UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)))
        (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
          (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 255) (@UInt8.instOfNat (nat_lit 255))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
          (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 255) (@UInt8.instOfNat (nat_lit 255))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
        (Int.ofNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_sub.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (n : Nat),
        @Eq α
            (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs))
            (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) (Int.ofNat n)) →
          @Eq Prop
            (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_sub.h6.inst (@hc_h (UInt8) (Lean.Grind.instCommRingUInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 255) (@UInt8.instOfNat (nat_lit 255)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Lean.Grind.CommRing.le_true_of_sub.h6.prem0)

-- Lean.Grind.CommRing.le_true_of_sub, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_sub.h11.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        True) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_sub.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (n : Nat),
        @Eq Prop
          (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
          True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_sub.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))

-- Lean.Grind.AC.diseq_simp_rhs_suffix, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_suffix.h9.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_suffix.h9.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_suffix.h9.prem1 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_suffix.h9.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) ≠
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_suffix.h9 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op}
        (lhs₁ rhs₁ head lhs₂ rhs₂ rhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ ≠ Lean.Grind.AC.Seq.denote ctx rhs₂ →
            Lean.Grind.AC.Seq.denote ctx lhs₂ ≠ Lean.Grind.AC.Seq.denote ctx rhs₂' := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_suffix.h9.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_suffix.h9.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_suffix.h9.prem1 HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_suffix.h9.prem2)

-- Lean.Grind.Order.le_unsat_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_unsat_k.h6.inst : Not False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_unsat_k.h6.prem0 : @Eq Bool
      ((@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).blt'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_unsat_k.h6.prem1 : @LE.le UInt8 instLEUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_unsat_k.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α] {a : α} {k : Int},
        @Eq Bool (k.blt' (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) Bool.true →
          @LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k)) →
            False) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_unsat_k.h6.inst (@hc_h (UInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.Order.le_unsat_k.h6.prem0 HypCheckProof.Lean.Grind.Order.le_unsat_k.h6.prem1)

-- Lean.Grind.Order.le_unsat_k, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_unsat_k.h9.inst : Not False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_unsat_k.h9.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_unsat_k.h9 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a : α} {k : Int},
        @LE.le α inst a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k)) →
          False) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_unsat_k.h9.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_unsat_k.h9.prem0)

-- Lean.Grind.Order.le_unsat_k, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_unsat_k.h10.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_unsat_k.h10.prem0 : (-1).blt' 0 = Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_unsat_k.h10 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α] [inst_3 : Std.IsPreorder α]
        [inst_4 : Lean.Grind.Ring α] [inst : Lean.Grind.OrderedRing α] {a : α} {k : Int}, k.blt' 0 = Bool.true → False := fun hc_h => HypCheckProof.Lean.Grind.Order.le_unsat_k.h10.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (Lean.Grind.instCommRingInt.toRing) _ (0) (-1) HypCheckProof.Lean.Grind.Order.le_unsat_k.h10.prem0)

-- Lean.Grind.OrderedRing.mul_nonpos_of_nonneg_of_nonpos, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonneg_of_nonpos.h9.inst : ¬-1 * -1 ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonneg_of_nonpos.h9.prem0 : -1 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonneg_of_nonpos.h9 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Lean.Grind.OrderedRing R] [inst_5 : Std.LawfulOrderLT R] {a b : R}, b ≤ 0 → a * b ≤ 0 := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonneg_of_nonpos.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt.toRing) (Int.instLEInt) (Int.instLTInt) _ _ _ (-1) (-1) HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonneg_of_nonpos.h9.prem0)

-- Lean.Grind.OrderedRing.mul_nonpos_of_nonneg_of_nonpos, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonneg_of_nonpos.h10.inst : Not
      (@LE.le Int Int.instLEInt
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonneg_of_nonpos.h10.prem0 : @LE.le Int Int.instLEInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonneg_of_nonpos.h10 : Not
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
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) a b)
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonneg_of_nonpos.h10.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonneg_of_nonpos.h10.prem0)

-- Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h9.inst : Not
      (@LE.le Int Int.instLEInt
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h9.prem0 : @LE.le Int Int.instLEInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h9 : Not
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
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) a b)
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h9.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h9.prem0)

-- Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h10.inst : ¬-1 * -1 ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h10.prem0 : -1 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h10 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Lean.Grind.OrderedRing R] [inst_5 : Std.LawfulOrderLT R] {a b : R}, a ≤ 0 → a * b ≤ 0 := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt.toRing) (Int.instLEInt) (Int.instLTInt) _ _ _ (-1) (-1) HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h10.prem0)

-- Lean.Grind.CommRing.le_true_of_kronLin, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h9.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h9.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).linOk_k
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h9.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linOk_k b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K a) (Lean.Grind.CommRing.Expr.kronLinEval_k K b) →
            @Eq Prop
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h9.prem0 HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h9.prem1)

-- Lean.Grind.CommRing.le_true_of_kronLin, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h10.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h10.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).linOk_k
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h10.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linOk_k b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Prop
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h10.prem0 HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h10.prem1)

-- Lean.Grind.Field.IsOrdered.mul_lt_mul_iff_of_pos_right, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_lt_mul_iff_of_pos_right.h10.inst : Not
      (Iff
        (@LT.lt Rat Rat.instLT
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
        (@LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_lt_mul_iff_of_pos_right.h10 : Not
      (∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R]
        [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1] [inst_4 : @Std.IsLinearOrder R inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing R
            (@Lean.Grind.CommSemiring.toSemiring R
              (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))
            inst_1 inst_2
            (@Std.IsLinearPreorder.toIsPreorder R inst_1 (@Std.IsLinearOrder.toIsLinearPreorder R inst_1 inst_4))]
        {a b c : R},
        Iff
          (@LT.lt R inst_2
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              a c)
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              b c))
          (@LT.lt R inst_2 a b)) := fun hc_h => HypCheckProof.Lean.Grind.Field.IsOrdered.mul_lt_mul_iff_of_pos_right.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Int.Internal.Linear.cooper_unsat, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.cooper_unsat.h7.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.cooper_unsat.h7.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.cooper_unsat.h7.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.cooper_unsat.h7.prem2 : 0 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.cooper_unsat.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly) (d α β : Int),
        Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → d ∣ Int.Internal.Linear.Poly.denote' ctx p₃ → False := fun hc_h => HypCheckProof.Int.Internal.Linear.cooper_unsat.h7.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (0) (0) (0) HypCheckProof.Int.Internal.Linear.cooper_unsat.h7.prem0 HypCheckProof.Int.Internal.Linear.cooper_unsat.h7.prem1 HypCheckProof.Int.Internal.Linear.cooper_unsat.h7.prem2)

-- Lean.Grind.CommRing.le_true_of_toPoly_eq, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPoly_eq.h10.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        True) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPoly_eq.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (bal₁ bal₂ : Bool) (lhs rhs : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal₂ rhs) →
          @Eq Prop
            (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_toPoly_eq.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl)

-- Lean.Grind.CommRing.le_true_of_toPoly_eq, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPoly_eq.h11.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        True) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPoly_eq.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (bal₁ bal₂ : Bool) (lhs rhs : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal₁ lhs) →
          @Eq Prop
            (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_toPoly_eq.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) rfl)

-- Lean.Grind.IntModule.OfNatModule.of_diseq, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.IntModule.OfNatModule.of_diseq.h9.inst : ¬Lean.Grind.IntModule.OfNatModule.toQ 0 ≠ Lean.Grind.IntModule.OfNatModule.toQ 0 := by
  simp
theorem HypCheckProof.Lean.Grind.IntModule.OfNatModule.of_diseq.h9 : ¬∀ {α : Type} [inst : Lean.Grind.NatModule α] [inst_1 : Lean.Grind.AddRightCancel α] {a b : α}
        {a' b' : Lean.Grind.IntModule.OfNatModule.Q α},
        Lean.Grind.IntModule.OfNatModule.toQ a = a' → Lean.Grind.IntModule.OfNatModule.toQ b = b' → a' ≠ b' := fun hc_h => HypCheckProof.Lean.Grind.IntModule.OfNatModule.of_diseq.h9.inst (@hc_h (Nat) (Lean.Grind.Semiring.toNatModule) _ (0) (0) (Lean.Grind.IntModule.OfNatModule.toQ 0) (Lean.Grind.IntModule.OfNatModule.toQ 0) rfl rfl)

-- Lean.Grind.OrderedAdd.zsmul_le_zsmul, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h8.inst : Not
      (@LE.le Int Int.instLEInt
        (@HSMul.hSMul Int Int Int
          (@instHSMul Int Int
            (@Lean.Grind.IntModule.zsmul Int
              (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@HSMul.hSMul Int Int Int
          (@instHSMul Int Int
            (@Lean.Grind.IntModule.zsmul Int
              (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h8.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h8 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : @Std.IsPreorder M inst] [inst_2 : Lean.Grind.IntModule M]
        [inst_3 :
          @Lean.Grind.OrderedAdd M
            (@instHAdd M
              (@Lean.Grind.AddCommMonoid.toAdd M
                (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2))))
            inst inst_1]
        {a b : M} {k : Int},
        @LE.le M inst a b →
          @LE.le M inst (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k a)
            (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k b)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h8.inst (@hc_h (Int) (Int.instLEInt) _ (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h8.prem0)

-- Lean.Grind.OrderedAdd.zsmul_le_zsmul, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h9.inst : Not
      (@LE.le Int Int.instLEInt
        (@HSMul.hSMul Int Int Int
          (@instHSMul Int Int
            (@Lean.Grind.IntModule.zsmul Int
              (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@HSMul.hSMul Int Int Int
          (@instHSMul Int Int
            (@Lean.Grind.IntModule.zsmul Int
              (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h9.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h9 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : @Std.IsPreorder M inst] [inst_2 : Lean.Grind.IntModule M]
        [inst_3 :
          @Lean.Grind.OrderedAdd M
            (@instHAdd M
              (@Lean.Grind.AddCommMonoid.toAdd M
                (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2))))
            inst inst_1]
        {a b : M} {k : Int},
        @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k →
          @LE.le M inst (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k a)
            (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k b)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h9.inst (@hc_h (Int) (Int.instLEInt) _ (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h9.prem0)

-- Lean.Grind.AC.eq_norm_ac, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_norm_ac.h8.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_norm_ac.h8.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_norm_ac.h8.prem1 : Std.Commutative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Commutative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_norm_ac.h8.prem2 : Lean.Grind.AC.Expr.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Expr.var 0) =
      Lean.Grind.AC.Expr.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Expr.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_norm_ac.h8 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} {x : Std.Commutative ctx.op}
        (lhs rhs : Lean.Grind.AC.Expr) (lhs' rhs' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Expr.denote ctx lhs = Lean.Grind.AC.Expr.denote ctx rhs →
          Lean.Grind.AC.Seq.denote ctx lhs' = Lean.Grind.AC.Seq.denote ctx rhs' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_norm_ac.h8.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_norm_ac.h8.prem0 HypCheckProof.Lean.Grind.AC.eq_norm_ac.h8.prem1 (Lean.Grind.AC.Expr.var 0) (Lean.Grind.AC.Expr.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_norm_ac.h8.prem2)

-- Lean.Grind.AC.eq_norm_ac, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_norm_ac.h9.inst : ¬Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 1) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_norm_ac.h9.prem0 : Std.Associative
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_norm_ac.h9.prem1 : Std.Commutative
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Commutative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_norm_ac.h9.prem2 : Lean.Grind.AC.eq_norm_ac_cert (Lean.Grind.AC.Expr.var 0) (Lean.Grind.AC.Expr.var 1) (Lean.Grind.AC.Seq.var 0)
        (Lean.Grind.AC.Seq.var 1) =
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.AC.eq_norm_ac.h9 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} {x : Std.Commutative ctx.op}
        (lhs rhs : Lean.Grind.AC.Expr) (lhs' rhs' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.eq_norm_ac_cert lhs rhs lhs' rhs' = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs' = Lean.Grind.AC.Seq.denote ctx rhs' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_norm_ac.h9.inst (@hc_h (Nat) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
      op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_norm_ac.h9.prem0 HypCheckProof.Lean.Grind.AC.eq_norm_ac.h9.prem1 (Lean.Grind.AC.Expr.var 0) (Lean.Grind.AC.Expr.var 1) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 1) HypCheckProof.Lean.Grind.AC.eq_norm_ac.h9.prem2)

-- Lean.Grind.AC.superpose_head_idempotent, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h3.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h3.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h3.prem1 : Lean.Grind.AC.superpose_head_idempotent_cert 0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0)
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h3.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op} (x : Lean.Grind.AC.Var)
        (lhs₁ rhs₁ rhs : Lean.Grind.AC.Seq),
        Lean.Grind.AC.superpose_head_idempotent_cert x lhs₁ rhs₁ rhs = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
            Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs := fun hc_h => HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h3.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h3.prem0 (0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h3.prem1 HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h3.prem2)

-- Lean.Grind.AC.superpose_head_idempotent, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h8.inst : ¬Lean.Grind.AC.Seq.denote
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
theorem HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h8.prem0 : Std.Associative
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   (intros; simp_all; done)))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h8.prem1 : Std.IdempotentOp
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }.op := (@Std.IdempotentOp.mk _ _ (by (try dsimp only);   (intros; simp_all; done)))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h8.prem2 : Lean.Grind.AC.Seq.denote
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
theorem HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h8 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.IdempotentOp ctx.op}
        (x : Lean.Grind.AC.Var) (lhs₁ rhs₁ rhs : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs := fun hc_h => HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h8.inst (@hc_h (Nat) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
      op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h8.prem0 HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h8.prem1 (0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 1) HypCheckProof.Lean.Grind.AC.superpose_head_idempotent.h8.prem2)

-- Lean.Grind.AC.diseq_erase_dup, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h3.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h3.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h3.prem1 : Lean.Grind.AC.eq_erase_dup_cert (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0))
        (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h3.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) ≠
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} (lhs rhs lhs' rhs' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.eq_erase_dup_cert lhs rhs lhs' rhs' = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs ≠ Lean.Grind.AC.Seq.denote ctx rhs →
            Lean.Grind.AC.Seq.denote ctx lhs' ≠ Lean.Grind.AC.Seq.denote ctx rhs' := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h3.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h3.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h3.prem1 HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h3.prem2)

-- Lean.Grind.AC.diseq_erase_dup, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h9.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a x : Bool) => a :
            Lean.Grind.AC.Context Bool }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a x : Bool) => a :
            Lean.Grind.AC.Context Bool }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h9.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a x : Bool) => a :
          Lean.Grind.AC.Context Bool }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   decide))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h9.prem1 : Std.IdempotentOp
      { vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a x : Bool) => a :
          Lean.Grind.AC.Context Bool }.op := (@Std.IdempotentOp.mk _ _ (by (try dsimp only);   decide))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h9.prem2 : Lean.Grind.AC.eq_erase_dup_cert (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0)
        (Lean.Grind.AC.Seq.var 0) =
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h9 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} {x : Std.IdempotentOp ctx.op}
        (lhs rhs lhs' rhs' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.eq_erase_dup_cert lhs rhs lhs' rhs' = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs' ≠ Lean.Grind.AC.Seq.denote ctx rhs' := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h9.inst (@hc_h (Bool) ({ vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a x : Bool) => a :
      Lean.Grind.AC.Context Bool }) HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h9.prem0 HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h9.prem1 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_erase_dup.h9.prem2)

-- Lean.Grind.Order.le_eq_true_k, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_k.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_k.h9 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a : α} {k : Int},
        @Eq Prop
          (@LE.le α inst a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k)))
          True) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_true_k.h9.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))

-- Lean.Grind.Linarith.eq_eq_subst, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_eq_subst.h7.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.eq_eq_subst.h7.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.Linarith.eq_eq_subst.h7.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.Linarith.eq_eq_subst.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] (ctx : Lean.Grind.Linarith.Context α) (x : Lean.Grind.Linarith.Var)
        (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
        @Eq α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
          @Eq α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @Eq α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₃)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.eq_eq_subst.h7.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.eq_eq_subst.h7.prem0 HypCheckProof.Lean.Grind.Linarith.eq_eq_subst.h7.prem1)

-- Lean.Grind.CommRing.eq_true_of_kron, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kron.h8.inst : Not
      (@Eq Prop
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kron.h8.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kron.h8.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kron.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronEval_k K B a) (Lean.Grind.CommRing.Expr.kronEval_k K B b) →
            @Eq Prop
              (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_kron.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kron.h8.prem0 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kron.h8.prem1)

-- Lean.Grind.CommRing.eq_true_of_kron, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kron.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kron.h9.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kron.h9.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kron.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Prop
              (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_kron.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kron.h9.prem0 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kron.h9.prem1)

-- Int.Internal.Linear.dvd_solve_elim, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_solve_elim.h7.inst : ¬0 ∣
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_solve_elim.h7.prem0 : 0 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_solve_elim.h7.prem1 : 0 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_solve_elim.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (d₁ : Int) (p₁ : Int.Internal.Linear.Poly) (d₂ : Int)
        (p₂ : Int.Internal.Linear.Poly) (d : Int) (p : Int.Internal.Linear.Poly),
        d₁ ∣ Int.Internal.Linear.Poly.denote' ctx p₁ →
          d₂ ∣ Int.Internal.Linear.Poly.denote' ctx p₂ → d ∣ Int.Internal.Linear.Poly.denote' ctx p := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_solve_elim.h7.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (0) (Int.Internal.Linear.Poly.num 0) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.dvd_solve_elim.h7.prem0 HypCheckProof.Int.Internal.Linear.dvd_solve_elim.h7.prem1)

-- Int.Internal.Linear.eq_le_subst_nonpos_rfl, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0)
          (Int.Internal.Linear.Poly.combine_mul_k ((Int.Internal.Linear.Poly.num (-1)).coeff_k 0)
            ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0).neg_k
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num (-1))) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h5.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h5.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0) (Int.Internal.Linear.Poly.num (-1)) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        p₃ = Int.Internal.Linear.Poly.combine_mul_k (p₂.coeff_k x) (p₁.coeff_k x).neg_k p₁ p₂ →
          Int.Internal.Linear.Poly.denote' ctx p₁ = 0 →
            Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h5.inst (@hc_h (Lean.RArray.leaf 0) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num (-1)) (Int.Internal.Linear.Poly.combine_mul_k ((Int.Internal.Linear.Poly.num (-1)).coeff_k 0)
      ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0).neg_k
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num (-1))) rfl HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h5.prem0 HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h5.prem1)

-- Int.Internal.Linear.eq_le_subst_nonpos_rfl, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h6.prem0 : ((Int.Internal.Linear.Poly.num 0).coeff_k 0).ble' 0 = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h6.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h6.prem2 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        (p₁.coeff_k x).ble' 0 = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₁ = 0 →
            Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h6.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h6.prem0 HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h6.prem1 HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h6.prem2)

-- Int.Internal.Linear.eq_le_subst_nonpos_rfl, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h7.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0)
          (Int.Internal.Linear.Poly.combine_mul_k
            ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0)
            ((Int.Internal.Linear.Poly.num 1).coeff_k 0).neg_k (Int.Internal.Linear.Poly.num 1)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h7.prem0 : ((Int.Internal.Linear.Poly.num 1).coeff_k 0).ble' 0 = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h7.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        (p₁.coeff_k x).ble' 0 = Bool.true →
          p₃ = Int.Internal.Linear.Poly.combine_mul_k (p₂.coeff_k x) (p₁.coeff_k x).neg_k p₁ p₂ →
            Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h7.inst (@hc_h (Lean.RArray.leaf 0) (0) (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.combine_mul_k ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0)
      ((Int.Internal.Linear.Poly.num 1).coeff_k 0).neg_k (Int.Internal.Linear.Poly.num 1)
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h7.prem0 rfl HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h7.prem1)

-- Int.Internal.Linear.eq_le_subst_nonpos_rfl, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h8.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.combine_mul_k
            ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 1)
            ((Int.Internal.Linear.Poly.add 1 0
                    (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0))).coeff_k
                1).neg_k
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0)))
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h8.prem0 : ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0))).coeff_k
            1).ble'
        0 =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h8.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0))) =
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h8 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        (p₁.coeff_k x).ble' 0 = Bool.true →
          p₃ = Int.Internal.Linear.Poly.combine_mul_k (p₂.coeff_k x) (p₁.coeff_k x).neg_k p₁ p₂ →
            Int.Internal.Linear.Poly.denote' ctx p₁ = 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h8.inst (@hc_h (Lean.RArray.leaf 1) (1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0))) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.combine_mul_k ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 1)
      ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0))).coeff_k
          1).neg_k
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0)))
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h8.prem0 rfl HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos_rfl.h8.prem1)

-- Lean.Grind.OrderedAdd.lt_neg_iff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.lt_neg_iff.h4.inst : ¬(UInt8.ofNat 0 < -UInt8.ofNat 1 ↔ UInt8.ofNat 1 < -UInt8.ofNat 0) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.lt_neg_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommGroup M] [inst_3 : LT M]
        [inst : Std.LawfulOrderLT M] {a b : M}, a < -b ↔ b < -a := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.lt_neg_iff.h4.inst (@hc_h (UInt8) (instLEUInt8) _ (Lean.Grind.Ring.toAddCommGroup) (instLTUInt8) _ (UInt8.ofNat 0) (UInt8.ofNat 1))

-- Lean.Grind.AC.eq_norm_a, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_norm_a.h7.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_norm_a.h7.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_norm_a.h7.prem1 : Lean.Grind.AC.Expr.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Expr.var 0) =
      Lean.Grind.AC.Expr.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Expr.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_norm_a.h7 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} (lhs rhs : Lean.Grind.AC.Expr)
        (lhs' rhs' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Expr.denote ctx lhs = Lean.Grind.AC.Expr.denote ctx rhs →
          Lean.Grind.AC.Seq.denote ctx lhs' = Lean.Grind.AC.Seq.denote ctx rhs' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_norm_a.h7.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_norm_a.h7.prem0 (Lean.Grind.AC.Expr.var 0) (Lean.Grind.AC.Expr.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_norm_a.h7.prem1)

-- Lean.Grind.AC.eq_norm_a, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_norm_a.h8.inst : ¬Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 1) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_norm_a.h8.prem0 : Std.Associative
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_norm_a.h8.prem1 : Lean.Grind.AC.eq_norm_a_cert (Lean.Grind.AC.Expr.var 0) (Lean.Grind.AC.Expr.var 1) (Lean.Grind.AC.Seq.var 0)
        (Lean.Grind.AC.Seq.var 1) =
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.AC.eq_norm_a.h8 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} (lhs rhs : Lean.Grind.AC.Expr)
        (lhs' rhs' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.eq_norm_a_cert lhs rhs lhs' rhs' = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs' = Lean.Grind.AC.Seq.denote ctx rhs' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_norm_a.h8.inst (@hc_h (Nat) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
      op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_norm_a.h8.prem0 (Lean.Grind.AC.Expr.var 0) (Lean.Grind.AC.Expr.var 1) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 1) HypCheckProof.Lean.Grind.AC.eq_norm_a.h8.prem1)

-- Int.Internal.Linear.eq_eq_subst'_rfl, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h6.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h6.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (a b : Int) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ = 0 →
          Int.Internal.Linear.Poly.denote' ctx p₂ = 0 → Int.Internal.Linear.Poly.denote' ctx p₃ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h6.inst (@hc_h (Lean.RArray.leaf 1) (0) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h6.prem0 HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h6.prem1)

-- Int.Internal.Linear.eq_eq_subst'_rfl, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h7.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.combine_mul_k 1 (Int.neg_k 0)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h7.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (a b : Int) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        p₃ = Int.Internal.Linear.Poly.combine_mul_k b a.neg_k p₁ p₂ →
          Int.Internal.Linear.Poly.denote' ctx p₂ = 0 → Int.Internal.Linear.Poly.denote' ctx p₃ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h7.inst (@hc_h (Lean.RArray.leaf 1) (0) (1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.combine_mul_k 1 (Int.neg_k 0)
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0)) rfl HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h7.prem0)

-- Int.Internal.Linear.eq_eq_subst'_rfl, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h8.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.combine_mul_k 0 (Int.neg_k 1) (Int.Internal.Linear.Poly.num 0)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h8.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h8 : ¬∀ (ctx : Int.Internal.Linear.Context) (a b : Int) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        p₃ = Int.Internal.Linear.Poly.combine_mul_k b a.neg_k p₁ p₂ →
          Int.Internal.Linear.Poly.denote' ctx p₁ = 0 → Int.Internal.Linear.Poly.denote' ctx p₃ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h8.inst (@hc_h (Lean.RArray.leaf 1) (1) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.combine_mul_k 0 (Int.neg_k 1) (Int.Internal.Linear.Poly.num 0)
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) rfl HypCheckProof.Int.Internal.Linear.eq_eq_subst'_rfl.h8.prem0)

-- Lean.Grind.Field.NormNum.zpow_eq, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.zpow_eq.h7.inst : Not
      (@Eq Rat
        (@HPow.hPow Rat Int Rat (@Lean.Grind.Field.zpow Rat Lean.Grind.instFieldRat)
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.zpow_eq.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (a : α) (n : Int) (v₁ v : Rat),
        @Eq α a (@Lean.Grind.Field.NormNum.ofRat α inst v₁) →
          @Eq α (@HPow.hPow α Int α (@Lean.Grind.Field.zpow α inst) a n) (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.zpow_eq.h7.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) rfl)

-- Lean.Grind.Field.NormNum.zpow_eq, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.zpow_eq.h8.inst : Not
      (@Eq Rat
        (@HPow.hPow Rat Int Rat (@Lean.Grind.Field.zpow Rat Lean.Grind.instFieldRat)
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.zpow_eq.h8.prem0 : @Eq Bool
      (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat)
        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@HPow.hPow Rat Int Rat (@instHPow Rat Int Rat.instPowInt)
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Field.NormNum.zpow_eq.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (a : α) (n : Int) (v₁ v : Rat),
        @Eq Bool
            (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat) v
              (@HPow.hPow Rat Int Rat (@instHPow Rat Int Rat.instPowInt) v₁ n))
            Bool.true →
          @Eq α (@HPow.hPow α Int α (@Lean.Grind.Field.zpow α inst) a n) (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.zpow_eq.h8.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Field.NormNum.zpow_eq.h8.prem0)

-- Lean.Grind.AC.norm_aci, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.norm_aci.h4.inst : ¬Lean.Grind.AC.Expr.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 1) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.norm_aci.h4.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.norm_aci.h4.prem1 : Std.Commutative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Commutative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.norm_aci.h4.prem2 : ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)).toSeq.erase0.sort.beq' (Lean.Grind.AC.Seq.var 1) = Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.AC.norm_aci.h4 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} {x : Std.Commutative ctx.op}
        (e : Lean.Grind.AC.Expr) (s : Lean.Grind.AC.Seq),
        e.toSeq.erase0.sort.beq' s = Bool.true → Lean.Grind.AC.Expr.denote ctx e = Lean.Grind.AC.Seq.denote ctx s := fun hc_h => HypCheckProof.Lean.Grind.AC.norm_aci.h4.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.norm_aci.h4.prem0 HypCheckProof.Lean.Grind.AC.norm_aci.h4.prem1 ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)) (Lean.Grind.AC.Seq.var 1) HypCheckProof.Lean.Grind.AC.norm_aci.h4.prem2)

-- Lean.Grind.Order.le_eq_false_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt.h3.inst : ¬(0 ≤ 0) = False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt.h3.prem0 : 0 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.IsPreorder α] {a b : α}, a < b → (b ≤ a) = False := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt.h3.inst (@hc_h (Nat) (instLENat) ({ lt := fun (a b : Nat) => a ≤ b : LT Nat }) _ (0) (0) HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt.h3.prem0)

-- Lean.Grind.CommRing.eq_true_of_toPolyS, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPolyS.h8.inst : Not
      (@Eq Prop
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        True) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPolyS.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (bal₁ bal₂ : Bool)
        (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolySX_k bal₂ rhs) →
          @Eq Prop
            (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx rhs))
            True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPolyS.h8.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolySX_k Bool.false
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) rfl)

-- Lean.Grind.CommRing.eq_true_of_toPolyS, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPolyS.h9.inst : Not
      (@Eq Prop
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        True) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPolyS.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (bal₁ bal₂ : Bool)
        (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolySX_k bal₁ lhs) →
          @Eq Prop
            (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx rhs))
            True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_toPolyS.h9.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolySX_k Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl)

-- Lean.Grind.CommRing.PPoly.denoteG_eq_zero_of_coeff, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denoteG_eq_zero_of_coeff.h7.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.PPoly.denoteG Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (fun (a : Nat) => @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denoteG_eq_zero_of_coeff.h7.prem0 : @Eq Int
      ((fun (a : Nat) => @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@OfNat.ofNat Int (nat_lit 1)
        (@Lean.Grind.Semiring.ofNat Int
          (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (nat_lit 1))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denoteG_eq_zero_of_coeff.h7.prem1 : @LE.le Nat instLENat (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).size
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denoteG_eq_zero_of_coeff.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.Ring α] (g : Nat → α),
        @Eq α (g (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@OfNat.ofNat α (nat_lit 1) (@Lean.Grind.Semiring.ofNat α (@Lean.Grind.Ring.toSemiring α inst) (nat_lit 1))) →
          ∀ (n : Nat) (p : Lean.Grind.CommRing.PPoly),
            @LE.le Nat instLENat p.size n →
              @Eq α (@Lean.Grind.CommRing.PPoly.denoteG α inst g p)
                (@OfNat.ofNat α (nat_lit 0)
                  (@Zero.toOfNat0 α
                    (@Lean.Grind.AddCommMonoid.toZero α
                      (@Lean.Grind.NatModule.toAddCommMonoid α
                        (@Lean.Grind.Semiring.toNatModule α (@Lean.Grind.Ring.toSemiring α inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.PPoly.denoteG_eq_zero_of_coeff.h7.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (fun (a : Nat) => @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.CommRing.PPoly.denoteG_eq_zero_of_coeff.h7.prem0 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.PPoly.denoteG_eq_zero_of_coeff.h7.prem1)

-- Lean.Grind.AC.norm_ai, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.norm_ai.h3.inst : ¬Lean.Grind.AC.Expr.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 1) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.norm_ai.h3.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.norm_ai.h3.prem1 : ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)).toSeq.erase0.beq' (Lean.Grind.AC.Seq.var 1) = Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.AC.norm_ai.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} (e : Lean.Grind.AC.Expr)
        (s : Lean.Grind.AC.Seq),
        e.toSeq.erase0.beq' s = Bool.true → Lean.Grind.AC.Expr.denote ctx e = Lean.Grind.AC.Seq.denote ctx s := fun hc_h => HypCheckProof.Lean.Grind.AC.norm_ai.h3.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.norm_ai.h3.prem0 ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)) (Lean.Grind.AC.Seq.var 1) HypCheckProof.Lean.Grind.AC.norm_ai.h3.prem1)

-- Lean.Grind.Order.eq_of_le_of_le, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.eq_of_le_of_le.h2.inst : ¬0 = 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.eq_of_le_of_le.h2.prem0 : 0 % 2 ≤ 2 % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.eq_of_le_of_le.h2.prem1 : 2 % 2 ≤ 0 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.Order.eq_of_le_of_le.h2 : ¬∀ {α : Type} [inst : LE α] {a b : α}, a ≤ b → b ≤ a → a = b := fun hc_h => HypCheckProof.Lean.Grind.Order.eq_of_le_of_le.h2.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (0) (2) HypCheckProof.Lean.Grind.Order.eq_of_le_of_le.h2.prem0 HypCheckProof.Lean.Grind.Order.eq_of_le_of_le.h2.prem1)

-- Int.Internal.Linear.diseq_split_resolve, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≠
      0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h4.prem1 : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ ≠ 0 →
          ¬Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h4.prem0 HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h4.prem1)

-- Int.Internal.Linear.diseq_split_resolve, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h5.prem0 : Int.Internal.Linear.diseq_split_cert (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 1)
        (Int.Internal.Linear.Poly.num 1) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h5.prem1 : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.diseq_split_cert p₁ p₂ p₃ = Bool.true →
          ¬Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h5.prem0 HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h5.prem1)

-- Int.Internal.Linear.diseq_split_resolve, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 2) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h6.prem0 : Int.Internal.Linear.diseq_split_cert (Int.Internal.Linear.Poly.num (-1)) (Int.Internal.Linear.Poly.num 0)
        (Int.Internal.Linear.Poly.num 2) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h6.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num (-1)) ≠ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.diseq_split_cert p₁ p₂ p₃ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₁ ≠ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h6.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num (-1)) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 2) HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h6.prem0 HypCheckProof.Int.Internal.Linear.diseq_split_resolve.h6.prem1)

-- Lean.Grind.AC.Seq.denote_concat_of_endsWithVar, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_concat_of_endsWithVar.h3.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          ((Lean.Grind.AC.Seq.var 0).concat_k (Lean.Grind.AC.Seq.var 0)) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_concat_of_endsWithVar.h3.prem0 : (Lean.Grind.AC.Seq.var 0).endsWithVar_k 0 = Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_concat_of_endsWithVar.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) [inst₁ : Std.Associative ctx.op] (s : Lean.Grind.AC.Seq)
        (x : Lean.Grind.AC.Var),
        s.endsWithVar_k x = Bool.true →
          Lean.Grind.AC.Seq.denote ctx (s.concat_k (Lean.Grind.AC.Seq.var x)) = Lean.Grind.AC.Seq.denote ctx s := fun hc_h => HypCheckProof.Lean.Grind.AC.Seq.denote_concat_of_endsWithVar.h3.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) _ (Lean.Grind.AC.Seq.var 0) (0) HypCheckProof.Lean.Grind.AC.Seq.denote_concat_of_endsWithVar.h3.prem0)

-- Lean.Grind.Linarith.eq_norm, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_norm.h6.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.eq_norm.h6.prem0 : @Eq Int
      (@Lean.Grind.Linarith.Expr.denote_k Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Expr.zero)
      (@Lean.Grind.Linarith.Expr.denote_k Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Expr.zero) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.Linarith.eq_norm.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] (ctx : Lean.Grind.Linarith.Context α)
        (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @Eq α (@Lean.Grind.Linarith.Expr.denote_k α inst ctx lhs) (@Lean.Grind.Linarith.Expr.denote_k α inst ctx rhs) →
          @Eq α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.eq_norm.h6.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.eq_norm.h6.prem0)

-- Lean.Grind.Linarith.eq_norm, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_norm.h7.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.eq_norm.h7.prem0 : @Eq Bool
      (Lean.Grind.Linarith.norm_cert
        (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        Lean.Grind.Linarith.Expr.zero
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.eq_norm.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] (ctx : Lean.Grind.Linarith.Context α)
        (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.norm_cert lhs rhs p) Bool.true →
          @Eq α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.eq_norm.h7.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.eq_norm.h7.prem0)

-- Lean.Grind.CommRing.eq_norm, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm.h6.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm.h6.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs) →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_norm.h6.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.eq_norm.h6.prem0)

-- Lean.Grind.CommRing.eq_norm, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm.h7.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm.h7.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.core_cert
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.core_cert lhs rhs p) Bool.true →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_norm.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.eq_norm.h7.prem0)

-- Lean.Grind.Linarith.Poly.denoteN_insert, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.Poly.denoteN_insert.h7.inst : Not
      (@Eq Int
        (@Lean.Grind.Linarith.Poly.denoteN Int
          (@Lean.Grind.Semiring.toNatModule Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.Linarith.Poly.insert (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (Lean.Grind.Linarith.Poly.add
              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.AddCommMonoid.toAdd Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))
          (@HSMul.hSMul Nat Int Int
            (@instHSMul Nat Int
              (@Lean.Grind.NatModule.nsmul Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))
            (Int.toNat (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@Lean.Grind.Linarith.Var.denote Int
              (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.Linarith.Poly.denoteN Int
            (@Lean.Grind.Semiring.toNatModule Int
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.Linarith.Poly.add
              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.Poly.denoteN_insert.h7.prem0 : @GE.ge Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.Poly.denoteN_insert.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.NatModule α] (ctx : Lean.Grind.Linarith.Context α) (k : Int)
        (x : Lean.Grind.Linarith.Var) (p : Lean.Grind.Linarith.Poly),
        @GE.ge Int Int.instLEInt k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          @Eq α (@Lean.Grind.Linarith.Poly.denoteN α inst ctx (Lean.Grind.Linarith.Poly.insert k x p))
            (@HAdd.hAdd α α α
              (@instHAdd α (@Lean.Grind.AddCommMonoid.toAdd α (@Lean.Grind.NatModule.toAddCommMonoid α inst)))
              (@HSMul.hSMul Nat α α (@instHSMul Nat α (@Lean.Grind.NatModule.nsmul α inst)) k.toNat
                (@Lean.Grind.Linarith.Var.denote α ctx x))
              (@Lean.Grind.Linarith.Poly.denoteN α inst ctx p))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.Poly.denoteN_insert.h7.inst (@hc_h (Int) (@Lean.Grind.Semiring.toNatModule Int
      (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.Poly.denoteN_insert.h7.prem0)

-- Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_toExpr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_toExpr.h6.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k)) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_toExpr.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α)
        (a b : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Expr b p.toExpr_k →
          @Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
            (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_toExpr.h6.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl)

-- Lean.Grind.Ring.OfSemiring.of_diseq, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Ring.OfSemiring.of_diseq.h6.inst : Not
      (@Ne
        (@Lean.Grind.Ring.OfSemiring.Q Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))
        (@Lean.Grind.CommRing.Expr.denoteSAsRing Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denoteSAsRing Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  simp
theorem HypCheckProof.Lean.Grind.Ring.OfSemiring.of_diseq.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.Semiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α inst)] (ctx : Lean.Grind.CommRing.Context α)
        (lhs rhs : Lean.Grind.CommRing.Expr),
        @Ne (@Lean.Grind.Ring.OfSemiring.Q α inst) (@Lean.Grind.CommRing.Expr.denoteSAsRing α inst ctx lhs)
          (@Lean.Grind.CommRing.Expr.denoteSAsRing α inst ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.Ring.OfSemiring.of_diseq.h6.inst (@hc_h (Int) (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))

-- Int.Internal.Linear.dvd_elim, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_elim.h5.inst : ¬0 ∣
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_elim.h5.prem0 : 0 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_elim.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (k₁ : Int) (p₁ : Int.Internal.Linear.Poly) (k₂ : Int)
        (p₂ : Int.Internal.Linear.Poly),
        k₁ ∣ Int.Internal.Linear.Poly.denote' ctx p₁ → k₂ ∣ Int.Internal.Linear.Poly.denote' ctx p₂ := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_elim.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.dvd_elim.h5.prem0)

-- Lean.Grind.AC.diseq_unsat, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_unsat.h4.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_unsat.h4.prem0 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) ≠
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_unsat.h4 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (lhs rhs : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs ≠ Lean.Grind.AC.Seq.denote ctx rhs → False := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_unsat.h4.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.diseq_unsat.h4.prem0)

-- Lean.Grind.AC.diseq_unsat, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_unsat.h5.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_unsat.h5.prem0 : Lean.Grind.AC.diseq_unsat_cert (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) = Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_unsat.h5 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (lhs rhs : Lean.Grind.AC.Seq),
        Lean.Grind.AC.diseq_unsat_cert lhs rhs = Bool.true → False := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_unsat.h5.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_unsat.h5.prem0)

-- Int.Internal.Linear.diseq_norm, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_norm.h3.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_norm.h3.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≠
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_norm.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ ≠ 0 → Int.Internal.Linear.Poly.denote' ctx p₂ ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_norm.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.diseq_norm.h3.prem0)

-- Int.Internal.Linear.diseq_norm, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_norm.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_norm.h4.prem0 : (Int.Internal.Linear.Poly.num 0).norm_k.beq' (Int.Internal.Linear.Poly.num 0) = Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_norm.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        p₁.norm_k.beq' p₂ = Bool.true → Int.Internal.Linear.Poly.denote' ctx p₂ ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_norm.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.diseq_norm.h4.prem0)

-- Int.Internal.Linear.le_norm, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm.h3.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm.h3.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_norm.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_norm.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.le_norm.h3.prem0)

-- Int.Internal.Linear.le_norm, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm.h4.prem0 : (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).norm_k.beq'
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_norm.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        p₁.norm_k.beq' p₂ = Bool.true → Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_norm.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.le_norm.h4.prem0)

-- Int.Internal.Linear.diseq_norm_poly, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_norm_poly.h3.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_norm_poly.h3.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≠
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_norm_poly.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p ≠ 0 → Int.Internal.Linear.Poly.denote' ctx p' ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_norm_poly.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.diseq_norm_poly.h3.prem0)

-- Int.Internal.Linear.diseq_norm_poly, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_norm_poly.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_norm_poly.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) =
      Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Int.Internal.Linear.diseq_norm_poly.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p = Int.Internal.Linear.Poly.denote' ctx p' →
          Int.Internal.Linear.Poly.denote' ctx p' ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_norm_poly.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.diseq_norm_poly.h4.prem0)

-- Int.Internal.Linear.eq_norm_poly, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm_poly.h3.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm_poly.h3.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_norm_poly.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p = 0 → Int.Internal.Linear.Poly.denote' ctx p' = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_norm_poly.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_norm_poly.h3.prem0)

-- Int.Internal.Linear.eq_norm_poly, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm_poly.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm_poly.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Int.Internal.Linear.eq_norm_poly.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p = Int.Internal.Linear.Poly.denote' ctx p' →
          Int.Internal.Linear.Poly.denote' ctx p' = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_norm_poly.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_norm_poly.h4.prem0)

-- Int.Internal.Linear.le_neg, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_neg.h3.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_neg.h3.prem0 : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_neg.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        ¬Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_neg.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.le_neg.h3.prem0)

-- Int.Internal.Linear.le_neg, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_neg.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_neg.h4.prem0 : Int.Internal.Linear.le_neg_cert (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 1) = Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_neg.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.le_neg_cert p₁ p₂ = Bool.true → Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_neg.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.le_neg.h4.prem0)

-- Int.Internal.Linear.eq_unsat_coeff, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_unsat_coeff.h3.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_unsat_coeff.h3.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_unsat_coeff.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p : Int.Internal.Linear.Poly) (k : Int),
        Int.Internal.Linear.Poly.denote' ctx p = 0 → False := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_unsat_coeff.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (0) HypCheckProof.Int.Internal.Linear.eq_unsat_coeff.h3.prem0)

-- Int.Internal.Linear.eq_unsat_coeff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_unsat_coeff.h4.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_unsat_coeff.h4.prem0 : Int.Internal.Linear.eq_unsat_coeff_cert (Int.Internal.Linear.Poly.num 1) 2 = Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_unsat_coeff.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p : Int.Internal.Linear.Poly) (k : Int),
        Int.Internal.Linear.eq_unsat_coeff_cert p k = Bool.true → False := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_unsat_coeff.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) (2) HypCheckProof.Int.Internal.Linear.eq_unsat_coeff.h4.prem0)

-- Lean.Grind.CommRing.Poly.denote_mulMonC_nc, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulMonC_nc.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.mulMonC_nc (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            Lean.Grind.CommRing.Mon.unit
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
          (@HMul.hMul Int Int Int
            (@instHMul Int
              (@Lean.Grind.Semiring.toMul Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
            (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@Lean.Grind.CommRing.Mon.denote Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.CommRing.Mon.unit))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulMonC_nc.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (m : Lean.Grind.CommRing.Mon) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α inst ctx (Lean.Grind.CommRing.Poly.mulMonC_nc k m p c))
          (@HMul.hMul α α α (@instHMul α (@Lean.Grind.Semiring.toMul α (@Lean.Grind.Ring.toSemiring α inst)))
            (@HMul.hMul α α α (@instHMul α (@Lean.Grind.Semiring.toMul α (@Lean.Grind.Ring.toSemiring α inst)))
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst) k)
              (@Lean.Grind.CommRing.Mon.denote α (@Lean.Grind.Ring.toSemiring α inst) ctx m))
            (@Lean.Grind.CommRing.Poly.denote α inst ctx p))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulMonC_nc.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))

-- Lean.Grind.CommRing.sub_eq_of_toPolyX_k, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toPolyX_k.h7.inst : Not
      (@Eq Int
        (@HSub.hSub Int Int Int
          (@instHSub Int (@Lean.Grind.Ring.toSub Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toPolyX_k.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (lhs rhs : Lean.Grind.CommRing.Expr) (k : Int),
        @Eq α
          (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
          (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toPolyX_k.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))

-- Lean.Grind.CommRing.Poly.denote_mulMonC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulMonC.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.mulMonC (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            Lean.Grind.CommRing.Mon.unit
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
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
          (@HMul.hMul Int Int Int
            (@instHMul Int
              (@Lean.Grind.Semiring.toMul Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
            (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@Lean.Grind.CommRing.Mon.denote Int
              (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
              (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.CommRing.Mon.unit))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulMonC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (m : Lean.Grind.CommRing.Mon) (p : Lean.Grind.CommRing.Poly),
        @Eq α
          (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
            (Lean.Grind.CommRing.Poly.mulMonC k m p c))
          (@HMul.hMul α α α
            (@instHMul α
              (@Lean.Grind.Semiring.toMul α
                (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
            (@HMul.hMul α α α
              (@instHMul α
                (@Lean.Grind.Semiring.toMul α
                  (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
              (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
              (@Lean.Grind.CommRing.Mon.denote α
                (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) ctx m))
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulMonC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))

-- Lean.Grind.CommRing.Poly.denote_mergeHintC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mergeHintC.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.mergeHintC (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mergeHintC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α) (hs : List Nat)
        (a b : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α inst ctx (Lean.Grind.CommRing.Poly.mergeHintC c hs a b))
          (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst)))
            (@Lean.Grind.CommRing.Poly.denote α inst ctx a) (@Lean.Grind.CommRing.Poly.denote α inst ctx b))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_mergeHintC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@List.nil Nat) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))

-- Lean.Grind.CommRing.Poly.denote_mulC_go, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulC_go.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.mulC.go
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@HMul.hMul Int Int Int
            (@instHMul Int
              (@Lean.Grind.Semiring.toMul Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
            (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
              (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
            (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
              (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulC_go.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (p₁ p₂ acc : Lean.Grind.CommRing.Poly),
        @Eq α
          (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
            (Lean.Grind.CommRing.Poly.mulC.go p₂ c p₁ acc))
          (@HAdd.hAdd α α α
            (@instHAdd α
              (@Lean.Grind.Semiring.toAdd α
                (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx acc)
            (@HMul.hMul α α α
              (@instHMul α
                (@Lean.Grind.Semiring.toMul α
                  (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂)))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulC_go.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))

-- Lean.Grind.CommRing.PPoly.dsum_add, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.dsum_add.h4.inst : ¬Lean.Grind.CommRing.PPoly.dsum 2 (1 + 1) = Lean.Grind.CommRing.PPoly.dsum 2 1 + Lean.Grind.CommRing.PPoly.dsum 2 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.dsum_add.h4.prem0 : 1 < 2 := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.dsum_add.h4 : ¬∀ {B : Nat},
        1 < B →
          ∀ (v₁ v₂ : Nat),
            Lean.Grind.CommRing.PPoly.dsum B (v₁ + v₂) =
              Lean.Grind.CommRing.PPoly.dsum B v₁ + Lean.Grind.CommRing.PPoly.dsum B v₂ := fun hc_h => HypCheckProof.Lean.Grind.CommRing.PPoly.dsum_add.h4.inst (@hc_h (2) HypCheckProof.Lean.Grind.CommRing.PPoly.dsum_add.h4.prem0 (1) (1))

-- Int.Internal.Linear.norm_dvd_gcd_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.norm_dvd_gcd_k.h6.inst : ¬(0 ∣ Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        (0 ∣
          Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.norm_dvd_gcd_k.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (k₁ : Int) (e₁ : Int.Internal.Linear.Expr) (k₂ : Int)
        (p₂ : Int.Internal.Linear.Poly) (g : Int),
        (k₁ ∣ Int.Internal.Linear.Expr.denote_k ctx e₁) = (k₂ ∣ Int.Internal.Linear.Poly.denote' ctx p₂) := fun hc_h => HypCheckProof.Int.Internal.Linear.norm_dvd_gcd_k.h6.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Expr.num 0) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0))

-- Lean.Grind.CommRing.Poly.denote_sumGo_k, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_sumGo_k.h4.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.sumGo_k
            (fun (a a_1 : Lean.Grind.CommRing.Poly) =>
              Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (@List.nil Lean.Grind.CommRing.Poly)
            (@List.cons Lean.Grind.CommRing.Poly
              (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
              (@List.nil Lean.Grind.CommRing.Poly))))
        (@Lean.Grind.CommRing.Poly.denoteList Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@List.cons Lean.Grind.CommRing.Poly
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
            (@List.nil Lean.Grind.CommRing.Poly)))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_sumGo_k.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (f : Lean.Grind.CommRing.Poly → Lean.Grind.CommRing.Poly → Lean.Grind.CommRing.Poly)
        (fuel ps : List Lean.Grind.CommRing.Poly),
        @Eq α
          (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
            (Lean.Grind.CommRing.Poly.sumGo_k f fuel ps))
          (@Lean.Grind.CommRing.Poly.denoteList α (@Lean.Grind.CommRing.toRing α inst) ctx ps)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_sumGo_k.h4.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (fun (a a_1 : Lean.Grind.CommRing.Poly) =>
      Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@List.nil Lean.Grind.CommRing.Poly) (@List.cons Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@List.nil Lean.Grind.CommRing.Poly)))

-- Lean.Grind.CommRing.Poly.denote_powC_nc, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_powC_nc.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).powC_nc
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HPow.hPow Int Nat Int
          (@Lean.Grind.Semiring.npow Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_powC_nc.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α)
        (p : Lean.Grind.CommRing.Poly) (k : Nat),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α inst ctx (p.powC_nc k c))
          (@HPow.hPow α Nat α (@Lean.Grind.Semiring.npow α (@Lean.Grind.Ring.toSemiring α inst))
            (@Lean.Grind.CommRing.Poly.denote α inst ctx p) k)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_powC_nc.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))

-- Lean.Grind.CommRing.Poly.denote_mulBC_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulBC_k.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mulBC_k
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
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
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
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulBC_k.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (p₁.mulBC_k p₂ c))
          (@HMul.hMul α α α
            (@instHMul α
              (@Lean.Grind.Semiring.toMul α
                (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulBC_k.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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

-- Lean.Grind.Field.add_div, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.add_div.h5.inst : Not
      (@Eq Rat
        (@HAdd.hAdd Rat Rat Rat
          (@instHAdd Rat
            (@Lean.Grind.Semiring.toAdd Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat (@Lean.Grind.Field.toDiv Rat Lean.Grind.instFieldRat))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
        (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat (@Lean.Grind.Field.toDiv Rat Lean.Grind.instFieldRat))
          (@HAdd.hAdd Rat Rat Rat
            (@instHAdd Rat
              (@Lean.Grind.Semiring.toAdd Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@HMul.hMul Rat Rat Rat
              (@instHMul Rat
                (@Lean.Grind.Semiring.toMul Rat
                  (@Lean.Grind.CommSemiring.toSemiring Rat
                    (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
              (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
              (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.add_div.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] {x y z : α},
        @Eq α
          (@HAdd.hAdd α α α
            (@instHAdd α
              (@Lean.Grind.Semiring.toAdd α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
            x (@HDiv.hDiv α α α (@instHDiv α (@Lean.Grind.Field.toDiv α inst)) y z))
          (@HDiv.hDiv α α α (@instHDiv α (@Lean.Grind.Field.toDiv α inst))
            (@HAdd.hAdd α α α
              (@instHAdd α
                (@Lean.Grind.Semiring.toAdd α
                  (@Lean.Grind.CommSemiring.toSemiring α
                    (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
              (@HMul.hMul α α α
                (@instHMul α
                  (@Lean.Grind.Semiring.toMul α
                    (@Lean.Grind.CommSemiring.toSemiring α
                      (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
                x z)
              y)
            z)) := fun hc_h => HypCheckProof.Lean.Grind.Field.add_div.h5.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.CommRing.denote_of_split_cert, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.denote_of_split_cert.h5.inst : Not
      (And
        (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Eq Int
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
            (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
                (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.denote_of_split_cert.h5 : Not
      (∀ (ctx : Lean.Grind.CommRing.Context Int) {p q : Lean.Grind.CommRing.Poly} {k c : Int},
        And (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k)
          (@Eq Int (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) ctx p)
            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
              (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) k
                (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) ctx q))
              c))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.denote_of_split_cert.h5.inst (@hc_h (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Lean.Grind.CommRing.Poly.denoteS_pow_nc, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_pow_nc.h5.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.num
                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))).pow_nc
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HPow.hPow Int Nat Int
          (@Lean.Grind.Semiring.npow Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))
          (@Lean.Grind.CommRing.Poly.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num
              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_pow_nc.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α) (p : Lean.Grind.CommRing.Poly)
        (k : Nat),
        @Eq α (@Lean.Grind.CommRing.Poly.denoteS α inst ctx (p.pow_nc k))
          (@HPow.hPow α Nat α (@Lean.Grind.Semiring.npow α inst) (@Lean.Grind.CommRing.Poly.denoteS α inst ctx p) k)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_pow_nc.h5.inst (@hc_h (Int) (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))

-- Lean.Grind.CommRing.eq_normS, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_normS.h5.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_normS.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α)
        (lhs rhs : Lean.Grind.CommRing.Expr),
        @Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx lhs)
          (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_normS.h5.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))

-- Int.Internal.Linear.diseq_unsat, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_unsat.h2.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_unsat.h2.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≠
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_unsat.h2 : ¬∀ (ctx : Int.Internal.Linear.Context) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p ≠ 0 → False := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_unsat.h2.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.diseq_unsat.h2.prem0)

-- Int.Internal.Linear.diseq_unsat, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_unsat.h3.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_unsat.h3.prem0 : (Int.Internal.Linear.Poly.num 0).isUnsatDiseq_k = Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_unsat.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p : Int.Internal.Linear.Poly), p.isUnsatDiseq_k = Bool.true → False := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_unsat.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.diseq_unsat.h3.prem0)

-- Lean.Grind.CommRing.eq_normS_nc, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_normS_nc.h5.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_normS_nc.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α)
        (lhs rhs : Lean.Grind.CommRing.Expr),
        @Eq α (@Lean.Grind.CommRing.Expr.denoteS α inst ctx lhs) (@Lean.Grind.CommRing.Expr.denoteS α inst ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_normS_nc.h5.inst (@hc_h (Int) (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))

-- Lean.Grind.CommRing.Poly.denoteS_toExpr_goTerm, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_toExpr_goTerm.h5.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.toExpr.goTerm
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            Lean.Grind.CommRing.Mon.unit))
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
          (@Lean.Grind.CommRing.denoteSInt Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@Lean.Grind.CommRing.Mon.denote Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.CommRing.Mon.unit))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_toExpr_goTerm.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (m : Lean.Grind.CommRing.Mon),
        @Eq α (@Lean.Grind.CommRing.Expr.denoteS α inst ctx (Lean.Grind.CommRing.Poly.toExpr.goTerm k m))
          (@HMul.hMul α α α (@instHMul α (@Lean.Grind.Semiring.toMul α inst)) (@Lean.Grind.CommRing.denoteSInt α inst k)
            (@Lean.Grind.CommRing.Mon.denote α inst ctx m))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_toExpr_goTerm.h5.inst (@hc_h (Int) (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Mon.unit))

-- Lean.Grind.CommRing.PPoly.monDenote_kron, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.monDenote_kron.h2.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.PPoly.monDenote Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (fun (i : Nat) =>
            @HPow.hPow Int Nat Int (@instHPow Int Nat (@instPowNat Int Int.instNatPow))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) i))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HPow.hPow Int Nat Int (@instHPow Int Nat (@instPowNat Int Int.instNatPow))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.monDenote_kron.h2 : Not
      (∀ (X : Int) {B : Nat} (i v : Nat),
        @Eq Int
          (@Lean.Grind.CommRing.PPoly.monDenote Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (fun (i : Nat) =>
              @HPow.hPow Int Nat Int (@instHPow Int Nat (@instPowNat Int Int.instNatPow)) X
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) B i))
            B i v)
          (@HPow.hPow Int Nat Int (@instHPow Int Nat (@instPowNat Int Int.instNatPow)) X
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) B i) v))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.PPoly.monDenote_kron.h2.inst (@hc_h (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))

-- Int.Internal.Linear.norm_le_k, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.norm_le_k.h4.inst : ¬(Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) ≤
          Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        (Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
          0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.norm_le_k.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        (Int.Internal.Linear.Expr.denote_k ctx lhs ≤ Int.Internal.Linear.Expr.denote_k ctx rhs) =
          (Int.Internal.Linear.Poly.denote' ctx p ≤ 0) := fun hc_h => HypCheckProof.Int.Internal.Linear.norm_le_k.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)))

-- Lean.Grind.AC.Seq.denote_concat, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_concat.h2.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          ((Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)).concat (Lean.Grind.AC.Seq.var 0)) =
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b :
              Lean.Grind.AC.Context Nat }.op
          (Lean.Grind.AC.Seq.denote
            { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b :
              Lean.Grind.AC.Context Nat }
            (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)))
          (Lean.Grind.AC.Seq.denote
            { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b :
              Lean.Grind.AC.Context Nat }
            (Lean.Grind.AC.Seq.var 0)) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_concat.h2 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (s₁ s₂ : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx (s₁.concat s₂) =
          ctx.op (Lean.Grind.AC.Seq.denote ctx s₁) (Lean.Grind.AC.Seq.denote ctx s₂) := fun hc_h => HypCheckProof.Lean.Grind.AC.Seq.denote_concat.h2.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0))

-- Lean.Grind.IsCharP.intCast_eq_zero_iff, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.IsCharP.intCast_eq_zero_iff.h3.inst : Not
      (Iff
        (@Eq Int
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Int (nat_lit 0)
            (@Zero.toOfNat0 Int
              (@Lean.Grind.AddCommMonoid.toZero Int
                (@Lean.Grind.NatModule.toAddCommMonoid Int
                  (@Lean.Grind.Semiring.toNatModule Int
                    (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))))
        (@Eq Int
          (@HMod.hMod Int Int Int (@instHMod Int Int.instMod) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.IsCharP.intCast_eq_zero_iff.h3 : Not
      (∀ (p : Nat) {α : Type} [inst : Lean.Grind.Ring α] (x : Int),
        Iff
          (@Eq α (@Int.cast α (@Lean.Grind.Ring.intCast α inst) x)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α (@Lean.Grind.Ring.toSemiring α inst)))))))
          (@Eq Int (@HMod.hMod Int Int Int (@instHMod Int Int.instMod) x (@Nat.cast Int instNatCastInt p))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := fun hc_h => HypCheckProof.Lean.Grind.IsCharP.intCast_eq_zero_iff.h3.inst (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))

-- Lean.Grind.Ring.intCast_nat_sub, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Ring.intCast_nat_sub.h4.inst : Not
      (@Eq Int
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Nat.cast Int instNatCastInt
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@HSub.hSub Int Int Int
          (@instHSub Int (@Lean.Grind.Ring.toSub Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@Nat.cast Int
            (@Lean.Grind.Semiring.natCast Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Nat.cast Int
            (@Lean.Grind.Semiring.natCast Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Ring.intCast_nat_sub.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Ring α] {x y : Nat},
        @Eq α
          (@Int.cast α (@Lean.Grind.Ring.intCast α inst)
            (@Nat.cast Int instNatCastInt (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) x y)))
          (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α inst))
            (@Nat.cast α (@Lean.Grind.Semiring.natCast α (@Lean.Grind.Ring.toSemiring α inst)) x)
            (@Nat.cast α (@Lean.Grind.Semiring.natCast α (@Lean.Grind.Ring.toSemiring α inst)) y))) := fun hc_h => HypCheckProof.Lean.Grind.Ring.intCast_nat_sub.h4.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))

-- Lean.Grind.Ring.ofNat_sub, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Ring.ofNat_sub.h4.inst : Not
      (@Eq Int
        (@OfNat.ofNat Int
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Lean.Grind.Semiring.ofNat Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@HSub.hSub Int Int Int
          (@instHSub Int (@Lean.Grind.Ring.toSub Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@OfNat.ofNat Int (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Lean.Grind.Semiring.ofNat Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@OfNat.ofNat Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Lean.Grind.Semiring.ofNat Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Ring.ofNat_sub.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Ring α] {x y : Nat},
        @Eq α
          (@OfNat.ofNat α (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) x y)
            (@Lean.Grind.Semiring.ofNat α (@Lean.Grind.Ring.toSemiring α inst)
              (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) x y)))
          (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α inst))
            (@OfNat.ofNat α x (@Lean.Grind.Semiring.ofNat α (@Lean.Grind.Ring.toSemiring α inst) x))
            (@OfNat.ofNat α y (@Lean.Grind.Semiring.ofNat α (@Lean.Grind.Ring.toSemiring α inst) y)))) := fun hc_h => HypCheckProof.Lean.Grind.Ring.ofNat_sub.h4.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))

-- Int.Internal.Linear.norm_eq_k, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.norm_eq_k.h4.inst : ¬(Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
          Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        (Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
          0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.norm_eq_k.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        (Int.Internal.Linear.Expr.denote_k ctx lhs = Int.Internal.Linear.Expr.denote_k ctx rhs) =
          (Int.Internal.Linear.Poly.denote' ctx p = 0) := fun hc_h => HypCheckProof.Int.Internal.Linear.norm_eq_k.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)))

-- Lean.Grind.Field.div_mul_cancel, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.div_mul_cancel.h4.inst : Not
      (@Eq Rat
        (@HMul.hMul Rat Rat Rat
          (@instHMul Rat
            (@Lean.Grind.Semiring.toMul Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat (@Lean.Grind.Field.toDiv Rat Lean.Grind.instFieldRat))
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
        (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.div_mul_cancel.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] {x y : α},
        @Eq α
          (@HMul.hMul α α α
            (@instHMul α
              (@Lean.Grind.Semiring.toMul α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
            (@HDiv.hDiv α α α (@instHDiv α (@Lean.Grind.Field.toDiv α inst)) x y) y)
          x) := fun hc_h => HypCheckProof.Lean.Grind.Field.div_mul_cancel.h4.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.Field.of_mul_eq_zero, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.of_mul_eq_zero.h4.inst : Not
      (Or
        (@Eq Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@OfNat.ofNat Rat (nat_lit 0)
            (@Zero.toOfNat0 Rat
              (@Lean.Grind.AddCommMonoid.toZero Rat
                (@Lean.Grind.NatModule.toAddCommMonoid Rat
                  (@Lean.Grind.Semiring.toNatModule Rat
                    (@Lean.Grind.CommSemiring.toSemiring Rat
                      (@Lean.Grind.CommRing.toCommSemiring Rat
                        (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))))))
        (@Eq Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@OfNat.ofNat Rat (nat_lit 0)
            (@Zero.toOfNat0 Rat
              (@Lean.Grind.AddCommMonoid.toZero Rat
                (@Lean.Grind.NatModule.toAddCommMonoid Rat
                  (@Lean.Grind.Semiring.toNatModule Rat
                    (@Lean.Grind.CommSemiring.toSemiring Rat
                      (@Lean.Grind.CommRing.toCommSemiring Rat
                        (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Field.of_mul_eq_zero.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] {a b : α},
        Or
          (@Eq α a
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α
                        (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))))))
          (@Eq α b
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α
                        (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))))))) := fun hc_h => HypCheckProof.Lean.Grind.Field.of_mul_eq_zero.h4.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))

-- Lean.Grind.CommRing.eq_int_module, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_int_module.h4.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denoteAsIntModule Int Lean.Grind.instCommRingInt
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_int_module.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Poly.denoteAsIntModule α inst ctx p)
          (@OfNat.ofNat α (nat_lit 0)
            (@Zero.toOfNat0 α
              (@Lean.Grind.AddCommMonoid.toZero α
                (@Lean.Grind.NatModule.toAddCommMonoid α
                  (@Lean.Grind.Semiring.toNatModule α
                    (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_int_module.h4.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))

-- Lean.Grind.Field.zpow_add_one, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.zpow_add_one.h3.inst : Not
      (@Eq Rat
        (@HPow.hPow Rat Int Rat (@Lean.Grind.Field.zpow Rat Lean.Grind.instFieldRat)
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@HMul.hMul Rat Rat Rat
          (@instHMul Rat
            (@Lean.Grind.Semiring.toMul Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@HPow.hPow Rat Int Rat (@Lean.Grind.Field.zpow Rat Lean.Grind.instFieldRat)
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.zpow_add_one.h3 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] {a : α} (n : Int),
        @Eq α
          (@HPow.hPow α Int α (@Lean.Grind.Field.zpow α inst) a
            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) n (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@HMul.hMul α α α
            (@instHMul α
              (@Lean.Grind.Semiring.toMul α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
            (@HPow.hPow α Int α (@Lean.Grind.Field.zpow α inst) a n) a)) := fun hc_h => HypCheckProof.Lean.Grind.Field.zpow_add_one.h3.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))

-- Lean.Grind.CommRing.Poly.eq_of_isMon_k, hypothesis 1: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.eq_of_isMon_k.h1.inst : ¬∃ (k : Int),
        ∃ (m : Lean.Grind.CommRing.Mon),
          Lean.Grind.CommRing.Poly.num 0 = Lean.Grind.CommRing.Poly.add k m (Lean.Grind.CommRing.Poly.num 0) := by
  simp
theorem HypCheckProof.Lean.Grind.CommRing.Poly.eq_of_isMon_k.h1 : ¬∀ {p : Lean.Grind.CommRing.Poly},
        ∃ (k : Int), ∃ (m : Lean.Grind.CommRing.Mon), p = Lean.Grind.CommRing.Poly.add k m (Lean.Grind.CommRing.Poly.num 0) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.eq_of_isMon_k.h1.inst (@hc_h (Lean.Grind.CommRing.Poly.num 0))

-- Lean.Grind.CommRing.PPoly.isMon_k_eq, hypothesis 1: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.isMon_k_eq.h1.inst : ¬∃ (k : Int),
        ∃ (d : Nat),
          ∃ (v : Nat),
            Lean.Grind.CommRing.PPoly.num 0 = Lean.Grind.CommRing.PPoly.add k d v (Lean.Grind.CommRing.PPoly.num 0) := by
  simp
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.isMon_k_eq.h1 : ¬∀ (p : Lean.Grind.CommRing.PPoly),
        ∃ (k : Int), ∃ (d : Nat), ∃ (v : Nat), p = Lean.Grind.CommRing.PPoly.add k d v (Lean.Grind.CommRing.PPoly.num 0) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.PPoly.isMon_k_eq.h1.inst (@hc_h (Lean.Grind.CommRing.PPoly.num 0))

-- Lean.Grind.CommRing.Expr.of_linS_k, hypothesis 1: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.of_linS_k.h1.inst : ¬((Lean.Grind.CommRing.Expr.var 0).neg.semi_k = Bool.true ∧
        (Lean.Grind.CommRing.Expr.var 0).neg.lin_k ≤ (Lean.Grind.CommRing.Expr.var 0).neg.linS_k) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.of_linS_k.h1 : ¬∀ (e : Lean.Grind.CommRing.Expr), e.semi_k = Bool.true ∧ e.lin_k ≤ e.linS_k := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.of_linS_k.h1.inst (@hc_h ((Lean.Grind.CommRing.Expr.var 0).neg))

