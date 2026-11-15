import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.CommRing.le_of_kronQLin_rel, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h14.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h14.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h14.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h14.prem2 : @Eq Bool
      (Lean.Grind.CommRing.Expr.linQOk_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h14.prem3 : @Eq Bool
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
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h14.prem4 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQLinEq_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h14 : Not
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
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (invs : Lean.Grind.CommRing.InvVars),
        @Lean.Grind.CommRing.InvVars.ok α inst ctx invs →
          @Eq Bool invs.nonzero_k Bool.true →
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
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h14.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (Rat.instLE) (Rat.instLT) _ _ _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h14.prem0 HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h14.prem1 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h14.prem2 HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h14.prem3 HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h14.prem4)

-- Lean.Grind.CommRing.le_of_kronQLin_rel, hypothesis 20: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h20.inst : Not
      (@Eq Prop
        (@LE.le Rat Rat.instLE
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LE.le Rat Rat.instLE
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h20.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h20.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h20.prem2 : @Eq Bool
      (Nat.blt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h20.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.linQOk_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h20.prem4 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQLinEq_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h20 : Not
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
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (invs : Lean.Grind.CommRing.InvVars),
        @Lean.Grind.CommRing.InvVars.ok α inst ctx invs →
          @Eq Bool invs.nonzero_k Bool.true →
            ∀ (d : Nat),
              @Eq Bool (Nat.blt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d) Bool.true →
                ∀ (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
                  @Eq Bool
                      (Lean.Grind.CommRing.Expr.linQOk_k invs
                        ((lhs.sub rhs).mul (Lean.Grind.CommRing.Expr.num (@Nat.cast Int instNatCastInt d))) (lhs'.sub rhs'))
                      Bool.true →
                    @Eq Bool
                        (Lean.Grind.CommRing.Expr.kronQLinEq_k K invs
                          ((lhs.sub rhs).mul (Lean.Grind.CommRing.Expr.num (@Nat.cast Int instNatCastInt d)))
                          (lhs'.sub rhs'))
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
                            (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h20.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (Rat.instLE) (Rat.instLT) _ _ _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h20.prem0 HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h20.prem1 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h20.prem2 (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h20.prem3 HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h20.prem4)

-- Lean.Grind.CommRing.le_of_kronQLin_rel, hypothesis 21: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h21.inst : Not
      (@Eq Prop
        (@LE.le Rat Rat.instLE
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LE.le Rat Rat.instLE
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h21.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h21.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h21.prem2 : @Eq Bool
      (Nat.blt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h21.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.linQOk_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h21.prem4 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h21 : Not
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
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (invs : Lean.Grind.CommRing.InvVars),
        @Lean.Grind.CommRing.InvVars.ok α inst ctx invs →
          @Eq Bool invs.nonzero_k Bool.true →
            ∀ (d : Nat),
              @Eq Bool (Nat.blt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d) Bool.true →
                ∀ (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
                  @Eq Bool
                      (Lean.Grind.CommRing.Expr.linQOk_k invs
                        ((lhs.sub rhs).mul (Lean.Grind.CommRing.Expr.num (@Nat.cast Int instNatCastInt d))) (lhs'.sub rhs'))
                      Bool.true →
                    @Eq Bool
                        (Lean.Grind.CommRing.Expr.kronQOk_k K invs
                          ((lhs.sub rhs).mul (Lean.Grind.CommRing.Expr.num (@Nat.cast Int instNatCastInt d)))
                          (lhs'.sub rhs'))
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
                            (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h21.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (Rat.instLE) (Rat.instLT) _ _ _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h21.prem0 HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h21.prem1 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h21.prem2 (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h21.prem3 HypCheckProof.Lean.Grind.CommRing.le_of_kronQLin_rel.h21.prem4)

-- Lean.Grind.CommRing.le_cancel_of_kronLinS, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h15.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h15.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h15.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h15.prem2 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h15.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h15.prem4 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h15 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.IsPreorder α inst_2]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α inst) inst_2 inst_3 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b a' b' c : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k (a'.add c)) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K a) (Lean.Grind.CommRing.Expr.kronLinEval_k K (a'.add c)) →
            @Eq Bool (b.linSOk_k (b'.add c)) Bool.true →
              @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K b (b'.add c)) Bool.true →
                @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K b) (Lean.Grind.CommRing.Expr.kronLinEval_k K (b'.add c)) →
                  @Eq Prop
                    (@LE.le α inst_2
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
                    (@LE.le α inst_2
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a')
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h15.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h15.prem0 HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h15.prem1 HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h15.prem2 HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h15.prem3 HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h15.prem4)

-- Lean.Grind.CommRing.le_cancel_of_kronLinS, hypothesis 16: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h16.inst : Not
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
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h16.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h16.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h16.prem2 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h16.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h16.prem4 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h16 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.IsPreorder α inst_2]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α inst) inst_2 inst_3 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b a' b' c : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k (a'.add c)) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a (a'.add c)) Bool.true →
            @Eq Bool (b.linSOk_k (b'.add c)) Bool.true →
              @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K b (b'.add c)) Bool.true →
                @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K b) (Lean.Grind.CommRing.Expr.kronLinEval_k K (b'.add c)) →
                  @Eq Prop
                    (@LE.le α inst_2
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
                    (@LE.le α inst_2
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a')
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h16.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h16.prem0 HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h16.prem1 HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h16.prem2 HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h16.prem3 HypCheckProof.Lean.Grind.CommRing.le_cancel_of_kronLinS.h16.prem4)

-- Lean.Grind.CommRing.eq_cancel_of_kronS, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronS.h13.inst : Not
      (@Eq Prop
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronS.h13.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronS.h13.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronS.h13.prem2 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronS.h13.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronS.h13.prem4 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronS.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b a' b' c : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a (a'.add c)) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a (a'.add c)) Bool.true →
            @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B b (b'.add c)) Bool.true →
              @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K b (b'.add c)) Bool.true →
                @Eq Int (Lean.Grind.CommRing.Expr.kronEval_k K B b) (Lean.Grind.CommRing.Expr.kronEval_k K B (b'.add c)) →
                  @Eq Prop
                    (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
                    (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a')
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronS.h13.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronS.h13.prem0 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronS.h13.prem1 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronS.h13.prem2 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronS.h13.prem3 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronS.h13.prem4)

-- Lean.Grind.CommRing.lt_of_kronLin_rel, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronLin_rel.h14.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronLin_rel.h14.prem0 : @Eq Bool
      (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).linOk_k
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronLin_rel.h14.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronLin_rel.h14 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
        [inst_5 : @Std.LawfulOrderLT α inst_2 inst_1] (ctx : Lean.Grind.CommRing.Context α) (K : Nat)
        (l r l' r' : Lean.Grind.CommRing.Expr),
        @Eq Bool ((l.sub r).linOk_k (l'.sub r')) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K (l.sub r))
              (Lean.Grind.CommRing.Expr.kronLinEval_k K (l'.sub r')) →
            @Eq Prop
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r))
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l')
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_of_kronLin_rel.h14.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.lt_of_kronLin_rel.h14.prem0 HypCheckProof.Lean.Grind.CommRing.lt_of_kronLin_rel.h14.prem1)

-- Lean.Grind.CommRing.lt_of_kronLin_rel, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronLin_rel.h15.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronLin_rel.h15.prem0 : @Eq Bool
      (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).linOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronLin_rel.h15.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronLin_rel.h15 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
        [inst_5 : @Std.LawfulOrderLT α inst_2 inst_1] (ctx : Lean.Grind.CommRing.Context α) (K : Nat)
        (l r l' r' : Lean.Grind.CommRing.Expr),
        @Eq Bool ((l.sub r).linOk_k (l'.sub r')) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K (l.sub r) (l'.sub r')) Bool.true →
            @Eq Prop
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r))
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l')
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_of_kronLin_rel.h15.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_of_kronLin_rel.h15.prem0 HypCheckProof.Lean.Grind.CommRing.lt_of_kronLin_rel.h15.prem1)

-- Lean.Grind.CommRing.le_of_kron_rel, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kron_rel.h15.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kron_rel.h15.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kron_rel.h15.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kron_rel.h15 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (l r l' r' : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B (l.sub r) (l'.sub r')) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K (l.sub r) (l'.sub r')) Bool.true →
            @Eq Prop
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r))
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l')
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_of_kron_rel.h15.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_of_kron_rel.h15.prem0 HypCheckProof.Lean.Grind.CommRing.le_of_kron_rel.h15.prem1)

-- Lean.Grind.CommRing.le_of_kronLin_rel, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronLin_rel.h13.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronLin_rel.h13.prem0 : @Eq Bool
      (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).linOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronLin_rel.h13.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronLin_rel.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (l r l' r' : Lean.Grind.CommRing.Expr),
        @Eq Bool ((l.sub r).linOk_k (l'.sub r')) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K (l.sub r))
              (Lean.Grind.CommRing.Expr.kronLinEval_k K (l'.sub r')) →
            @Eq Prop
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r))
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l')
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_of_kronLin_rel.h13.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_of_kronLin_rel.h13.prem0 HypCheckProof.Lean.Grind.CommRing.le_of_kronLin_rel.h13.prem1)

-- Lean.Grind.CommRing.le_of_kronLin_rel, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronLin_rel.h14.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronLin_rel.h14.prem0 : @Eq Bool
      (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).linOk_k
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronLin_rel.h14.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_of_kronLin_rel.h14 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (l r l' r' : Lean.Grind.CommRing.Expr),
        @Eq Bool ((l.sub r).linOk_k (l'.sub r')) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K (l.sub r) (l'.sub r')) Bool.true →
            @Eq Prop
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r))
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l')
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_of_kronLin_rel.h14.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_of_kronLin_rel.h14.prem0 HypCheckProof.Lean.Grind.CommRing.le_of_kronLin_rel.h14.prem1)

-- Lean.Grind.CommRing.eq_true_of_kronQ, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h12.inst : Not
      (@Eq Prop
        (@Eq Rat
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h12.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h12.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h12.prem2 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degQOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h12.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQEq_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (invs : Lean.Grind.CommRing.InvVars),
        @Lean.Grind.CommRing.InvVars.ok α inst ctx invs →
          @Eq Bool invs.nonzero_k Bool.true →
            ∀ (a b : Lean.Grind.CommRing.Expr),
              @Eq Bool (Lean.Grind.CommRing.Expr.degQOk_k B invs a b) Bool.true →
                @Eq Bool (Lean.Grind.CommRing.Expr.kronQEq_k K B invs a b) Bool.true →
                  @Eq Prop
                    (@Eq α
                      (@Lean.Grind.CommRing.Expr.denote α
                        (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx a)
                      (@Lean.Grind.CommRing.Expr.denote α
                        (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx b))
                    True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h12.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h12.prem0 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h12.prem1 (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h12.prem2 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h12.prem3)

-- Lean.Grind.CommRing.eq_true_of_kronQ, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h13.inst : Not
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
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h13.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h13.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h13.prem2 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degQOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h13.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (invs : Lean.Grind.CommRing.InvVars),
        @Lean.Grind.CommRing.InvVars.ok α inst ctx invs →
          @Eq Bool invs.nonzero_k Bool.true →
            ∀ (a b : Lean.Grind.CommRing.Expr),
              @Eq Bool (Lean.Grind.CommRing.Expr.degQOk_k B invs a b) Bool.true →
                @Eq Bool (Lean.Grind.CommRing.Expr.kronQOk_k K invs a b) Bool.true →
                  @Eq Prop
                    (@Eq α
                      (@Lean.Grind.CommRing.Expr.denote α
                        (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx a)
                      (@Lean.Grind.CommRing.Expr.denote α
                        (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx b))
                    True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h13.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h13.prem0 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h13.prem1 (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h13.prem2 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQ.h13.prem3)

-- Lean.Grind.CommRing.lt_norm, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm.h6.inst : Not
      (@LT.lt UInt8 instLTUInt8
        (@Lean.Grind.CommRing.Poly.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
          (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        (@OfNat.ofNat UInt8 (nat_lit 0)
          (@Zero.toOfNat0 UInt8
            (@Lean.Grind.AddCommMonoid.toZero UInt8
              (@Lean.Grind.NatModule.toAddCommMonoid UInt8
                (@Lean.Grind.Semiring.toNatModule UInt8
                  (@Lean.Grind.CommSemiring.toSemiring UInt8
                    (@Lean.Grind.CommRing.toCommSemiring UInt8 Lean.Grind.instCommRingUInt8)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm.h6.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.core_cert
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm.h6.prem1 : @LT.lt UInt8 instLTUInt8
      (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
        (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
        (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.core_cert lhs rhs p) Bool.true →
          @LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs) →
            @LT.lt α inst_2 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm.h6.inst (@hc_h (UInt8) (Lean.Grind.instCommRingUInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) HypCheckProof.Lean.Grind.CommRing.lt_norm.h6.prem0 HypCheckProof.Lean.Grind.CommRing.lt_norm.h6.prem1)

-- Lean.Grind.CommRing.lt_norm, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm.h11.prem0 : @LT.lt Int Int.instLTInt
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs) →
          @LT.lt α inst_2 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_norm.h11.prem0)

-- Lean.Grind.CommRing.lt_norm, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm.h12.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.core_cert
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.core_cert lhs rhs p) Bool.true →
          @LT.lt α inst_2 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_norm.h12.prem0)

-- Lean.Grind.Order.lt_eq_false_of_le_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h6.inst : Not
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
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h6.prem0 : @Eq Bool
      ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).ble'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h6.prem1 : @LE.le UInt8 instLEUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α] (a b : α) (k₁ k₂ : Int),
        @Eq Bool
            ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁).ble'
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
          @LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
            @Eq Prop
              (@LT.lt α inst_1 b
                (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
                  (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
              False) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h6.inst (@hc_h (UInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h6.prem0 HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h6.prem1)

-- Lean.Grind.Order.lt_eq_false_of_le_k, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h11.inst : Not
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
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h11.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h11 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] (a b : α)
        (k₁ k₂ : Int),
        @LE.le α inst a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @Eq Prop
            (@LT.lt α inst_1 b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
            False) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h11.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h11.prem0)

-- Lean.Grind.Order.lt_eq_false_of_le_k, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h12.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@HAdd.hAdd Int Int Int
            (@instHAdd Int
              (@Lean.Grind.Semiring.toAdd Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        False) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h12.prem0 : @Eq Bool
      ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).ble'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h12 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] (a b : α)
        (k₁ k₂ : Int),
        @Eq Bool
            ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁).ble'
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
          @Eq Prop
            (@LT.lt α inst_1 b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
            False) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h12.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h12.prem0)

-- Lean.Grind.Order.lt_eq_false_of_lt_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h6.inst : Not
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
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h6.prem0 : @Eq Bool
      ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).ble'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h6.prem1 : @LT.lt UInt8 instLTUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst : @Std.IsPreorder α inst] [inst : Lean.Grind.Ring α] (a b : α) (k₁ k₂ : Int),
        @Eq Bool
            ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁).ble'
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
          @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst) k₁)) →
            @Eq Prop
              (@LT.lt α inst_1 b
                (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst))) a
                  (@Int.cast α (@Lean.Grind.Ring.intCast α inst) k₂)))
              False) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h6.inst (@hc_h (UInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h6.prem0 HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h6.prem1)

-- Lean.Grind.Order.lt_eq_false_of_lt_k, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h11.inst : Not
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
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h11.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h11 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] (a b : α)
        (k₁ k₂ : Int),
        @LT.lt α inst_1 a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @Eq Prop
            (@LT.lt α inst_1 b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
            False) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h11.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h11.prem0)

-- Lean.Grind.Order.lt_eq_false_of_lt_k, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h12.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@HAdd.hAdd Int Int Int
            (@instHAdd Int
              (@Lean.Grind.Semiring.toAdd Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        False) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h12.prem0 : @Eq Bool
      ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).ble'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h12 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] (a b : α)
        (k₁ k₂ : Int),
        @Eq Bool
            ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁).ble'
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
          @Eq Prop
            (@LT.lt α inst_1 b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
            False) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h12.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h12.prem0)

-- Lean.Grind.Linarith.lt_norm, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_norm.h6.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.lt_norm.h6.prem0 : @Eq Bool
      (Lean.Grind.Linarith.norm_cert Lean.Grind.Linarith.Expr.zero
        (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_norm.h6.prem1 : @LT.lt UInt8 instLTUInt8
      (@Lean.Grind.Linarith.Expr.denote_k UInt8
        (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
        (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
        Lean.Grind.Linarith.Expr.zero)
      (@Lean.Grind.Linarith.Expr.denote_k UInt8
        (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
        (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
        (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.lt_norm.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.Linarith.Context α) (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.norm_cert lhs rhs p) Bool.true →
          @LT.lt α inst_2 (@Lean.Grind.Linarith.Expr.denote_k α inst ctx lhs)
              (@Lean.Grind.Linarith.Expr.denote_k α inst ctx rhs) →
            @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.lt_norm.h6.inst (@hc_h (UInt8) (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)) (instLEUInt8) (instLTUInt8) _ _ (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.lt_norm.h6.prem0 HypCheckProof.Lean.Grind.Linarith.lt_norm.h6.prem1)

-- Lean.Grind.Linarith.lt_norm, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_norm.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.lt_norm.h11.prem0 : @LT.lt Int Int.instLTInt
      (@Lean.Grind.Linarith.Expr.denote_k Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Expr.zero)
      (@Lean.Grind.Linarith.Expr.denote_k Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.lt_norm.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 inst_4]
        (ctx : Lean.Grind.Linarith.Context α) (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @LT.lt α inst_2 (@Lean.Grind.Linarith.Expr.denote_k α inst ctx lhs)
            (@Lean.Grind.Linarith.Expr.denote_k α inst ctx rhs) →
          @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.lt_norm.h11.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.lt_norm.h11.prem0)

-- Lean.Grind.Linarith.lt_norm, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_norm.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.lt_norm.h12.prem0 : @Eq Bool
      (Lean.Grind.Linarith.norm_cert Lean.Grind.Linarith.Expr.zero Lean.Grind.Linarith.Expr.zero
        Lean.Grind.Linarith.Poly.nil)
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.lt_norm.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 inst_4]
        (ctx : Lean.Grind.Linarith.Context α) (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.norm_cert lhs rhs p) Bool.true →
          @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.lt_norm.h12.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.lt_norm.h12.prem0)

-- Lean.Grind.Linarith.not_le_norm, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.not_le_norm.h6.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.not_le_norm.h6.prem0 : @Eq Bool
      (Lean.Grind.Linarith.norm_cert Lean.Grind.Linarith.Expr.zero
        (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.not_le_norm.h6.prem1 : Not
      (@LE.le UInt8 instLEUInt8
        (@Lean.Grind.Linarith.Expr.denote_k UInt8
          (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
          (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Lean.Grind.Linarith.Expr.denote_k UInt8
          (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
          Lean.Grind.Linarith.Expr.zero)) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.not_le_norm.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsLinearOrder α inst_1]
        (ctx : Lean.Grind.Linarith.Context α) (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.norm_cert rhs lhs p) Bool.true →
          Not
              (@LE.le α inst_1 (@Lean.Grind.Linarith.Expr.denote_k α inst ctx lhs)
                (@Lean.Grind.Linarith.Expr.denote_k α inst ctx rhs)) →
            @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.not_le_norm.h6.inst (@hc_h (UInt8) (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)) (instLEUInt8) (instLTUInt8) _ _ (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.not_le_norm.h6.prem0 HypCheckProof.Lean.Grind.Linarith.not_le_norm.h6.prem1)

-- Lean.Grind.Linarith.not_le_norm, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.not_le_norm.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.not_le_norm.h11.prem0 : Not
      (@LE.le Int Int.instLEInt
        (@Lean.Grind.Linarith.Expr.denote_k Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Lean.Grind.Linarith.Expr.denote_k Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Expr.zero)) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.not_le_norm.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsLinearOrder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 (@Std.IsLinearPreorder.toIsPreorder α inst_1 (@Std.IsLinearOrder.toIsLinearPreorder α inst_1 inst_4))]
        (ctx : Lean.Grind.Linarith.Context α) (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        Not
            (@LE.le α inst_1 (@Lean.Grind.Linarith.Expr.denote_k α inst ctx lhs)
              (@Lean.Grind.Linarith.Expr.denote_k α inst ctx rhs)) →
          @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.not_le_norm.h11.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.not_le_norm.h11.prem0)

-- Lean.Grind.Linarith.not_le_norm, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.not_le_norm.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.not_le_norm.h12.prem0 : @Eq Bool
      (Lean.Grind.Linarith.norm_cert Lean.Grind.Linarith.Expr.zero Lean.Grind.Linarith.Expr.zero
        Lean.Grind.Linarith.Poly.nil)
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.not_le_norm.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsLinearOrder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 (@Std.IsLinearPreorder.toIsPreorder α inst_1 (@Std.IsLinearOrder.toIsLinearPreorder α inst_1 inst_4))]
        (ctx : Lean.Grind.Linarith.Context α) (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.norm_cert rhs lhs p) Bool.true →
          @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.not_le_norm.h12.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.not_le_norm.h12.prem0)

-- Lean.Grind.CommRing.Stepwise.simpsP, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsP.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsP.h11.prem0 : @Eq Bool
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsP.h11.prem1 : @Eq Lean.Grind.CommRing.PPoly
      (Lean.Grind.CommRing.Poly.toPP_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      (Lean.Grind.CommRing.PPoly.combineN_k (fun (k : Int) => k)
        (Lean.Grind.CommRing.Poly.toPP_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (Lean.Grind.CommRing.PSumTree.eval_k (fun (k : Int) => k) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (Lean.Grind.CommRing.PSumTree.leaf (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsP.h11.prem2 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsP.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (B : Nat)
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
                (Lean.Grind.CommRing.PPoly.combineN_k (fun (k : Int) => k) (Lean.Grind.CommRing.Poly.toPP_k B p₁)
                  (Lean.Grind.CommRing.PSumTree.eval_k (fun (k : Int) => k) B t)) →
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
                            (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsP.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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
      (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsP.h11.prem0 rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsP.h11.prem1 HypCheckProof.Lean.Grind.CommRing.Stepwise.simpsP.h11.prem2)

-- Lean.Grind.CommRing.lt_true_of_poly, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_true_of_poly.h12.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        True) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_true_of_poly.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs : Lean.Grind.CommRing.Expr) (n : Nat),
        @Eq Prop
          (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
          True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_true_of_poly.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))

-- Lean.Grind.CommRing.Stepwise.imp_keqC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h3.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.imp_keq_certC
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h3.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        [inst_1 :
          @Lean.Grind.NoNatZeroDivisors α
            (@Lean.Grind.Semiring.toNatModule α
              (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))]
        (k : Int) (lhs rhs : Lean.Grind.CommRing.Expr) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.imp_keq_certC lhs rhs k p₁ p₂ c) Bool.true →
          @Eq α
              (@HMul.hMul α α α
                (@instHMul α
                  (@Lean.Grind.Semiring.toMul α
                    (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h3.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h3.prem1)

-- Lean.Grind.CommRing.Stepwise.imp_keqC, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h11.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h11.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h11 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α)
        [inst_2 :
          @Lean.Grind.NoNatZeroDivisors α
            (@Lean.Grind.Semiring.toNatModule α
              (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))]
        (k : Int) (lhs rhs : Lean.Grind.CommRing.Expr) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq α
            (@HMul.hMul α α α
              (@instHMul α
                (@Lean.Grind.Semiring.toMul α
                  (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
              (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁))
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h11.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h11.prem0)

-- Lean.Grind.CommRing.Stepwise.imp_keqC, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h12.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h12.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.imp_keq_certC
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h12 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α)
        [inst_2 :
          @Lean.Grind.NoNatZeroDivisors α
            (@Lean.Grind.Semiring.toNatModule α
              (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))]
        (k : Int) (lhs rhs : Lean.Grind.CommRing.Expr) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.imp_keq_certC lhs rhs k p₁ p₂ c) Bool.true →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h12.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keqC.h12.prem0)

-- Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS.h11.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.PPoly),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b) →
            @Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS.h11.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Bool.false
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS.h11.prem0 rfl)

-- Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS.h12.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.PPoly),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a) →
            @Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS.h12.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eqS.h12.prem0 rfl)

-- Lean.Grind.OrderedRing.mul_lt_mul_of_neg_left, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_left.h10.inst : ¬-1 * 0 < -1 * 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_left.h10.prem0 : -1 < 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_left.h10 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Lean.Grind.OrderedRing R] [inst_5 : Std.LawfulOrderLT R] {a b c : R}, c < 0 → c * b < c * a := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_left.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt.toRing) (Int.instLEInt) (Int.instLTInt) _ _ _ (0) (0) (-1) HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_left.h10.prem0)

-- Lean.Grind.OrderedRing.mul_lt_mul_of_neg_left, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_left.h11.inst : Not
      (@LT.lt Int Int.instLTInt
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_left.h11.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_left.h11 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.IsPartialOrder R inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2
            (@Std.IsPartialOrder.toIsPreorder R inst_1 inst_3)]
        [inst_5 : @Std.LawfulOrderLT R inst_2 inst_1] {a b c : R},
        @LT.lt R inst_2 a b →
          @LT.lt R inst_2
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) c b)
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) c a)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_left.h11.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_left.h11.prem0)

-- Lean.Grind.CommRing.lt_false_of_denote_eq, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_denote_eq.h10.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_denote_eq.h10.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_denote_eq.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p) →
          @Eq Prop
            (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_denote_eq.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_denote_eq.h10.prem0)

-- Lean.Grind.CommRing.lt_false_of_denote_eq, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_denote_eq.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_denote_eq.h11.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_denote_eq.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p) →
          @Eq Prop
            (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_denote_eq.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_denote_eq.h11.prem0)

-- Lean.Grind.CommRing.le_true_of_kronSN, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronSN.h10.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronSN.h10.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronSN.h10.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronSN.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronEval_k K B a) (Lean.Grind.CommRing.Expr.kronEval_k K B b) →
            @Eq Prop
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_kronSN.h10.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_true_of_kronSN.h10.prem0 HypCheckProof.Lean.Grind.CommRing.le_true_of_kronSN.h10.prem1)

-- Lean.Grind.CommRing.le_true_of_kronSN, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronSN.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronSN.h11.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronSN.h11.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronSN.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Prop
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_kronSN.h11.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_true_of_kronSN.h11.prem0 HypCheckProof.Lean.Grind.CommRing.le_true_of_kronSN.h11.prem1)

-- Lean.Grind.CommRing.Stepwise.d_step1, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h11.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h11.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
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
                (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@List.nil Nat) HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h11.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h11.prem1)

-- Lean.Grind.CommRing.Stepwise.d_step1, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h12.inst : Not
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
          (Lean.Grind.CommRing.Poly.mergeHint (@List.nil Nat)
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
            (Lean.Grind.CommRing.Poly.mulMon_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              Lean.Grind.CommRing.Mon.unit
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h12.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (init p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly)
        (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHint hs p₁ (Lean.Grind.CommRing.Poly.mulMon_k k₂ m₂ p₂)) →
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
                (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx init))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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
        Lean.Grind.CommRing.Mon.unit (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h12.prem0)

-- Lean.Grind.CommRing.Stepwise.d_step1, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h13.inst : Not
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
          (Lean.Grind.CommRing.Poly.mergeHint (@List.nil Nat)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h13.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (init p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly)
        (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHint hs p₁ (Lean.Grind.CommRing.Poly.mulMon_k k₂ m₂ p₂)) →
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
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h13.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1.h13.prem0)

-- Lean.Grind.CommRing.le_true_of_kron, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h10.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h10.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h10.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronEval_k K B a) (Lean.Grind.CommRing.Expr.kronEval_k K B b) →
            @Eq Prop
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h10.prem0 HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h10.prem1)

-- Lean.Grind.CommRing.le_true_of_kron, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h11.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h11.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Prop
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h11.prem0 HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h11.prem1)

-- Lean.Grind.Linarith.zero_lt_one, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h6.inst : Not
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
                (@Lean.Grind.Semiring.toNatModule UInt8
                  (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h6.prem0 : @Eq Bool
      (Lean.Grind.Linarith.zero_lt_one_cert
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h6.prem1 : @Eq UInt8
      (@Lean.Grind.Linarith.Var.denote UInt8
        (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
        (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@One.one UInt8
        (@One.ofOfNat1 UInt8
          (@Lean.Grind.Semiring.ofNat UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
            (nat_lit 1)))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.Ring α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1]
        [inst_4 : @Std.IsPreorder α inst_1] (ctx : Lean.Grind.Linarith.Context α) (p : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.zero_lt_one_cert p) Bool.true →
          @Eq α
              (@Lean.Grind.Linarith.Var.denote α ctx
                (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@One.one α
                (@One.ofOfNat1 α (@Lean.Grind.Semiring.ofNat α (@Lean.Grind.Ring.toSemiring α inst) (nat_lit 1)))) →
            @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α (@Lean.Grind.Ring.toIntModule α inst) ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α (@Lean.Grind.Ring.toSemiring α inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h6.inst (@hc_h (UInt8) (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h6.prem0 HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h6.prem1)

-- Lean.Grind.Linarith.zero_lt_one, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h9.inst : Not
      (@LT.lt Int Int.instLTInt
        (@Lean.Grind.Linarith.Poly.denote' Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h9.prem0 : @Eq Int
      (@Lean.Grind.Linarith.Var.denote Int (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@One.one Int
        (@One.ofOfNat1 Int
          (@Lean.Grind.Semiring.ofNat Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (nat_lit 1)))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.Ring α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1]
        [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst) inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.Linarith.Context α) (p : Lean.Grind.Linarith.Poly),
        @Eq α
            (@Lean.Grind.Linarith.Var.denote α ctx
              (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@One.one α (@One.ofOfNat1 α (@Lean.Grind.Semiring.ofNat α (@Lean.Grind.Ring.toSemiring α inst) (nat_lit 1)))) →
          @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α (@Lean.Grind.Ring.toIntModule α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α (@Lean.Grind.Ring.toSemiring α inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h9.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h9.prem0)

-- Lean.Grind.Linarith.zero_lt_one, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h10.inst : Not
      (@LT.lt Int Int.instLTInt
        (@Lean.Grind.Linarith.Poly.denote' Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.Linarith.Poly.add
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h10.prem0 : @Eq Bool
      (Lean.Grind.Linarith.zero_lt_one_cert
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.Ring α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1]
        [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst) inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.Linarith.Context α) (p : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.zero_lt_one_cert p) Bool.true →
          @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α (@Lean.Grind.Ring.toIntModule α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α (@Lean.Grind.Ring.toSemiring α inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h10.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h10.prem0)

-- Lean.Grind.AC.superpose_ac_idempotent, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_ac_idempotent.h4.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_ac_idempotent.h4.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_ac_idempotent.h4.prem1 : Std.Commutative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Commutative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_ac_idempotent.h4.prem2 : Lean.Grind.AC.superpose_ac_idempotent_cert 0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0)
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose_ac_idempotent.h4.prem3 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.superpose_ac_idempotent.h4 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op} {inst₂ : Std.Commutative ctx.op}
        (x : Lean.Grind.AC.Var) (lhs₁ rhs₁ rhs : Lean.Grind.AC.Seq),
        Lean.Grind.AC.superpose_ac_idempotent_cert x lhs₁ rhs₁ rhs = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
            Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs := fun hc_h => HypCheckProof.Lean.Grind.AC.superpose_ac_idempotent.h4.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.superpose_ac_idempotent.h4.prem0 HypCheckProof.Lean.Grind.AC.superpose_ac_idempotent.h4.prem1 (0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.superpose_ac_idempotent.h4.prem2 HypCheckProof.Lean.Grind.AC.superpose_ac_idempotent.h4.prem3)

-- Int.Internal.Linear.dvd_solve_combine, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_solve_combine.h10.inst : ¬0 ∣
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_solve_combine.h10.prem0 : 0 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_solve_combine.h10.prem1 : 0 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_solve_combine.h10 : ¬∀ (ctx : Int.Internal.Linear.Context) (d₁ : Int) (p₁ : Int.Internal.Linear.Poly) (d₂ : Int)
        (p₂ : Int.Internal.Linear.Poly) (d : Int) (p : Int.Internal.Linear.Poly) (g α β : Int),
        d₁ ∣ Int.Internal.Linear.Poly.denote' ctx p₁ →
          d₂ ∣ Int.Internal.Linear.Poly.denote' ctx p₂ → d ∣ Int.Internal.Linear.Poly.denote' ctx p := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_solve_combine.h10.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (0) (Int.Internal.Linear.Poly.num 0) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) (0) (0) HypCheckProof.Int.Internal.Linear.dvd_solve_combine.h10.prem0 HypCheckProof.Int.Internal.Linear.dvd_solve_combine.h10.prem1)

-- Lean.Grind.Field.NormNum.mul_eq, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.mul_eq.h8.inst : Not
      (@Eq Rat
        (@HMul.hMul Rat Rat Rat
          (@instHMul Rat
            (@Lean.Grind.Semiring.toMul Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.mul_eq.h8 : Not
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
              (@HMul.hMul α α α
                (@instHMul α
                  (@Lean.Grind.Semiring.toMul α
                    (@Lean.Grind.CommSemiring.toSemiring α
                      (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
                a b)
              (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.mul_eq.h8.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) rfl rfl)

-- Lean.Grind.Field.NormNum.mul_eq, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.mul_eq.h9.inst : Not
      (@Eq Rat
        (@HMul.hMul Rat Rat Rat
          (@instHMul Rat
            (@Lean.Grind.Semiring.toMul Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.mul_eq.h9.prem0 : @Eq Bool
      (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat)
        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
      Bool.true := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.mul_eq.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (a b : α) (v₁ v₂ v : Rat),
        @Eq Bool
            (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat) v
              (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) v₁ v₂))
            Bool.true →
          @Eq α b (@Lean.Grind.Field.NormNum.ofRat α inst v₂) →
            @Eq α
              (@HMul.hMul α α α
                (@instHMul α
                  (@Lean.Grind.Semiring.toMul α
                    (@Lean.Grind.CommSemiring.toSemiring α
                      (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
                a b)
              (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.mul_eq.h9.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Field.NormNum.mul_eq.h9.prem0 rfl)

-- Lean.Grind.Field.NormNum.mul_eq, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.mul_eq.h10.inst : Not
      (@Eq Rat
        (@HMul.hMul Rat Rat Rat
          (@instHMul Rat
            (@Lean.Grind.Semiring.toMul Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.mul_eq.h10.prem0 : @Eq Bool
      (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat)
        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
      Bool.true := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.mul_eq.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (a b : α) (v₁ v₂ v : Rat),
        @Eq Bool
            (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat) v
              (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) v₁ v₂))
            Bool.true →
          @Eq α a (@Lean.Grind.Field.NormNum.ofRat α inst v₁) →
            @Eq α
              (@HMul.hMul α α α
                (@instHMul α
                  (@Lean.Grind.Semiring.toMul α
                    (@Lean.Grind.CommSemiring.toSemiring α
                      (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
                a b)
              (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.mul_eq.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Field.NormNum.mul_eq.h10.prem0 rfl)

-- Lean.Grind.Field.NormNum.add_eq, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.add_eq.h8.inst : Not
      (@Eq Rat
        (@HAdd.hAdd Rat Rat Rat
          (@instHAdd Rat
            (@Lean.Grind.Semiring.toAdd Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.add_eq.h8 : Not
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
              (@HAdd.hAdd α α α
                (@instHAdd α
                  (@Lean.Grind.Semiring.toAdd α
                    (@Lean.Grind.CommSemiring.toSemiring α
                      (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
                a b)
              (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.add_eq.h8.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) rfl rfl)

-- Lean.Grind.Field.NormNum.add_eq, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.add_eq.h9.inst : Not
      (@Eq Rat
        (@HAdd.hAdd Rat Rat Rat
          (@instHAdd Rat
            (@Lean.Grind.Semiring.toAdd Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.add_eq.h9.prem0 : @Eq Bool
      (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat)
        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
      Bool.true := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.add_eq.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (a b : α) (v₁ v₂ v : Rat),
        @Eq Bool
            (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat) v
              (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) v₁ v₂))
            Bool.true →
          @Eq α b (@Lean.Grind.Field.NormNum.ofRat α inst v₂) →
            @Eq α
              (@HAdd.hAdd α α α
                (@instHAdd α
                  (@Lean.Grind.Semiring.toAdd α
                    (@Lean.Grind.CommSemiring.toSemiring α
                      (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
                a b)
              (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.add_eq.h9.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Field.NormNum.add_eq.h9.prem0 rfl)

-- Lean.Grind.Field.NormNum.add_eq, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.add_eq.h10.inst : Not
      (@Eq Rat
        (@HAdd.hAdd Rat Rat Rat
          (@instHAdd Rat
            (@Lean.Grind.Semiring.toAdd Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.add_eq.h10.prem0 : @Eq Bool
      (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat)
        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
      Bool.true := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.add_eq.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (a b : α) (v₁ v₂ v : Rat),
        @Eq Bool
            (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat) v
              (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) v₁ v₂))
            Bool.true →
          @Eq α a (@Lean.Grind.Field.NormNum.ofRat α inst v₁) →
            @Eq α
              (@HAdd.hAdd α α α
                (@instHAdd α
                  (@Lean.Grind.Semiring.toAdd α
                    (@Lean.Grind.CommSemiring.toSemiring α
                      (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
                a b)
              (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.add_eq.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Field.NormNum.add_eq.h10.prem0 rfl)

-- Lean.Grind.Field.IsOrdered.mul_lt_mul_iff_of_pos_left, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_lt_mul_iff_of_pos_left.h10.inst : Not
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
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
        (@LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_lt_mul_iff_of_pos_left.h10 : Not
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
              c a)
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              c b))
          (@LT.lt R inst_2 a b)) := fun hc_h => HypCheckProof.Lean.Grind.Field.IsOrdered.mul_lt_mul_iff_of_pos_left.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.Field.IsOrdered.mul_lt_mul_iff_of_neg_left, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_lt_mul_iff_of_neg_left.h10.inst : Not
      (Iff
        (@LT.lt Rat Rat.instLT
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
        (@LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_lt_mul_iff_of_neg_left.h10 : Not
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
              c a)
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              c b))
          (@LT.lt R inst_2 b a)) := fun hc_h => HypCheckProof.Lean.Grind.Field.IsOrdered.mul_lt_mul_iff_of_neg_left.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.OrderedAdd.add_lt_left, hypothesis 4: necessary
/- FAILED: 8:220: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 } | 41:123: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h4.inst : ¬(0 + 1) % 2 < (1 + 1) % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h4.prem0 : 0 % 2 < 1 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M] [inst_3 : LT M]
        [inst : Std.LawfulOrderLT M] {a b : M}, a < b → ∀ (c : M), a + c < b + c := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) ({ lt := fun (a b : Nat) => a % 2 < b % 2 : LT Nat }) (@Std.LawfulOrderLT.mk _ _ _ (by (try dsimp only);   (intros; omega))) (0) (1) HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h4.prem0 (1))
-/

-- Lean.Grind.OrderedAdd.add_lt_left, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h6.inst : ¬(0 + 1) % 2 < (1 + 1) % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h6.prem0 : 0 % 2 < 1 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h6 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M]
        [inst : Lean.Grind.OrderedAdd M] [inst : LT M] {a b : M}, a < b → ∀ (c : M), a + c < b + c := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h6.inst (@hc_h (Nat) (instLENat) _ (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) _ ({ lt := fun (a b : Nat) => a % 2 < b % 2 : LT Nat }) (0) (1) HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h6.prem0 (1))

-- Lean.Grind.Linarith.le_norm, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_norm.h4.inst : Not
      (@LE.le UInt8 instLEUInt8
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
theorem HypCheckProof.Lean.Grind.Linarith.le_norm.h4.prem0 : @Eq Bool
      (Lean.Grind.Linarith.norm_cert Lean.Grind.Linarith.Expr.zero
        (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_norm.h4.prem1 : @LE.le UInt8 instLEUInt8
      (@Lean.Grind.Linarith.Expr.denote_k UInt8
        (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
        (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
        Lean.Grind.Linarith.Expr.zero)
      (@Lean.Grind.Linarith.Expr.denote_k UInt8
        (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
        (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
        (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.le_norm.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.Linarith.Context α) (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.norm_cert lhs rhs p) Bool.true →
          @LE.le α inst_1 (@Lean.Grind.Linarith.Expr.denote_k α inst ctx lhs)
              (@Lean.Grind.Linarith.Expr.denote_k α inst ctx rhs) →
            @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.le_norm.h4.inst (@hc_h (UInt8) (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)) (instLEUInt8) _ (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.le_norm.h4.prem0 HypCheckProof.Lean.Grind.Linarith.le_norm.h4.prem1)

-- Lean.Grind.Linarith.le_norm, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_norm.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.le_norm.h9.prem0 : @LE.le Int Int.instLEInt
      (@Lean.Grind.Linarith.Expr.denote_k Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Expr.zero)
      (@Lean.Grind.Linarith.Expr.denote_k Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Expr.zero) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.le_norm.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        [inst_3 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 inst_2]
        (ctx : Lean.Grind.Linarith.Context α) (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @LE.le α inst_1 (@Lean.Grind.Linarith.Expr.denote_k α inst ctx lhs)
            (@Lean.Grind.Linarith.Expr.denote_k α inst ctx rhs) →
          @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.le_norm.h9.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.le_norm.h9.prem0)

-- Lean.Grind.Linarith.le_norm, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_norm.h10.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.le_norm.h10.prem0 : @Eq Bool
      (Lean.Grind.Linarith.norm_cert
        (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        Lean.Grind.Linarith.Expr.zero
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.le_norm.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        [inst_3 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 inst_2]
        (ctx : Lean.Grind.Linarith.Context α) (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.norm_cert lhs rhs p) Bool.true →
          @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.le_norm.h10.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.le_norm.h10.prem0)

-- Lean.Grind.Field.IsOrdered.lt_mul_inv_iff_lt_mul_of_neg, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.lt_mul_inv_iff_lt_mul_of_neg.h10.inst : Not
      (Iff
        (@LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
            (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
              (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))))
        (@LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.lt_mul_inv_iff_lt_mul_of_neg.h10 : Not
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
          (@LT.lt R inst_2 b
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              a c))) := fun hc_h => HypCheckProof.Lean.Grind.Field.IsOrdered.lt_mul_inv_iff_lt_mul_of_neg.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))

-- Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_neg_right, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_neg_right.h10.inst : Not
      (Iff
        (@LE.le Rat Rat.instLE
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
        (@LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_neg_right.h10 : Not
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
          (@LE.le R inst_1
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
          (@LE.le R inst_1 b a)) := fun hc_h => HypCheckProof.Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_neg_right.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.Field.IsOrdered.mul_inv_lt_iff_mul_lt_of_neg, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_inv_lt_iff_mul_lt_of_neg.h10.inst : Not
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
        (@LT.lt Rat Rat.instLT
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_inv_lt_iff_mul_lt_of_neg.h10 : Not
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
          (@LT.lt R inst_2
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              c b)
            a)) := fun hc_h => HypCheckProof.Lean.Grind.Field.IsOrdered.mul_inv_lt_iff_mul_lt_of_neg.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.Order.le_of_offset_eq_1_k, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_of_offset_eq_1_k.h10.inst : Not
      (@LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_of_offset_eq_1_k.h10 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b : α} {k : Int},
        @LE.le α inst a
          (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
            (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_of_offset_eq_1_k.h10.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Lean.Grind.Field.IsOrdered.mul_inv_le_iff_mul_le_of_neg, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_inv_le_iff_mul_le_of_neg.h10.inst : Not
      (Iff
        (@LE.le Rat Rat.instLE
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
              (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
        (@LE.le Rat Rat.instLE
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_inv_le_iff_mul_le_of_neg.h10 : Not
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
          (@LE.le R inst_1
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              a (@Inv.inv R (@Lean.Grind.Field.toInv R inst) b))
            c)
          (@LE.le R inst_1
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              c b)
            a)) := fun hc_h => HypCheckProof.Lean.Grind.Field.IsOrdered.mul_inv_le_iff_mul_le_of_neg.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))

-- Lean.Grind.Order.le_of_offset_eq_2_k, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_of_offset_eq_2_k.h10.inst : Not
      (@LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_of_offset_eq_2_k.h10 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b : α} {k : Int},
        @LE.le α inst b
          (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
            (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) (@Neg.neg Int Int.instNegInt k)))) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_of_offset_eq_2_k.h10.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))

-- Lean.Grind.CommRing.eq_of_kron_rel, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kron_rel.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kron_rel.h11.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kron_rel.h11.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kron_rel.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (l r l' r' : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B (l.sub r) (l'.sub r')) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K (l.sub r) (l'.sub r')) Bool.true →
            @Eq Prop
              (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r))
              (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx l')
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx r'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_of_kron_rel.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_of_kron_rel.h11.prem0 HypCheckProof.Lean.Grind.CommRing.eq_of_kron_rel.h11.prem1)

-- Lean.Grind.OrderedRing.le_of_natCast_le_natCast, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.le_of_natCast_le_natCast.h9.inst : ¬1 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.le_of_natCast_le_natCast.h9 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R]
        [inst_4 : Std.IsPreorder R] [inst : Lean.Grind.OrderedRing R] (a b : Nat), a ≤ b := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.le_of_natCast_le_natCast.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt.toRing) (Int.instLEInt) (Int.instLTInt) _ _ _ (1) (0))

-- Lean.Grind.OrderedAdd.zsmul_pos_iff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_pos_iff.h4.inst : ¬(0 < -1 • UInt8.ofNat 1 ↔ 0 < -1) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_pos_iff.h4.prem0 : 0 < UInt8.ofNat 1 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_pos_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.IntModule M] [inst_3 : LT M]
        [inst : Std.LawfulOrderLT M] (k : Int) {x : M}, 0 < x → (0 < k • x ↔ 0 < k) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_pos_iff.h4.inst (@hc_h (UInt8) (instLEUInt8) _ (Lean.Grind.Ring.toIntModule) (instLTUInt8) _ (-1) (UInt8.ofNat 1) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_pos_iff.h4.prem0)

-- Lean.Grind.OrderedAdd.zsmul_pos_iff, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_pos_iff.h9.inst : Not
      (Iff
        (@LT.lt Int Int.instLTInt
          (@OfNat.ofNat Int (nat_lit 0)
            (@Zero.toOfNat0 Int
              (@Lean.Grind.AddCommMonoid.toZero Int
                (@Lean.Grind.NatModule.toAddCommMonoid Int
                  (@Lean.Grind.IntModule.toNatModule Int
                    (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
          (@HSMul.hSMul Int Int Int
            (@instHSMul Int Int
              (@Lean.Grind.IntModule.zsmul Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_pos_iff.h9 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : @Std.IsPreorder M inst] [inst_2 : Lean.Grind.IntModule M]
        [inst_3 :
          @Lean.Grind.OrderedAdd M
            (@instHAdd M
              (@Lean.Grind.AddCommMonoid.toAdd M
                (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2))))
            inst inst_1]
        [inst_4 : LT M] [inst : @Std.LawfulOrderLT M inst_4 inst] (k : Int) {x : M},
        Iff
          (@LT.lt M inst_4
            (@OfNat.ofNat M (nat_lit 0)
              (@Zero.toOfNat0 M
                (@Lean.Grind.AddCommMonoid.toZero M
                  (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2)))))
            (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k x))
          (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_pos_iff.h9.inst (@hc_h (Int) (Int.instLEInt) _ (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (Int.instLTInt) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Lean.Grind.AC.diseq_erase0, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_erase0.h3.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_erase0.h3.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_erase0.h3.prem1 : Lean.Grind.AC.eq_erase0_cert (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0))
        (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_erase0.h3.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) ≠
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_erase0.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} (lhs rhs lhs' rhs' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.eq_erase0_cert lhs rhs lhs' rhs' = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs ≠ Lean.Grind.AC.Seq.denote ctx rhs →
            Lean.Grind.AC.Seq.denote ctx lhs' ≠ Lean.Grind.AC.Seq.denote ctx rhs' := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_erase0.h3.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.diseq_erase0.h3.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_erase0.h3.prem1 HypCheckProof.Lean.Grind.AC.diseq_erase0.h3.prem2)

-- Lean.Grind.AC.eq_erase0, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase0.h3.inst : ¬Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 1) =
        Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase0.h3.prem0 : Std.Associative
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase0.h3.prem1 : Lean.Grind.AC.eq_erase0_cert (Lean.Grind.AC.Seq.var 1) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0))
        (Lean.Grind.AC.Seq.var 1) (Lean.Grind.AC.Seq.var 0) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase0.h3.prem2 : Lean.Grind.AC.Seq.denote
        {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 1) =
      Lean.Grind.AC.Seq.denote
        {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.eq_erase0.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} (lhs rhs lhs' rhs' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.eq_erase0_cert lhs rhs lhs' rhs' = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs = Lean.Grind.AC.Seq.denote ctx rhs →
            Lean.Grind.AC.Seq.denote ctx lhs' = Lean.Grind.AC.Seq.denote ctx rhs' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_erase0.h3.inst (@hc_h (Nat) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
      op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_erase0.h3.prem0 (Lean.Grind.AC.Seq.var 1) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 1) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.eq_erase0.h3.prem1 HypCheckProof.Lean.Grind.AC.eq_erase0.h3.prem2)

-- Lean.Grind.CommRing.eq_gcd, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_gcd.h8.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_gcd.h8.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_gcd.h8.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_gcd.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Int)
        (p₁ p₂ p : Lean.Grind.CommRing.Poly),
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_gcd.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.eq_gcd.h8.prem0 HypCheckProof.Lean.Grind.CommRing.eq_gcd.h8.prem1)

-- Lean.Grind.CommRing.eq_gcd, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_gcd.h9.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_gcd.h9.prem0 : @Eq Bool
      (Lean.Grind.CommRing.eq_gcd_cert (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_gcd.h9.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_gcd.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Int)
        (p₁ p₂ p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.eq_gcd_cert a b p₁ p₂ p) Bool.true →
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_gcd.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.eq_gcd.h9.prem0 HypCheckProof.Lean.Grind.CommRing.eq_gcd.h9.prem1)

-- Lean.Grind.CommRing.eq_gcd, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_gcd.h10.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_gcd.h10.prem0 : @Eq Bool
      (Lean.Grind.CommRing.eq_gcd_cert (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_gcd.h10.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_gcd.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Int)
        (p₁ p₂ p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.eq_gcd_cert a b p₁ p₂ p) Bool.true →
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_gcd.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.eq_gcd.h10.prem0 HypCheckProof.Lean.Grind.CommRing.eq_gcd.h10.prem1)

-- Lean.Grind.CommRing.Stepwise.imp_1eqC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h3.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.imp_1eq_certC
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h3.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (lhs rhs : Lean.Grind.CommRing.Expr) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.imp_1eq_certC lhs rhs p₁ p₂ c) Bool.true →
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
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h3.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h3.prem1)

-- Lean.Grind.CommRing.Stepwise.imp_1eqC, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h9.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h9.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h9 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p₁ p₂ : Lean.Grind.CommRing.Poly),
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
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h9.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h9.prem0)

-- Lean.Grind.CommRing.Stepwise.imp_1eqC, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h10.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h10.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.imp_1eq_certC
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h10 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.imp_1eq_certC lhs rhs p₁ p₂ c) Bool.true →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h10.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqC.h10.prem0)

-- Lean.Grind.CommRing.Stepwise.imp_keq, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keq.h9.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keq.h9.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keq.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        [inst_1 :
          @Lean.Grind.NoNatZeroDivisors α
            (@Lean.Grind.Semiring.toNatModule α
              (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))]
        (k : Int) (lhs rhs : Lean.Grind.CommRing.Expr) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq α
            (@HMul.hMul α α α
              (@instHMul α
                (@Lean.Grind.Semiring.toMul α
                  (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
              (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁))
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keq.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keq.h9.prem0)

-- Lean.Grind.CommRing.Stepwise.imp_keq, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keq.h10.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keq.h10.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.imp_keq_cert
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keq.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        [inst_1 :
          @Lean.Grind.NoNatZeroDivisors α
            (@Lean.Grind.Semiring.toNatModule α
              (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))]
        (k : Int) (lhs rhs : Lean.Grind.CommRing.Expr) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.imp_keq_cert lhs rhs k p₁ p₂) Bool.true →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keq.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_keq.h10.prem0)

-- Lean.Grind.Field.IsOrdered.pos_of_inv_pos, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.pos_of_inv_pos.h8.inst : Not
      (@LT.lt Rat Rat.instLT
        (@OfNat.ofNat Rat (nat_lit 0)
          (@Zero.toOfNat0 Rat
            (@Lean.Grind.AddCommMonoid.toZero Rat
              (@Lean.Grind.NatModule.toAddCommMonoid Rat
                (@Lean.Grind.Semiring.toNatModule Rat
                  (@Lean.Grind.CommSemiring.toSemiring Rat
                    (@Lean.Grind.CommRing.toCommSemiring Rat
                      (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))))))
        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) := by
  decide
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.pos_of_inv_pos.h8 : Not
      (∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R]
        [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1] [inst_4 : @Std.IsLinearOrder R inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing R
            (@Lean.Grind.CommSemiring.toSemiring R
              (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))
            inst_1 inst_2
            (@Std.IsLinearPreorder.toIsPreorder R inst_1 (@Std.IsLinearOrder.toIsLinearPreorder R inst_1 inst_4))]
        {a : R},
        @LT.lt R inst_2
          (@OfNat.ofNat R (nat_lit 0)
            (@Zero.toOfNat0 R
              (@Lean.Grind.AddCommMonoid.toZero R
                (@Lean.Grind.NatModule.toAddCommMonoid R
                  (@Lean.Grind.Semiring.toNatModule R
                    (@Lean.Grind.CommSemiring.toSemiring R
                      (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst))))))))
          a) := fun hc_h => HypCheckProof.Lean.Grind.Field.IsOrdered.pos_of_inv_pos.h8.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Int.Internal.Linear.eq_diseq_subst_rfl, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.combine_mul_k
            ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0)
            ((Int.Internal.Linear.Poly.num 0).coeff_k 0).neg_k (Int.Internal.Linear.Poly.num 0)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) ≠
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h5.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h5.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≠
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        p₃ = Int.Internal.Linear.Poly.combine_mul_k (p₂.coeff_k x) (p₁.coeff_k x).neg_k p₁ p₂ →
          Int.Internal.Linear.Poly.denote' ctx p₁ = 0 →
            Int.Internal.Linear.Poly.denote' ctx p₂ ≠ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.combine_mul_k ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0)
      ((Int.Internal.Linear.Poly.num 0).coeff_k 0).neg_k (Int.Internal.Linear.Poly.num 0)
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) rfl HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h5.prem0 HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h5.prem1)

-- Int.Internal.Linear.eq_diseq_subst_rfl, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0) (Int.Internal.Linear.Poly.num 0) ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h6.prem0 : ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0).bneZero_k = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h6.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h6.prem2 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0) (Int.Internal.Linear.Poly.num 1) ≠ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        (p₁.coeff_k x).bneZero_k = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₁ = 0 →
            Int.Internal.Linear.Poly.denote' ctx p₂ ≠ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h6.inst (@hc_h (Lean.RArray.leaf 0) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h6.prem0 HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h6.prem1 HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h6.prem2)

-- Int.Internal.Linear.eq_diseq_subst_rfl, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h7.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.combine_mul_k
            ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0)
            ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0).neg_k
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) ≠
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h7.prem0 : ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0).bneZero_k = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h7.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≠
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        (p₁.coeff_k x).bneZero_k = Bool.true →
          p₃ = Int.Internal.Linear.Poly.combine_mul_k (p₂.coeff_k x) (p₁.coeff_k x).neg_k p₁ p₂ →
            Int.Internal.Linear.Poly.denote' ctx p₂ ≠ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h7.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.combine_mul_k ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0)
      ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0).neg_k
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h7.prem0 rfl HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h7.prem1)

-- Int.Internal.Linear.eq_diseq_subst_rfl, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h8.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0)
          (Int.Internal.Linear.Poly.combine_mul_k ((Int.Internal.Linear.Poly.num 0).coeff_k 0)
            ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0).neg_k
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0)) ≠
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h8.prem0 : ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0).bneZero_k = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h8.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h8 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        (p₁.coeff_k x).bneZero_k = Bool.true →
          p₃ = Int.Internal.Linear.Poly.combine_mul_k (p₂.coeff_k x) (p₁.coeff_k x).neg_k p₁ p₂ →
            Int.Internal.Linear.Poly.denote' ctx p₁ = 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h8.inst (@hc_h (Lean.RArray.leaf 0) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.combine_mul_k ((Int.Internal.Linear.Poly.num 0).coeff_k 0)
      ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0).neg_k
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h8.prem0 rfl HypCheckProof.Int.Internal.Linear.eq_diseq_subst_rfl.h8.prem1)

-- Lean.Grind.CommRing.gcd_eq_0, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h7.inst : Not
      (@Eq Int
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h7.prem0 : @Eq Int
      (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h7.prem1 : @Eq Int
      (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (g n m a b : Int),
        @Eq α (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) n)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
          @Eq α (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) m)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
            @Eq α (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) g)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h7.prem0 HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h7.prem1)

-- Lean.Grind.CommRing.gcd_eq_0, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h8.inst : Not
      (@Eq Int
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
            (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h8.prem0 : @Eq Int
      (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (g n m a b : Int),
        @Eq Int g
            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) a n)
              (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) b m)) →
          @Eq α (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) m)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
            @Eq α (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) g)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
      (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) rfl HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h8.prem0)

-- Lean.Grind.CommRing.gcd_eq_0, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h9.inst : Not
      (@Eq Int
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
            (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h9.prem0 : @Eq Int
      (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (g n m a b : Int),
        @Eq Int g
            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) a n)
              (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) b m)) →
          @Eq α (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) n)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
            @Eq α (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) g)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
      (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) rfl HypCheckProof.Lean.Grind.CommRing.gcd_eq_0.h9.prem0)

-- Int.Internal.Linear.dvd_le_tight_mod, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_le_tight_mod.h7.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_le_tight_mod.h7.prem0 : 0 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_le_tight_mod.h7.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_le_tight_mod.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (d : Int) (p₁ p₂ p₃ : Int.Internal.Linear.Poly) (t g : Int),
        d ∣ Int.Internal.Linear.Poly.denote' ctx p₁ →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_le_tight_mod.h7.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) (0) HypCheckProof.Int.Internal.Linear.dvd_le_tight_mod.h7.prem0 HypCheckProof.Int.Internal.Linear.dvd_le_tight_mod.h7.prem1)

-- Int.Internal.Linear.dvd_le_tight_mod, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_le_tight_mod.h9.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_le_tight_mod.h9.prem0 : Int.Internal.Linear.dvd_le_tight_mod_cert 0 (Int.Internal.Linear.Poly.num 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) 0 1 =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_le_tight_mod.h9.prem1 : 0 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_le_tight_mod.h9 : ¬∀ (ctx : Int.Internal.Linear.Context) (d : Int) (p₁ p₂ p₃ : Int.Internal.Linear.Poly) (t g : Int),
        Int.Internal.Linear.dvd_le_tight_mod_cert d p₁ p₂ p₃ t g = Bool.true →
          d ∣ Int.Internal.Linear.Poly.denote' ctx p₁ → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_le_tight_mod.h9.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) (1) HypCheckProof.Int.Internal.Linear.dvd_le_tight_mod.h9.prem0 HypCheckProof.Int.Internal.Linear.dvd_le_tight_mod.h9.prem1)

-- Lean.Grind.CommRing.Stepwise.coreC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreC.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
                (Lean.Grind.CommRing.Expr.var
                  (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))).toPolyC_k
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreC.h3.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p ((lhs.sub rhs).toPolyC_k c) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs) →
            @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.coreC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.var
            (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))).toPolyC_k
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.coreC.h3.prem0)

-- Lean.Grind.CommRing.Stepwise.coreC, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreC.h8.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreC.h8.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreC.h8 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs) →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.coreC.h8.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.coreC.h8.prem0)

-- Lean.Grind.CommRing.Stepwise.coreC, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreC.h9.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
                (Lean.Grind.CommRing.Expr.var
                  (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))).toPolyC_k
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.CommSemiring.toSemiring Int
                    (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreC.h9 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p ((lhs.sub rhs).toPolyC_k c) →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.coreC.h9.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.var
            (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))).toPolyC_k
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) rfl)

-- Lean.Grind.CommRing.le_true_of_denote_eq, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h8.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h8.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p) →
          @Eq Prop
            (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h8.prem0)

-- Lean.Grind.CommRing.le_true_of_denote_eq, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h9.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p) →
          @Eq Prop
            (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h9.prem0)

-- Lean.Grind.CommRing.Stepwise.mulC, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.mulC.h8.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.mulC.h8.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.mulC.h8 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly) (k : Int) (p : Lean.Grind.CommRing.Poly),
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
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.mulC.h8.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.mulC.h8.prem0)

-- Lean.Grind.CommRing.Stepwise.mulC, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.mulC.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.mulC.h9.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.mul_certC
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.mulC.h9 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly) (k : Int) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.mul_certC p₁ k p c) Bool.true →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.mulC.h9.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.mulC.h9.prem0)

-- Lean.Grind.OrderedAdd.zsmul_nonneg, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonneg.h7.inst : Not
      (@LE.le Int Int.instLEInt
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.IntModule.toNatModule Int
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
        (@HSMul.hSMul Int Int Int
          (@instHSMul Int Int
            (@Lean.Grind.IntModule.zsmul Int
              (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonneg.h7.prem0 : @LE.le Int Int.instLEInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonneg.h7 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : @Std.IsPreorder M inst] [inst_2 : Lean.Grind.IntModule M]
        [inst_3 :
          @Lean.Grind.OrderedAdd M
            (@instHAdd M
              (@Lean.Grind.AddCommMonoid.toAdd M
                (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2))))
            inst inst_1]
        {k : Int} {x : M},
        @LE.le M inst
            (@OfNat.ofNat M (nat_lit 0)
              (@Zero.toOfNat0 M
                (@Lean.Grind.AddCommMonoid.toZero M
                  (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2)))))
            x →
          @LE.le M inst
            (@OfNat.ofNat M (nat_lit 0)
              (@Zero.toOfNat0 M
                (@Lean.Grind.AddCommMonoid.toZero M
                  (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2)))))
            (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k x)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonneg.h7.inst (@hc_h (Int) (Int.instLEInt) _ (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonneg.h7.prem0)

-- Lean.Grind.OrderedAdd.zsmul_nonneg, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonneg.h8.inst : Not
      (@LE.le Int Int.instLEInt
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.IntModule.toNatModule Int
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
        (@HSMul.hSMul Int Int Int
          (@instHSMul Int Int
            (@Lean.Grind.IntModule.zsmul Int
              (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonneg.h8.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonneg.h8 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : @Std.IsPreorder M inst] [inst_2 : Lean.Grind.IntModule M]
        [inst_3 :
          @Lean.Grind.OrderedAdd M
            (@instHAdd M
              (@Lean.Grind.AddCommMonoid.toAdd M
                (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2))))
            inst inst_1]
        {k : Int} {x : M},
        @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k →
          @LE.le M inst
            (@OfNat.ofNat M (nat_lit 0)
              (@Zero.toOfNat0 M
                (@Lean.Grind.AddCommMonoid.toZero M
                  (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2)))))
            (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k x)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonneg.h8.inst (@hc_h (Int) (Int.instLEInt) _ (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonneg.h8.prem0)

-- Lean.Grind.OrderedRing.pos_natCast_of_pos, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.pos_natCast_of_pos.h8.inst : Not
      (@LT.lt Int Int.instLTInt
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
        (@Nat.cast Int
          (@Lean.Grind.Semiring.natCast Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.pos_natCast_of_pos.h8 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1]
        [inst_5 : @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2 inst_4] (a : Nat),
        @LT.lt R inst_2
          (@OfNat.ofNat R (nat_lit 0)
            (@Zero.toOfNat0 R
              (@Lean.Grind.AddCommMonoid.toZero R
                (@Lean.Grind.NatModule.toAddCommMonoid R
                  (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
          (@Nat.cast R (@Lean.Grind.Semiring.natCast R (@Lean.Grind.Ring.toSemiring R inst)) a)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.pos_natCast_of_pos.h8.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))

-- Lean.Grind.OrderedRing.nonpos_intCast_of_nonpos, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.nonpos_intCast_of_nonpos.h6.inst : Not
      (@LE.le UInt8 instLEUInt8
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
theorem HypCheckProof.Lean.Grind.OrderedRing.nonpos_intCast_of_nonpos.h6.prem0 : @LE.le Int Int.instLEInt (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.nonpos_intCast_of_nonpos.h6 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1] (a : Int),
        @LE.le Int Int.instLEInt a (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          @LE.le R inst_1 (@Int.cast R (@Lean.Grind.Ring.intCast R inst) a)
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.nonpos_intCast_of_nonpos.h6.inst (@hc_h (UInt8) (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (instLEUInt8) (instLTUInt8) _ _ (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.OrderedRing.nonpos_intCast_of_nonpos.h6.prem0)

-- Lean.Grind.OrderedRing.nonpos_intCast_of_nonpos, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.nonpos_intCast_of_nonpos.h8.inst : Not
      (@LE.le Int Int.instLEInt
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.nonpos_intCast_of_nonpos.h8 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1]
        [inst_5 : @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2 inst_4] (a : Int),
        @LE.le R inst_1 (@Int.cast R (@Lean.Grind.Ring.intCast R inst) a)
          (@OfNat.ofNat R (nat_lit 0)
            (@Zero.toOfNat0 R
              (@Lean.Grind.AddCommMonoid.toZero R
                (@Lean.Grind.NatModule.toAddCommMonoid R
                  (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.nonpos_intCast_of_nonpos.h8.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))

-- Lean.Grind.CommRing.eq_normEq0, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_normEq0.h7.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_normEq0.h7.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_normEq0.h7.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_normEq0.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (c : Nat)
        (p₁ p₂ p : Lean.Grind.CommRing.Poly),
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_normEq0.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.eq_normEq0.h7.prem0 HypCheckProof.Lean.Grind.CommRing.eq_normEq0.h7.prem1)

-- Lean.Grind.CommRing.eq_normEq0, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_normEq0.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_normEq0.h9.prem0 : @Eq Bool
      (Lean.Grind.CommRing.eq_normEq0_cert (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_normEq0.h9.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_normEq0.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (c : Nat)
        (p₁ p₂ p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.eq_normEq0_cert c p₁ p₂ p) Bool.true →
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_normEq0.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.eq_normEq0.h9.prem0 HypCheckProof.Lean.Grind.CommRing.eq_normEq0.h9.prem1)

-- Lean.Grind.CommRing.Stepwise.div, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.div.h7.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.div.h7.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.div.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        [inst_1 :
          @Lean.Grind.NoNatZeroDivisors α
            (@Lean.Grind.Semiring.toNatModule α
              (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))]
        (p₁ : Lean.Grind.CommRing.Poly) (k : Int) (p : Lean.Grind.CommRing.Poly),
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
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.div.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) _ (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.div.h7.prem0)

-- Lean.Grind.CommRing.Stepwise.div, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.div.h8.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.div.h8.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.div_cert
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.div.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        [inst_1 :
          @Lean.Grind.NoNatZeroDivisors α
            (@Lean.Grind.Semiring.toNatModule α
              (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))]
        (p₁ : Lean.Grind.CommRing.Poly) (k : Int) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.div_cert p₁ k p) Bool.true →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.div.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) _ (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.div.h8.prem0)

-- Int.Internal.Linear.eq_eq_subst', hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h6.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h6.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (a b : Int) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ = 0 →
          Int.Internal.Linear.Poly.denote' ctx p₂ = 0 → Int.Internal.Linear.Poly.denote' ctx p₃ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h6.inst (@hc_h (Lean.RArray.leaf 1) (0) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h6.prem0 HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h6.prem1)

-- Int.Internal.Linear.eq_eq_subst', hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h7.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h7.prem0 : Int.Internal.Linear.eq_eq_subst'_cert 0 1 (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
        (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h7.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (a b : Int) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.eq_eq_subst'_cert a b p₁ p₂ p₃ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₂ = 0 → Int.Internal.Linear.Poly.denote' ctx p₃ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h7.inst (@hc_h (Lean.RArray.leaf 1) (0) (1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h7.prem0 HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h7.prem1)

-- Int.Internal.Linear.eq_eq_subst', hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h8.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h8.prem0 : Int.Internal.Linear.eq_eq_subst'_cert (-1) 0 (Int.Internal.Linear.Poly.num 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h8.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h8 : ¬∀ (ctx : Int.Internal.Linear.Context) (a b : Int) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.eq_eq_subst'_cert a b p₁ p₂ p₃ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₁ = 0 → Int.Internal.Linear.Poly.denote' ctx p₃ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h8.inst (@hc_h (Lean.RArray.leaf 1) (-1) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h8.prem0 HypCheckProof.Int.Internal.Linear.eq_eq_subst'.h8.prem1)

-- Lean.Grind.AC.diseq_norm_a, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_norm_a.h7.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_norm_a.h7.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_norm_a.h7.prem1 : Lean.Grind.AC.Expr.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Expr.var 0) ≠
      Lean.Grind.AC.Expr.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_norm_a.h7 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} (lhs rhs : Lean.Grind.AC.Expr)
        (lhs' rhs' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Expr.denote ctx lhs ≠ Lean.Grind.AC.Expr.denote ctx rhs →
          Lean.Grind.AC.Seq.denote ctx lhs' ≠ Lean.Grind.AC.Seq.denote ctx rhs' := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_norm_a.h7.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.diseq_norm_a.h7.prem0 (Lean.Grind.AC.Expr.var 0) ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_norm_a.h7.prem1)

-- Lean.Grind.AC.diseq_norm_a, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_norm_a.h8.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_norm_a.h8.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_norm_a.h8.prem1 : Lean.Grind.AC.eq_norm_a_cert (Lean.Grind.AC.Expr.var 0) (Lean.Grind.AC.Expr.var 0) (Lean.Grind.AC.Seq.var 0)
        (Lean.Grind.AC.Seq.var 0) =
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_norm_a.h8 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} (lhs rhs : Lean.Grind.AC.Expr)
        (lhs' rhs' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.eq_norm_a_cert lhs rhs lhs' rhs' = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs' ≠ Lean.Grind.AC.Seq.denote ctx rhs' := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_norm_a.h8.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.diseq_norm_a.h8.prem0 (Lean.Grind.AC.Expr.var 0) (Lean.Grind.AC.Expr.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_norm_a.h8.prem1)

-- Lean.Grind.AC.Seq.denote_insert_of_contains, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_insert_of_contains.h3.inst : ¬Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.insert 0 (Lean.Grind.AC.Seq.cons 1 (Lean.Grind.AC.Seq.var 0))) =
        Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 1 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_insert_of_contains.h3.prem0 : (Lean.Grind.AC.Seq.cons 1 (Lean.Grind.AC.Seq.var 0)).contains_k 0 = Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_insert_of_contains.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) [inst₁ : Std.Associative ctx.op] [inst₃ : Std.IdempotentOp ctx.op]
        (s : Lean.Grind.AC.Seq) (x : Lean.Grind.AC.Var),
        s.contains_k x = Bool.true →
          Lean.Grind.AC.Seq.denote ctx (Lean.Grind.AC.Seq.insert x s) = Lean.Grind.AC.Seq.denote ctx s := fun hc_h => HypCheckProof.Lean.Grind.AC.Seq.denote_insert_of_contains.h3.inst (@hc_h (Nat) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
      op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }) (@Std.Associative.mk _ _ (by (try dsimp only);   (intros; simp_all; done))) (@Std.IdempotentOp.mk _ _ (by (try dsimp only);   (intros; simp_all; done))) (Lean.Grind.AC.Seq.cons 1 (Lean.Grind.AC.Seq.var 0)) (0) HypCheckProof.Lean.Grind.AC.Seq.denote_insert_of_contains.h3.prem0)

-- Lean.Grind.AC.Seq.denote_insert_of_contains, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_insert_of_contains.h4.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.insert 0 (Lean.Grind.AC.Seq.var 0)) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_insert_of_contains.h4.prem0 : (Lean.Grind.AC.Seq.var 0).contains_k 0 = Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_insert_of_contains.h4 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) [inst₁ : Std.Associative ctx.op] [inst₂ : Std.Commutative ctx.op]
        (s : Lean.Grind.AC.Seq) (x : Lean.Grind.AC.Var),
        s.contains_k x = Bool.true →
          Lean.Grind.AC.Seq.denote ctx (Lean.Grind.AC.Seq.insert x s) = Lean.Grind.AC.Seq.denote ctx s := fun hc_h => HypCheckProof.Lean.Grind.AC.Seq.denote_insert_of_contains.h4.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) _ _ (Lean.Grind.AC.Seq.var 0) (0) HypCheckProof.Lean.Grind.AC.Seq.denote_insert_of_contains.h4.prem0)

-- Int.Internal.Linear.eq_le_subst_nonpos, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h5.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h5.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ = 0 →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h5.prem0 HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h5.prem1)

-- Int.Internal.Linear.eq_le_subst_nonpos, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0) (Int.Internal.Linear.Poly.num 1) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h6.prem0 : Int.Internal.Linear.eq_le_subst_nonpos_cert 0 (Int.Internal.Linear.Poly.num 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 1) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h6.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.eq_le_subst_nonpos_cert x p₁ p₂ p₃ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h6.inst (@hc_h (Lean.RArray.leaf 0) (0) (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h6.prem0 HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h6.prem1)

-- Int.Internal.Linear.eq_le_subst_nonpos, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h7.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h7.prem0 : Int.Internal.Linear.eq_le_subst_nonpos_cert 1
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0)))
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h7.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0))) =
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.eq_le_subst_nonpos_cert x p₁ p₂ p₃ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₁ = 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h7.inst (@hc_h (Lean.RArray.leaf 1) (1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0))) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h7.prem0 HypCheckProof.Int.Internal.Linear.eq_le_subst_nonpos.h7.prem1)

-- Lean.Grind.CommRing.Expr.denote_powLeafBC_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_powLeafBC_k.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).powLeafBC_k
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))
        (@HPow.hPow Int Nat Int
          (@Lean.Grind.Semiring.npow Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_powLeafBC_k.h3.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_powLeafBC_k.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (a : Lean.Grind.CommRing.Expr) (k : Nat) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a) →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.powLeafBC_k k c p))
            (@HPow.hPow α Nat α
              (@Lean.Grind.Semiring.npow α
                (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a) k)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_powLeafBC_k.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_powLeafBC_k.h3.prem0)

-- Lean.Grind.CommRing.Expr.denote_powLeafBC_k, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_powLeafBC_k.h8.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).add
                (Lean.Grind.CommRing.Expr.var
                  (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1))))).powLeafBC_k
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@HPow.hPow Int Nat Int
          (@Lean.Grind.Semiring.npow Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            ((Lean.Grind.CommRing.Expr.var
                  (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).add
              (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_powLeafBC_k.h8 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr) (k : Nat) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.powLeafBC_k k c p))
          (@HPow.hPow α Nat α
            (@Lean.Grind.Semiring.npow α
              (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a) k)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_powLeafBC_k.h8.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).add
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))

-- Lean.Grind.OrderedRing.neg_one_lt_zero, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.neg_one_lt_zero.h6.inst : Not
      (@LT.lt UInt8 instLTUInt8
        (@Neg.neg UInt8 (@Lean.Grind.Ring.toNeg UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@OfNat.ofNat UInt8 (nat_lit 1)
            (@Lean.Grind.Semiring.ofNat UInt8
              (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
              (nat_lit 1))))
        (@OfNat.ofNat UInt8 (nat_lit 0)
          (@Zero.toOfNat0 UInt8
            (@Lean.Grind.AddCommMonoid.toZero UInt8
              (@Lean.Grind.NatModule.toAddCommMonoid UInt8
                (@Lean.Grind.Semiring.toNatModule UInt8
                  (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.neg_one_lt_zero.h6 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1],
        @LT.lt R inst_2
          (@Neg.neg R (@Lean.Grind.Ring.toNeg R inst)
            (@OfNat.ofNat R (nat_lit 1) (@Lean.Grind.Semiring.ofNat R (@Lean.Grind.Ring.toSemiring R inst) (nat_lit 1))))
          (@OfNat.ofNat R (nat_lit 0)
            (@Zero.toOfNat0 R
              (@Lean.Grind.AddCommMonoid.toZero R
                (@Lean.Grind.NatModule.toAddCommMonoid R
                  (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.neg_one_lt_zero.h6.inst (@hc_h (UInt8) (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (instLEUInt8) (instLTUInt8) _ _)

-- Lean.Grind.Order.lt_unsat, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_unsat.h3.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_unsat.h3.prem0 : 0 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_unsat.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst : Std.IsPreorder α] (a : α), a < a → False := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_unsat.h3.inst (@hc_h (Nat) (instLENat) ({ lt := fun (a b : Nat) => a ≤ b : LT Nat }) _ (0) HypCheckProof.Lean.Grind.Order.lt_unsat.h3.prem0)

-- Int.Internal.Linear.le_combine, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine.h4.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_combine.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_combine.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.le_combine.h4.prem0 HypCheckProof.Int.Internal.Linear.le_combine.h4.prem1)

-- Int.Internal.Linear.le_combine, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine.h5.prem0 : Int.Internal.Linear.le_combine_cert (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
        (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine.h5.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_combine.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.le_combine_cert p₁ p₂ p₃ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_combine.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.le_combine.h5.prem0 HypCheckProof.Int.Internal.Linear.le_combine.h5.prem1)

-- Int.Internal.Linear.le_combine, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine.h6.prem0 : Int.Internal.Linear.le_combine_cert (Int.Internal.Linear.Poly.num 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_combine.h6.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_combine.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.le_combine_cert p₁ p₂ p₃ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_combine.h6.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.le_combine.h6.prem0 HypCheckProof.Int.Internal.Linear.le_combine.h6.prem1)

-- Lean.Grind.no_int_zero_divisors, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.no_int_zero_divisors.h2.inst : Not
      (@Eq UInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
        (@OfNat.ofNat UInt8 (nat_lit 0)
          (@Zero.toOfNat0 UInt8
            (@Lean.Grind.AddCommMonoid.toZero UInt8
              (@Lean.Grind.NatModule.toAddCommMonoid UInt8
                (@Lean.Grind.IntModule.toNatModule UInt8
                  (@Lean.Grind.Ring.toIntModule UInt8
                    (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.no_int_zero_divisors.h2.prem0 : @Ne Int (@OfNat.ofNat Int (nat_lit 4) (@instOfNat (nat_lit 4))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.no_int_zero_divisors.h2.prem1 : @Eq UInt8
      (@HSMul.hSMul Int UInt8 UInt8
        (@instHSMul Int UInt8
          (@Lean.Grind.IntModule.zsmul UInt8
            (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (@OfNat.ofNat Int (nat_lit 4) (@instOfNat (nat_lit 4)))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))))
      (@OfNat.ofNat UInt8 (nat_lit 0)
        (@Zero.toOfNat0 UInt8
          (@Lean.Grind.AddCommMonoid.toZero UInt8
            (@Lean.Grind.NatModule.toAddCommMonoid UInt8
              (@Lean.Grind.IntModule.toNatModule UInt8
                (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.no_int_zero_divisors.h2 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] {k : Int} {a : α},
        @Ne Int k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          @Eq α (@HSMul.hSMul Int α α (@instHSMul Int α (@Lean.Grind.IntModule.zsmul α inst)) k a)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @Eq α a
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.no_int_zero_divisors.h2.inst (@hc_h (UInt8) (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)) (@OfNat.ofNat Int (nat_lit 4) (@instOfNat (nat_lit 4))) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) HypCheckProof.Lean.Grind.no_int_zero_divisors.h2.prem0 HypCheckProof.Lean.Grind.no_int_zero_divisors.h2.prem1)

-- Lean.Grind.no_int_zero_divisors, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.no_int_zero_divisors.h5.inst : Not
      (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.IntModule.toNatModule Int
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.no_int_zero_divisors.h5.prem0 : @Eq Int
      (@HSMul.hSMul Int Int Int
        (@instHSMul Int Int
          (@Lean.Grind.IntModule.zsmul Int
            (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.no_int_zero_divisors.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α]
        [inst_1 : @Lean.Grind.NoNatZeroDivisors α (@Lean.Grind.IntModule.toNatModule α inst)] {k : Int} {a : α},
        @Eq α (@HSMul.hSMul Int α α (@instHSMul Int α (@Lean.Grind.IntModule.zsmul α inst)) k a)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
          @Eq α a
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.no_int_zero_divisors.h5.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.no_int_zero_divisors.h5.prem0)

-- Lean.Grind.no_int_zero_divisors, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.no_int_zero_divisors.h6.inst : Not
      (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.IntModule.toNatModule Int
                  (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.no_int_zero_divisors.h6.prem0 : @Ne Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.no_int_zero_divisors.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α]
        [inst_1 : @Lean.Grind.NoNatZeroDivisors α (@Lean.Grind.IntModule.toNatModule α inst)] {k : Int} {a : α},
        @Ne Int k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          @Eq α a
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.no_int_zero_divisors.h6.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.no_int_zero_divisors.h6.prem0)

-- Lean.Grind.OrderedAdd.add_le_right_iff, hypothesis 4: necessary
/- FAILED: 5:174: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 } | 38:123: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_right_iff.h4.inst : ¬(0 % 2 ≤ 1 % 2 ↔ (1 + 0) % 2 ≤ (1 + 1) % 2) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_right_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M] {a b : M} (c : M),
        a ≤ b ↔ c + a ≤ c + b := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_le_right_iff.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) (0) (1) (1))
-/

-- Lean.Grind.CommRing.Stepwise.eq_mul, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.eq_mul.h6.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.eq_mul.h6.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.eq_mul.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly)
        (k : Int) (p : Lean.Grind.CommRing.Poly),
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
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.eq_mul.h6.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.eq_mul.h6.prem0)

-- Lean.Grind.CommRing.Stepwise.eq_mul, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.eq_mul.h7.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.eq_mul.h7.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.mul_cert
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.eq_mul.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly)
        (k : Int) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.mul_cert p₁ k p) Bool.true →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.eq_mul.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.eq_mul.h7.prem0)

-- Lean.Grind.CommRing.Stepwise.mul, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.mul.h6.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.mul.h6.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.mul.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly)
        (k : Int) (p : Lean.Grind.CommRing.Poly),
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
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.mul.h6.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.mul.h6.prem0)

-- Lean.Grind.CommRing.Stepwise.mul, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.mul.h7.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.mul.h7.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.mul_cert
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.mul.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly)
        (k : Int) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.mul_cert p₁ k p) Bool.true →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.mul.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.mul.h7.prem0)

-- Lean.Grind.CommRing.Poly.denote_substInvB_k, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_substInvB_k.h7.inst : Not
      (@Eq Rat
        (@Lean.Grind.CommRing.PolyQ.denote Rat Lean.Grind.instFieldRat
          (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).substInvB_k
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@Lean.Grind.CommRing.Poly.denote Rat
          (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
          (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_substInvB_k.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (ctx : Lean.Grind.CommRing.Context α) (p : Lean.Grind.CommRing.Poly) (x : Lean.Grind.CommRing.Var) (c : Nat),
        @Eq α (@Lean.Grind.CommRing.PolyQ.denote α inst ctx (p.substInvB_k x c))
          (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_substInvB_k.h7.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))

-- Lean.Grind.CommRing.Expr.eq_of_toPolyC_nc_eq, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_nc_eq.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_nc_eq.h3.prem0 : @Eq Bool
      (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toPolyC_nc_k
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).beq'
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).toPolyC_nc_k
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_nc_eq.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool ((a.toPolyC_nc_k c).beq' (b.toPolyC_nc_k c)) Bool.true →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α inst ctx a) (@Lean.Grind.CommRing.Expr.denote α inst ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_nc_eq.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_nc_eq.h3.prem0)

-- Lean.Grind.CommRing.Expr.eq_of_toPolyC_nc_eq, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_nc_eq.h7.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_nc_eq.h7 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Ring α]
        [inst_1 : @Lean.Grind.IsCharP α (@Lean.Grind.Ring.toSemiring α inst) c] (ctx : Lean.Grind.CommRing.Context α)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α inst ctx a) (@Lean.Grind.CommRing.Expr.denote α inst ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_nc_eq.h7.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))

-- Int.Internal.Linear.dvd_coeff, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_coeff.h6.inst : ¬0 ∣
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_coeff.h6.prem0 : 0 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_coeff.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (k₁ : Int) (p₁ : Int.Internal.Linear.Poly) (k₂ : Int)
        (p₂ : Int.Internal.Linear.Poly) (g : Int),
        k₁ ∣ Int.Internal.Linear.Poly.denote' ctx p₁ → k₂ ∣ Int.Internal.Linear.Poly.denote' ctx p₂ := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_coeff.h6.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) HypCheckProof.Int.Internal.Linear.dvd_coeff.h6.prem0)

-- Int.Internal.Linear.dvd_coeff, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_coeff.h7.inst : ¬0 ∣
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_coeff.h7.prem0 : Int.Internal.Linear.dvd_coeff_cert 0 (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) 0
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) 1 =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_coeff.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (k₁ : Int) (p₁ : Int.Internal.Linear.Poly) (k₂ : Int)
        (p₂ : Int.Internal.Linear.Poly) (g : Int),
        Int.Internal.Linear.dvd_coeff_cert k₁ p₁ k₂ p₂ g = Bool.true → k₂ ∣ Int.Internal.Linear.Poly.denote' ctx p₂ := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_coeff.h7.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (1) HypCheckProof.Int.Internal.Linear.dvd_coeff.h7.prem0)

-- Int.Internal.Linear.cooper_left_split_ineq, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.cooper_left_split_ineq.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.cooper_left_split_ineq.h6.prem0 : Int.Internal.Linear.cooper_left_split_ineq_cert (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (↑1) 1
        (Int.Internal.Linear.Poly.num 1) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.cooper_left_split_ineq.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly) (k : Nat) (b : Int)
        (p' : Int.Internal.Linear.Poly),
        Int.Internal.Linear.cooper_left_split_ineq_cert p₁ p₂ (↑k) b p' = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p' ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.cooper_left_split_ineq.h6.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (1) (1) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.cooper_left_split_ineq.h6.prem0)

-- Lean.Grind.CommRing.Expr.eq_of_denote_eq_toExpr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denote_eq_toExpr.h6.inst : Not
      (@Eq Int
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
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k)) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denote_eq_toExpr.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Expr b p.toExpr_k →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denote_eq_toExpr.h6.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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

-- Lean.Grind.CommRing.Expr.eq_of_denote_eq_toExpr, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denote_eq_toExpr.h7.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denote_eq_toExpr.h7.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denote_eq_toExpr.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denote_eq_toExpr.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denote_eq_toExpr.h7.prem0)

-- Lean.Grind.Field.NormNum.eq_mul_inv, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.eq_mul_inv.h6.inst : Not
      (@Eq Rat
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
        (@HMul.hMul Rat Rat Rat
          (@instHMul Rat
            (@Lean.Grind.Semiring.toMul Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@IntCast.intCast Rat
            (@Lean.Grind.Ring.intCast Rat
              (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
            (@NatCast.natCast Rat
              (@Lean.Grind.Semiring.natCast Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.eq_mul_inv.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (a : α) (v : Rat) (n : Int) (d : Nat),
        @Eq α a (@Lean.Grind.Field.NormNum.ofRat α inst v) →
          @Eq α a
            (@HMul.hMul α α α
              (@instHMul α
                (@Lean.Grind.Semiring.toMul α
                  (@Lean.Grind.CommSemiring.toSemiring α
                    (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
              (@IntCast.intCast α
                (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))) n)
              (@Inv.inv α (@Lean.Grind.Field.toInv α inst)
                (@NatCast.natCast α
                  (@Lean.Grind.Semiring.natCast α
                    (@Lean.Grind.CommSemiring.toSemiring α
                      (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
                  d)))) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.eq_mul_inv.h6.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) rfl)

-- Lean.Grind.Field.NormNum.eq_mul_inv, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.eq_mul_inv.h7.inst : Not
      (@Eq Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
        (@HMul.hMul Rat Rat Rat
          (@instHMul Rat
            (@Lean.Grind.Semiring.toMul Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@IntCast.intCast Rat
            (@Lean.Grind.Ring.intCast Rat
              (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
            (@NatCast.natCast Rat
              (@Lean.Grind.Semiring.natCast Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.eq_mul_inv.h7.prem0 : @Eq Bool
      ((@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq)
            (Rat.num (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).and
        (@BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
          (Rat.den (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Field.NormNum.eq_mul_inv.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (a : α) (v : Rat) (n : Int) (d : Nat),
        @Eq Bool
            ((@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) v.num n).and
              (@BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) v.den d))
            Bool.true →
          @Eq α a
            (@HMul.hMul α α α
              (@instHMul α
                (@Lean.Grind.Semiring.toMul α
                  (@Lean.Grind.CommSemiring.toSemiring α
                    (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
              (@IntCast.intCast α
                (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))) n)
              (@Inv.inv α (@Lean.Grind.Field.toInv α inst)
                (@NatCast.natCast α
                  (@Lean.Grind.Semiring.natCast α
                    (@Lean.Grind.CommSemiring.toSemiring α
                      (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
                  d)))) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.eq_mul_inv.h7.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Lean.Grind.Field.NormNum.eq_mul_inv.h7.prem0)

-- Lean.Grind.Linarith.imp_eq, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.imp_eq.h6.inst : Not
      (@Eq Int
        (@Lean.Grind.Linarith.Var.denote Int
          (@Lean.RArray.branch Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Lean.Grind.Linarith.Var.denote Int
          (@Lean.RArray.branch Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.imp_eq.h6.prem0 : @Eq Int
      (@Lean.Grind.Linarith.Poly.denote' Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.branch Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
        Lean.Grind.Linarith.Poly.nil)
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.imp_eq.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] (ctx : Lean.Grind.Linarith.Context α) (p : Lean.Grind.Linarith.Poly)
        (x y : Lean.Grind.Linarith.Var),
        @Eq α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
          @Eq α (@Lean.Grind.Linarith.Var.denote α ctx x) (@Lean.Grind.Linarith.Var.denote α ctx y)) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.imp_eq.h6.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@Lean.RArray.branch Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))))) (Lean.Grind.Linarith.Poly.nil) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Lean.Grind.Linarith.imp_eq.h6.prem0)

-- Lean.Grind.Linarith.imp_eq, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.imp_eq.h7.inst : Not
      (@Eq Int
        (@Lean.Grind.Linarith.Var.denote Int
          (@Lean.RArray.branch Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Lean.Grind.Linarith.Var.denote Int
          (@Lean.RArray.branch Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.imp_eq.h7.prem0 : @Eq Bool
      (Lean.Grind.Linarith.imp_eq_cert
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (Lean.Grind.Linarith.Poly.add
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 1) (instOfNatNat (nat_lit 1))) Lean.Grind.Linarith.Poly.nil))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.imp_eq.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] (ctx : Lean.Grind.Linarith.Context α) (p : Lean.Grind.Linarith.Poly)
        (x y : Lean.Grind.Linarith.Var),
        @Eq Bool (Lean.Grind.Linarith.imp_eq_cert p x y) Bool.true →
          @Eq α (@Lean.Grind.Linarith.Var.denote α ctx x) (@Lean.Grind.Linarith.Var.denote α ctx y)) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.imp_eq.h7.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@Lean.RArray.branch Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 1) (instOfNatNat (nat_lit 1))) Lean.Grind.Linarith.Poly.nil)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Lean.Grind.Linarith.imp_eq.h7.prem0)

-- Lean.Grind.CommRing.Poly.denoteList_cancelTerms_k, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteList_cancelTerms_k.h7.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denoteList Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.cancelTerms_k
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))
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
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteList_cancelTerms_k.h7.prem0 : @Ne Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteList_cancelTerms_k.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (p : Lean.Grind.CommRing.Poly)
        (c : Int) (x : Lean.Grind.CommRing.Var),
        @Ne Int c (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          @Eq α
            (@Lean.Grind.CommRing.Poly.denoteList α (@Lean.Grind.CommRing.toRing α inst) ctx
              (Lean.Grind.CommRing.Poly.cancelTerms_k c x p))
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denoteList_cancelTerms_k.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Lean.Grind.CommRing.Poly.denoteList_cancelTerms_k.h7.prem0)

-- Lean.Grind.OrderedAdd.le_neg_iff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.le_neg_iff.h4.inst : ¬(UInt8.ofNat 0 ≤ -UInt8.ofNat 1 ↔ UInt8.ofNat 1 ≤ -UInt8.ofNat 0) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.le_neg_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommGroup M] {a b : M}, a ≤ -b ↔ b ≤ -a := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.le_neg_iff.h4.inst (@hc_h (UInt8) (instLEUInt8) _ (Lean.Grind.Ring.toAddCommGroup) (UInt8.ofNat 0) (UInt8.ofNat 1))

-- Lean.Grind.Order.le_eq_true_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt.h3.inst : ¬(1 ≤ 0) = True := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt.h3.prem0 : 1 ≠ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] {a b : α}, a < b → (a ≤ b) = True := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt.h3.inst (@hc_h (Nat) (instLENat) ({ lt := fun (a b : Nat) => a ≠ b : LT Nat }) (1) (0) HypCheckProof.Lean.Grind.Order.le_eq_true_of_lt.h3.prem0)

-- Lean.Grind.Field.NormNum.inv_eq, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.inv_eq.h5.inst : Not
      (@Eq Rat
        (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.inv_eq.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (a : α) (v₁ v : Rat),
        @Eq α a (@Lean.Grind.Field.NormNum.ofRat α inst v₁) →
          @Eq α (@Inv.inv α (@Lean.Grind.Field.toInv α inst) a) (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.inv_eq.h5.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) rfl)

-- Lean.Grind.Field.NormNum.inv_eq, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.inv_eq.h6.inst : Not
      (@Eq Rat
        (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.inv_eq.h6.prem0 : @Eq Bool
      (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat)
        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@Inv.inv Rat Rat.instInv (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
      Bool.true := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.inv_eq.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (a : α) (v₁ v : Rat),
        @Eq Bool (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat) v (@Inv.inv Rat Rat.instInv v₁)) Bool.true →
          @Eq α (@Inv.inv α (@Lean.Grind.Field.toInv α inst) a) (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.inv_eq.h6.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Field.NormNum.inv_eq.h6.prem0)

-- Lean.Grind.Field.NormNum.neg_eq, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.neg_eq.h5.inst : Not
      (@Eq Rat
        (@Neg.neg Rat
          (@Lean.Grind.Ring.toNeg Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.neg_eq.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (a : α) (v₁ v : Rat),
        @Eq α a (@Lean.Grind.Field.NormNum.ofRat α inst v₁) →
          @Eq α
            (@Neg.neg α (@Lean.Grind.Ring.toNeg α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))) a)
            (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.neg_eq.h5.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) rfl)

-- Lean.Grind.Field.NormNum.neg_eq, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.neg_eq.h6.inst : Not
      (@Eq Rat
        (@Neg.neg Rat
          (@Lean.Grind.Ring.toNeg Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.neg_eq.h6.prem0 : @Eq Bool
      (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat)
        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@Neg.neg Rat Rat.instNeg (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Field.NormNum.neg_eq.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (a : α) (v₁ v : Rat),
        @Eq Bool (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat) v (@Neg.neg Rat Rat.instNeg v₁)) Bool.true →
          @Eq α
            (@Neg.neg α (@Lean.Grind.Ring.toNeg α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))) a)
            (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.neg_eq.h6.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Field.NormNum.neg_eq.h6.prem0)

-- Lean.Grind.Field.NormNum.eq_int, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.eq_int.h5.inst : Not
      (@Eq Rat
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
        (@IntCast.intCast Rat
          (@Lean.Grind.Ring.intCast Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.eq_int.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (a : α) (v : Rat) (n : Int),
        @Eq α a (@Lean.Grind.Field.NormNum.ofRat α inst v) →
          @Eq α a
            (@IntCast.intCast α
              (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))) n)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.eq_int.h5.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) rfl)

-- Lean.Grind.Field.NormNum.eq_int, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.eq_int.h6.inst : Not
      (@Eq Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
        (@IntCast.intCast Rat
          (@Lean.Grind.Ring.intCast Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.eq_int.h6.prem0 : @Eq Bool
      ((@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (Rat.num (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))).and
        (@BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
          (Rat.den (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Field.NormNum.eq_int.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (a : α) (v : Rat) (n : Int),
        @Eq Bool
            ((@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) n v.num).and
              (@BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) v.den
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bool.true →
          @Eq α a
            (@IntCast.intCast α
              (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))) n)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.eq_int.h6.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Field.NormNum.eq_int.h6.prem0)

-- Lean.Grind.Field.NormNum.eq_inv, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.eq_inv.h5.inst : Not
      (@Eq Rat
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
        (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
          (@NatCast.natCast Rat
            (@Lean.Grind.Semiring.natCast Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.eq_inv.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (a : α) (v : Rat) (d : Nat),
        @Eq α a (@Lean.Grind.Field.NormNum.ofRat α inst v) →
          @Eq α a
            (@Inv.inv α (@Lean.Grind.Field.toInv α inst)
              (@NatCast.natCast α
                (@Lean.Grind.Semiring.natCast α
                  (@Lean.Grind.CommSemiring.toSemiring α
                    (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
                d))) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.eq_inv.h5.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) rfl)

-- Lean.Grind.Field.NormNum.eq_inv, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.eq_inv.h6.inst : Not
      (@Eq Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
          (@NatCast.natCast Rat
            (@Lean.Grind.Semiring.natCast Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.eq_inv.h6.prem0 : @Eq Bool
      ((@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq)
            (Rat.num (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).and
        (@BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
          (Rat.den (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Field.NormNum.eq_inv.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (a : α) (v : Rat) (d : Nat),
        @Eq Bool
            ((@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) v.num
                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).and
              (@BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat) v.den d))
            Bool.true →
          @Eq α a
            (@Inv.inv α (@Lean.Grind.Field.toInv α inst)
              (@NatCast.natCast α
                (@Lean.Grind.Semiring.natCast α
                  (@Lean.Grind.CommSemiring.toSemiring α
                    (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
                d))) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.eq_inv.h6.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Lean.Grind.Field.NormNum.eq_inv.h6.prem0)

-- Int.Internal.Linear.eq_of_le_ge, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h3.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num (-1)) = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h3.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num (-1)) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h3.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₁ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num (-1)) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h3.prem0 HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h3.prem1)

-- Int.Internal.Linear.eq_of_le_ge, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h4.prem0 : Int.Internal.Linear.eq_of_le_ge_cert (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.num (-1)) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h4.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num (-1)) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.eq_of_le_ge_cert p₁ p₂ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₁ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.num (-1)) HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h4.prem0 HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h4.prem1)

-- Int.Internal.Linear.eq_of_le_ge, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num (-1)) = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h5.prem0 : Int.Internal.Linear.eq_of_le_ge_cert (Int.Internal.Linear.Poly.num (-1)) (Int.Internal.Linear.Poly.num 1) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h5.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num (-1)) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.eq_of_le_ge_cert p₁ p₂ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₁ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num (-1)) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h5.prem0 HypCheckProof.Int.Internal.Linear.eq_of_le_ge.h5.prem1)

-- Lean.Grind.CommRing.Expr.denote_toPP_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPP_k.h6.inst : ¬Lean.Grind.CommRing.PPoly.denote (fun (a : Nat) => -1) 2
          (Lean.Grind.CommRing.Expr.toPP_k 2 ((Lean.Grind.CommRing.Expr.var 0).mul (Lean.Grind.CommRing.Expr.var 0))) =
        Lean.Grind.CommRing.Expr.denoteF (fun (a : Nat) => -1)
          ((Lean.Grind.CommRing.Expr.var 0).mul (Lean.Grind.CommRing.Expr.var 0)) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPP_k.h6.prem0 : 1 < 2 := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPP_k.h6 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Nat → α) (B : Nat),
        1 < B →
          ∀ (e : Lean.Grind.CommRing.Expr),
            Lean.Grind.CommRing.PPoly.denote ctx B (Lean.Grind.CommRing.Expr.toPP_k B e) =
              Lean.Grind.CommRing.Expr.denoteF ctx e := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPP_k.h6.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (fun (a : Nat) => -1) (2) HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPP_k.h6.prem0 ((Lean.Grind.CommRing.Expr.var 0).mul (Lean.Grind.CommRing.Expr.var 0)))

-- Lean.Grind.Field.natCast_div_of_dvd, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.natCast_div_of_dvd.h4.inst : Not
      (@Eq Rat
        (@Nat.cast Rat
          (@Lean.Grind.Semiring.natCast Rat
            (@Lean.Grind.CommSemiring.toSemiring Rat
              (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
          (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat (@Lean.Grind.Field.toDiv Rat Lean.Grind.instFieldRat))
          (@Nat.cast Rat
            (@Lean.Grind.Semiring.natCast Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Nat.cast Rat
            (@Lean.Grind.Semiring.natCast Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.natCast_div_of_dvd.h4.prem0 : @Ne Rat
      (@Nat.cast Rat
        (@Lean.Grind.Semiring.natCast Rat
          (@Lean.Grind.CommSemiring.toSemiring Rat
            (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@OfNat.ofNat Rat (nat_lit 0)
        (@Zero.toOfNat0 Rat
          (@Lean.Grind.AddCommMonoid.toZero Rat
            (@Lean.Grind.NatModule.toAddCommMonoid Rat
              (@Lean.Grind.Semiring.toNatModule Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Field.natCast_div_of_dvd.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] {x y : Nat},
        @Ne α
            (@Nat.cast α
              (@Lean.Grind.Semiring.natCast α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
              y)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α
                        (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))))) →
          @Eq α
            (@Nat.cast α
              (@Lean.Grind.Semiring.natCast α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
              (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) x y))
            (@HDiv.hDiv α α α (@instHDiv α (@Lean.Grind.Field.toDiv α inst))
              (@Nat.cast α
                (@Lean.Grind.Semiring.natCast α
                  (@Lean.Grind.CommSemiring.toSemiring α
                    (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
                x)
              (@Nat.cast α
                (@Lean.Grind.Semiring.natCast α
                  (@Lean.Grind.CommSemiring.toSemiring α
                    (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
                y))) := fun hc_h => HypCheckProof.Lean.Grind.Field.natCast_div_of_dvd.h4.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) HypCheckProof.Lean.Grind.Field.natCast_div_of_dvd.h4.prem0)

-- Lean.Grind.ne_of_beq_eq_false, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.ne_of_beq_eq_false.h2.inst : ¬(0 = 0) = False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.ne_of_beq_eq_false.h2.prem0 : (0 != 0) = Bool.false := by
  decide
theorem HypCheckProof.Lean.Grind.ne_of_beq_eq_false.h2 : ¬∀ {α : Type} {x : BEq α} {a b : α}, (a == b) = Bool.false → (a = b) = False := fun hc_h => HypCheckProof.Lean.Grind.ne_of_beq_eq_false.h2.inst (@hc_h (Nat) ({ beq := fun (a b : Nat) => a != b : BEq Nat }) (0) (0) HypCheckProof.Lean.Grind.ne_of_beq_eq_false.h2.prem0)

-- Lean.Grind.AC.Seq.denote_union, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_union.h2.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a b : Bool) => !(a && b) :
            Lean.Grind.AC.Context Bool }
          ((Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)).union
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
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_union.h2.prem0 : Std.Commutative
      { vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a b : Bool) => !(a && b) :
          Lean.Grind.AC.Context Bool }.op := (@Std.Commutative.mk _ _ (by (try dsimp only);   decide))
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_union.h2 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₂ : Std.Commutative ctx.op} (s₁ s₂ : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx (s₁.union s₂) =
          ctx.op (Lean.Grind.AC.Seq.denote ctx s₁) (Lean.Grind.AC.Seq.denote ctx s₂) := fun hc_h => HypCheckProof.Lean.Grind.AC.Seq.denote_union.h2.inst (@hc_h (Bool) ({ vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a b : Bool) => !(a && b) :
      Lean.Grind.AC.Context Bool }) HypCheckProof.Lean.Grind.AC.Seq.denote_union.h2.prem0 (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)))

-- Lean.Grind.AC.Seq.denote_union, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_union.h3.inst : ¬Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          ((Lean.Grind.AC.Seq.var 1).union (Lean.Grind.AC.Seq.var 0)) =
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
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_union.h3.prem0 : Std.Associative
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   (intros; simp_all; done)))
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_union.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op} (s₁ s₂ : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx (s₁.union s₂) =
          ctx.op (Lean.Grind.AC.Seq.denote ctx s₁) (Lean.Grind.AC.Seq.denote ctx s₂) := fun hc_h => HypCheckProof.Lean.Grind.AC.Seq.denote_union.h3.inst (@hc_h (Nat) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
      op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.Seq.denote_union.h3.prem0 (Lean.Grind.AC.Seq.var 1) (Lean.Grind.AC.Seq.var 0))

-- Lean.Grind.AC.Seq.denote_sort', hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_sort'.h2.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a b : Bool) => !(a && b) :
            Lean.Grind.AC.Context Bool }
          ((Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)).sort'
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
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_sort'.h2.prem0 : Std.Commutative
      { vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a b : Bool) => !(a && b) :
          Lean.Grind.AC.Context Bool }.op := (@Std.Commutative.mk _ _ (by (try dsimp only);   decide))
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_sort'.h2 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₂ : Std.Commutative ctx.op} (s acc : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx (s.sort' acc) =
          ctx.op (Lean.Grind.AC.Seq.denote ctx s) (Lean.Grind.AC.Seq.denote ctx acc) := fun hc_h => HypCheckProof.Lean.Grind.AC.Seq.denote_sort'.h2.inst (@hc_h (Bool) ({ vars := Lean.RArray.leaf { down := Bool.true : PLift Bool }, op := fun (a b : Bool) => !(a && b) :
      Lean.Grind.AC.Context Bool }) HypCheckProof.Lean.Grind.AC.Seq.denote_sort'.h2.prem0 (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)))

-- Lean.Grind.AC.Seq.denote_sort', hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_sort'.h3.inst : ¬Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          ((Lean.Grind.AC.Seq.var 1).sort' (Lean.Grind.AC.Seq.var 0)) =
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
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_sort'.h3.prem0 : Std.Associative
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   (intros; simp_all; done)))
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_sort'.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op} (s acc : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx (s.sort' acc) =
          ctx.op (Lean.Grind.AC.Seq.denote ctx s) (Lean.Grind.AC.Seq.denote ctx acc) := fun hc_h => HypCheckProof.Lean.Grind.AC.Seq.denote_sort'.h3.inst (@hc_h (Nat) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
      op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.Seq.denote_sort'.h3.prem0 (Lean.Grind.AC.Seq.var 1) (Lean.Grind.AC.Seq.var 0))

-- Lean.Grind.eq_of_beq_eq_true, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.eq_of_beq_eq_true.h2.inst : ¬0 = 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.eq_of_beq_eq_true.h2.prem0 : (0 / 2 == 1 / 2) = Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.eq_of_beq_eq_true.h2 : ¬∀ {α : Type} {x : BEq α} {a b : α}, (a == b) = Bool.true → a = b := fun hc_h => HypCheckProof.Lean.Grind.eq_of_beq_eq_true.h2.inst (@hc_h (Nat) ({ beq := fun (a b : Nat) => a / 2 == b / 2 : BEq Nat }) (0) (1) HypCheckProof.Lean.Grind.eq_of_beq_eq_true.h2.prem0)

-- Int.Internal.Linear.norm_eq, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.norm_eq.h4.inst : ¬(Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
          Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        (Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
          0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.norm_eq.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        (Int.Internal.Linear.Expr.denote ctx lhs = Int.Internal.Linear.Expr.denote ctx rhs) =
          (Int.Internal.Linear.Poly.denote' ctx p = 0) := fun hc_h => HypCheckProof.Int.Internal.Linear.norm_eq.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)))

-- Lean.Grind.CommRing.Expr.denoteS_num_of_nonneg, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_num_of_nonneg.h4.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        (@Lean.Grind.CommRing.denoteSInt Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_num_of_nonneg.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α) (k : Int),
        @Eq α (@Lean.Grind.CommRing.Expr.denoteS α inst ctx (Lean.Grind.CommRing.Expr.num k))
          (@Lean.Grind.CommRing.denoteSInt α inst k)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denoteS_num_of_nonneg.h4.inst (@hc_h (Int) (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))

-- Lean.Grind.CommRing.Poly.denoteS_toExpr, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_toExpr.h4.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num
              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))).toExpr)
        (@Lean.Grind.CommRing.Poly.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.num
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_toExpr.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denoteS α inst ctx p.toExpr) (@Lean.Grind.CommRing.Poly.denoteS α inst ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_toExpr.h4.inst (@hc_h (Int) (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))

-- Int.Internal.Linear.le_eq_false, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_eq_false.h3.inst : ¬(Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) ≤
          Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        False := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_eq_false.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr),
        (Int.Internal.Linear.Expr.denote ctx lhs ≤ Int.Internal.Linear.Expr.denote ctx rhs) = False := fun hc_h => HypCheckProof.Int.Internal.Linear.le_eq_false.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0))

-- Int.Internal.Linear.dvd_eq_false, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_eq_false.h3.inst : ¬(0 ∣ Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) = False := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_eq_false.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (k : Int) (e : Int.Internal.Linear.Expr),
        (k ∣ Int.Internal.Linear.Expr.denote ctx e) = False := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_eq_false.h3.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Expr.num 0))

-- Int.Internal.Linear.Poly.denote_div_eq_of_divCoeffs, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.Poly.denote_div_eq_of_divCoeffs.h3.inst : ¬Int.Internal.Linear.Poly.denote (Lean.RArray.leaf 1)
              (Int.Internal.Linear.Poly.div 0 (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) *
            0 +
          Int.Internal.Linear.cmod (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).getConst 0 =
        Int.Internal.Linear.Poly.denote (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.Poly.denote_div_eq_of_divCoeffs.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p : Int.Internal.Linear.Poly) (k : Int),
        Int.Internal.Linear.Poly.denote ctx (Int.Internal.Linear.Poly.div k p) * k + Int.Internal.Linear.cmod p.getConst k =
          Int.Internal.Linear.Poly.denote ctx p := fun hc_h => HypCheckProof.Int.Internal.Linear.Poly.denote_div_eq_of_divCoeffs.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0))

-- Int.Internal.Linear.Expr.eq_of_norm_eq, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.Expr.eq_of_norm_eq.h3.inst : ¬Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.Expr.eq_of_norm_eq.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (e : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Expr.denote ctx e = Int.Internal.Linear.Poly.denote' ctx p := fun hc_h => HypCheckProof.Int.Internal.Linear.Expr.eq_of_norm_eq.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)))

-- Int.Internal.Linear.lt_false_of_norm_eq_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.lt_false_of_norm_eq_k.h3.inst : ¬(Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) <
          Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0)) =
        False := by
  decide
theorem HypCheckProof.Int.Internal.Linear.lt_false_of_norm_eq_k.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr),
        (Int.Internal.Linear.Expr.denote_k ctx lhs < Int.Internal.Linear.Expr.denote_k ctx rhs) = False := fun hc_h => HypCheckProof.Int.Internal.Linear.lt_false_of_norm_eq_k.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.var 0))

-- Int.Internal.Linear.Expr.eq_of_norm_eq_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.Expr.eq_of_norm_eq_k.h3.inst : ¬Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.Expr.eq_of_norm_eq_k.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (e : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Expr.denote_k ctx e = Int.Internal.Linear.Poly.denote' ctx p := fun hc_h => HypCheckProof.Int.Internal.Linear.Expr.eq_of_norm_eq_k.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)))

-- Int.Internal.Linear.eq_eq_true, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_true.h3.inst : ¬(Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
          Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0)) =
        True := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_eq_true.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr),
        (Int.Internal.Linear.Expr.denote ctx lhs = Int.Internal.Linear.Expr.denote ctx rhs) = True := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_eq_true.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.var 0))

-- Int.Internal.Linear.dvd_eq_false_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_eq_false_k.h3.inst : ¬(0 ∣ Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) = False := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_eq_false_k.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (k : Int) (e : Int.Internal.Linear.Expr),
        (k ∣ Int.Internal.Linear.Expr.denote_k ctx e) = False := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_eq_false_k.h3.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Expr.num 0))

-- Int.Internal.Linear.dvd_of_eq_zero, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_of_eq_zero.h3.inst : ¬0 ∣
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_of_eq_zero.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (d : Int) (p : Int.Internal.Linear.Poly),
        d ∣ Int.Internal.Linear.Poly.denote' ctx p := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_of_eq_zero.h3.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)))

-- Int.Internal.Linear.le_true_of_norm_eq_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_true_of_norm_eq_k.h3.inst : ¬(Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0) ≤
          Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        True := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_true_of_norm_eq_k.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr),
        (Int.Internal.Linear.Expr.denote_k ctx lhs ≤ Int.Internal.Linear.Expr.denote_k ctx rhs) = True := fun hc_h => HypCheckProof.Int.Internal.Linear.le_true_of_norm_eq_k.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0) (Int.Internal.Linear.Expr.num 0))

-- Int.Internal.Linear.Expr.eq_of_norm_expr_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.Expr.eq_of_norm_expr_k.h3.inst : ¬Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
        Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.Expr.eq_of_norm_expr_k.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (e e' : Int.Internal.Linear.Expr),
        Int.Internal.Linear.Expr.denote_k ctx e = Int.Internal.Linear.Expr.denote_k ctx e' := fun hc_h => HypCheckProof.Int.Internal.Linear.Expr.eq_of_norm_expr_k.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.var 0))

-- Lean.Grind.Ring.intCast_eq_ofNat_of_nonpos, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Ring.intCast_eq_ofNat_of_nonpos.h3.inst : Not
      (@Eq Int
        (@IntCast.intCast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@Neg.neg Int (@Lean.Grind.Ring.toNeg Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (Int.natAbs (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@Lean.Grind.Semiring.ofNat Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (Int.natAbs (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Ring.intCast_eq_ofNat_of_nonpos.h3 : Not
      (∀ {α : Type} [inst : Lean.Grind.Ring α] (x : Int),
        @Eq α (@IntCast.intCast α (@Lean.Grind.Ring.intCast α inst) x)
          (@Neg.neg α (@Lean.Grind.Ring.toNeg α inst)
            (@OfNat.ofNat α x.natAbs (@Lean.Grind.Semiring.ofNat α (@Lean.Grind.Ring.toSemiring α inst) x.natAbs)))) := fun hc_h => HypCheckProof.Lean.Grind.Ring.intCast_eq_ofNat_of_nonpos.h3.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))

-- Lean.Grind.Field.mul_inv_cancel, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.mul_inv_cancel.h3.inst : Not
      (@Eq Rat
        (@HMul.hMul Rat Rat Rat
          (@instHMul Rat
            (@Lean.Grind.Semiring.toMul Rat
              (@Lean.Grind.Ring.toSemiring Rat
                (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Rat (nat_lit 1)
          (@Lean.Grind.Semiring.ofNat Rat
            (@Lean.Grind.Ring.toSemiring Rat
              (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))
            (nat_lit 1)))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.mul_inv_cancel.h3 : Not
      (∀ {α : Type} [self : Lean.Grind.Field α] {a : α},
        @Eq α
          (@HMul.hMul α α α
            (@instHMul α
              (@Lean.Grind.Semiring.toMul α
                (@Lean.Grind.Ring.toSemiring α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α self)))))
            a (@Inv.inv α (@Lean.Grind.Field.toInv α self) a))
          (@OfNat.ofNat α (nat_lit 1)
            (@Lean.Grind.Semiring.ofNat α
              (@Lean.Grind.Ring.toSemiring α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α self)))
              (nat_lit 1)))) := fun hc_h => HypCheckProof.Lean.Grind.Field.mul_inv_cancel.h3.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.CommRing.Mon.eq_of_revlexFuel, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Mon.eq_of_revlexFuel.h3.inst : ¬Lean.Grind.CommRing.Mon.unit =
        Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit := by
  simp
theorem HypCheckProof.Lean.Grind.CommRing.Mon.eq_of_revlexFuel.h3 : ¬∀ {fuel : Nat} {m₁ m₂ : Lean.Grind.CommRing.Mon}, m₁ = m₂ := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Mon.eq_of_revlexFuel.h3.inst (@hc_h (0) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit))

-- Lean.Grind.CommRing.norm_int_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.norm_int_k.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Poly.denote'_k Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.norm_int_k.h3 : Not
      (∀ (ctx : Lean.Grind.CommRing.Context Int) (e : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Int (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) ctx e)
          (@Lean.Grind.CommRing.Poly.denote'_k Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.norm_int_k.h3.inst (@hc_h (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))

-- Lean.Grind.CommRing.norm_int, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.norm_int.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Poly.denote' Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.norm_int.h3 : Not
      (∀ (ctx : Lean.Grind.CommRing.Context Int) (e : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Int (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) ctx e)
          (@Lean.Grind.CommRing.Poly.denote' Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.norm_int.h3.inst (@hc_h (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))

-- Lean.Grind.CommRing.Mon.degreeOf_cancelVar, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Mon.degreeOf_cancelVar.h3.inst : ¬((Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit).cancelVar
              0).degreeOf
          0 =
        (Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit).degreeOf
          0 := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Mon.degreeOf_cancelVar.h3 : ¬∀ (m : Lean.Grind.CommRing.Mon) (x y : Lean.Grind.CommRing.Var), (m.cancelVar x).degreeOf y = m.degreeOf y := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Mon.degreeOf_cancelVar.h3.inst (@hc_h (Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit) (0) (0))

-- Lean.Grind.CommRing.Expr.of_degOk_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.of_degOk_k.h3.inst : ¬(1 < 0 ∧ (Lean.Grind.CommRing.Expr.num 0).degB_k < 0 ∧ (Lean.Grind.CommRing.Expr.num 0).degB_k < 0) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.of_degOk_k.h3 : ¬∀ {B : Nat} {a b : Lean.Grind.CommRing.Expr}, 1 < B ∧ a.degB_k < B ∧ b.degB_k < B := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.of_degOk_k.h3.inst (@hc_h (0) (Lean.Grind.CommRing.Expr.num 0) (Lean.Grind.CommRing.Expr.num 0))

-- Lean.Grind.CommRing.Expr.of_degSOk_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.of_degSOk_k.h3.inst : ¬(Bool.rec Bool.false (Lean.Grind.CommRing.Expr.num 0).semi_k (Lean.Grind.CommRing.Expr.num 0).semi_k = Bool.true ∧
        Lean.Grind.CommRing.Expr.degOk_k 0 (Lean.Grind.CommRing.Expr.num 0) (Lean.Grind.CommRing.Expr.num 0) = Bool.true) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.of_degSOk_k.h3 : ¬∀ {B : Nat} {a b : Lean.Grind.CommRing.Expr},
        Bool.rec Bool.false b.semi_k a.semi_k = Bool.true ∧ Lean.Grind.CommRing.Expr.degOk_k B a b = Bool.true := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.of_degSOk_k.h3.inst (@hc_h (0) (Lean.Grind.CommRing.Expr.num 0) (Lean.Grind.CommRing.Expr.num 0))

-- Lean.Grind.CommRing.Expr.kronQLin_eq_evalQ, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.kronQLin_eq_evalQ.h3.inst : ¬Lean.Grind.CommRing.Expr.kronQLin_k 0 [] (Lean.Grind.CommRing.Expr.var 0) =
        Lean.Grind.CommRing.Expr.evalQ [] (Lean.Grind.CommRing.Expr.var 0) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.kronQLin_eq_evalQ.h3 : ¬∀ (K : Nat) (invs : Lean.Grind.CommRing.InvVars) (e : Lean.Grind.CommRing.Expr),
        Lean.Grind.CommRing.Expr.kronQLin_k K invs e = Lean.Grind.CommRing.Expr.evalQ invs e := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.kronQLin_eq_evalQ.h3.inst (@hc_h (0) ([]) (Lean.Grind.CommRing.Expr.var 0))

-- Lean.Grind.AC.Expr.denote_toSeq, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Expr.denote_toSeq.h2.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)).op (Lean.Grind.AC.Expr.var 0)).toSeq =
        Lean.Grind.AC.Expr.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)).op (Lean.Grind.AC.Expr.var 0)) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.Expr.denote_toSeq.h2 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (e : Lean.Grind.AC.Expr),
        Lean.Grind.AC.Seq.denote ctx e.toSeq = Lean.Grind.AC.Expr.denote ctx e := fun hc_h => HypCheckProof.Lean.Grind.AC.Expr.denote_toSeq.h2.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)).op (Lean.Grind.AC.Expr.var 0)))

-- Lean.Grind.Order.le_eq_true, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true.h2.inst : ¬False = True := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_true.h2 : ¬∀ {α : Type} [inst : LE α] {a : α}, (a ≤ a) = True := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_true.h2.inst (@hc_h (Bool) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (Bool.false))

