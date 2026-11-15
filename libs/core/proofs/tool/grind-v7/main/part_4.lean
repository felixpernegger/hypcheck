import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.CommRing.lt_cancel_of_kronLinS, hypothesis 19: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h19.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h19.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h19.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h19.prem2 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h19.prem3 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h19.prem4 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h19 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.LawfulOrderLT α inst_3 inst_2] [inst_5 : @Std.IsPreorder α inst_2]
        [inst_6 : @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α inst) inst_2 inst_3 inst_5]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b a' b' c : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k (a'.add c)) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a (a'.add c)) Bool.true →
            @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K a) (Lean.Grind.CommRing.Expr.kronLinEval_k K (a'.add c)) →
              @Eq Bool (b.linSOk_k (b'.add c)) Bool.true →
                @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K b) (Lean.Grind.CommRing.Expr.kronLinEval_k K (b'.add c)) →
                  @Eq Prop
                    (@LT.lt α inst_3
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
                    (@LT.lt α inst_3
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a')
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h19.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h19.prem0 HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h19.prem1 HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h19.prem2 HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h19.prem3 HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h19.prem4)

-- Lean.Grind.CommRing.lt_cancel_of_kronLinS, hypothesis 20: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h20.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h20.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h20.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h20.prem2 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h20.prem3 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h20.prem4 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h20 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        [inst_2 : LE α] [inst_3 : LT α] [inst_4 : @Std.LawfulOrderLT α inst_3 inst_2] [inst_5 : @Std.IsPreorder α inst_2]
        [inst_6 : @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α inst) inst_2 inst_3 inst_5]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b a' b' c : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k (a'.add c)) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a (a'.add c)) Bool.true →
            @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K a) (Lean.Grind.CommRing.Expr.kronLinEval_k K (a'.add c)) →
              @Eq Bool (b.linSOk_k (b'.add c)) Bool.true →
                @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K b (b'.add c)) Bool.true →
                  @Eq Prop
                    (@LT.lt α inst_3
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
                    (@LT.lt α inst_3
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a')
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h20.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h20.prem0 HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h20.prem1 HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h20.prem2 HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h20.prem3 HypCheckProof.Lean.Grind.CommRing.lt_cancel_of_kronLinS.h20.prem4)

-- Lean.Grind.CommRing.eq_of_kronQLin_rel, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h9.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h9.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h9.prem2 : @Eq Bool
      (Lean.Grind.CommRing.Expr.linQOk_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h9.prem3 : @Eq Bool
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h9.prem4 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQLinEq_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
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
                      (@Eq α
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx lhs)
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs))
                      (@Eq α
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx lhs')
                        (@Lean.Grind.CommRing.Expr.denote α
                          (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h9.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h9.prem0 HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h9.prem1 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h9.prem2 HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h9.prem3 HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h9.prem4)

-- Lean.Grind.CommRing.eq_of_kronQLin_rel, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h15.inst : Not
      (@Eq Prop
        (@Eq Rat
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Eq Rat
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h15.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h15.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h15.prem2 : @Eq Bool
      (Nat.blt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h15.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.linQOk_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h15.prem4 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQLinEq_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h15 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
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
                        (@Eq α
                          (@Lean.Grind.CommRing.Expr.denote α
                            (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx lhs)
                          (@Lean.Grind.CommRing.Expr.denote α
                            (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs))
                        (@Eq α
                          (@Lean.Grind.CommRing.Expr.denote α
                            (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx lhs')
                          (@Lean.Grind.CommRing.Expr.denote α
                            (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h15.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h15.prem0 HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h15.prem1 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h15.prem2 (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h15.prem3 HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h15.prem4)

-- Lean.Grind.CommRing.eq_of_kronQLin_rel, hypothesis 16: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h16.inst : Not
      (@Eq Prop
        (@Eq Rat
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Eq Rat
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h16.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h16.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h16.prem2 : @Eq Bool
      (Nat.blt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h16.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.linQOk_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h16.prem4 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mul
          (Lean.Grind.CommRing.Expr.num
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h16 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
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
                        (@Eq α
                          (@Lean.Grind.CommRing.Expr.denote α
                            (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx lhs)
                          (@Lean.Grind.CommRing.Expr.denote α
                            (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs))
                        (@Eq α
                          (@Lean.Grind.CommRing.Expr.denote α
                            (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx lhs')
                          (@Lean.Grind.CommRing.Expr.denote α
                            (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h16.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h16.prem0 HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h16.prem1 (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h16.prem2 (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h16.prem3 HypCheckProof.Lean.Grind.CommRing.eq_of_kronQLin_rel.h16.prem4)

-- Lean.Grind.CommRing.eq_cancel_of_kronLinS, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h11.inst : Not
      (@Eq Prop
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h11.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h11.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h11.prem2 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h11.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h11.prem4 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b a' b' c : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k (a'.add c)) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K a) (Lean.Grind.CommRing.Expr.kronLinEval_k K (a'.add c)) →
            @Eq Bool (b.linSOk_k (b'.add c)) Bool.true →
              @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K b (b'.add c)) Bool.true →
                @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K b) (Lean.Grind.CommRing.Expr.kronLinEval_k K (b'.add c)) →
                  @Eq Prop
                    (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
                    (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a')
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h11.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h11.prem0 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h11.prem1 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h11.prem2 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h11.prem3 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h11.prem4)

-- Lean.Grind.CommRing.eq_cancel_of_kronLinS, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h12.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h12.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h12.prem2 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h12.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h12.prem4 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b a' b' c : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k (a'.add c)) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a (a'.add c)) Bool.true →
            @Eq Bool (b.linSOk_k (b'.add c)) Bool.true →
              @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K b (b'.add c)) Bool.true →
                @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K b) (Lean.Grind.CommRing.Expr.kronLinEval_k K (b'.add c)) →
                  @Eq Prop
                    (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
                    (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a')
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h12.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h12.prem0 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h12.prem1 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h12.prem2 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h12.prem3 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h12.prem4)

-- Lean.Grind.CommRing.eq_cancel_of_kronLinS, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h14.inst : Not
      (@Eq Prop
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h14.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h14.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h14.prem2 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h14.prem3 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h14.prem4 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h14 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b a' b' c : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k (a'.add c)) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a (a'.add c)) Bool.true →
            @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K a) (Lean.Grind.CommRing.Expr.kronLinEval_k K (a'.add c)) →
              @Eq Bool (b.linSOk_k (b'.add c)) Bool.true →
                @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K b) (Lean.Grind.CommRing.Expr.kronLinEval_k K (b'.add c)) →
                  @Eq Prop
                    (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
                    (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a')
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h14.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h14.prem0 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h14.prem1 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h14.prem2 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h14.prem3 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h14.prem4)

-- Lean.Grind.CommRing.eq_cancel_of_kronLinS, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h15.inst : Not
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
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h15.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h15.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h15.prem2 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h15.prem3 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linSOk_k
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h15.prem4 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h15 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b a' b' c : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k (a'.add c)) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a (a'.add c)) Bool.true →
            @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K a) (Lean.Grind.CommRing.Expr.kronLinEval_k K (a'.add c)) →
              @Eq Bool (b.linSOk_k (b'.add c)) Bool.true →
                @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K b (b'.add c)) Bool.true →
                  @Eq Prop
                    (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
                    (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a')
                      (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h15.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h15.prem0 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h15.prem1 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h15.prem2 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h15.prem3 HypCheckProof.Lean.Grind.CommRing.eq_cancel_of_kronLinS.h15.prem4)

-- Lean.Grind.CommRing.Stepwise.d_stepkC, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h14.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h14.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h14.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h14 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k₁ k : Int) (init p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int)
        (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
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
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h14.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@List.nil Nat) HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h14.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h14.prem1)

-- Lean.Grind.CommRing.Stepwise.d_stepkC, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h15.inst : Not
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
          (Lean.Grind.CommRing.Poly.mergeHintC (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)
            (Lean.Grind.CommRing.Poly.mulConstC_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h15.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h15 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k₁ k : Int) (init p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int)
        (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHintC c hs (Lean.Grind.CommRing.Poly.mulConstC_k k₁ p₁ c)
              (Lean.Grind.CommRing.Poly.mulMonC_k k₂ m₂ p₂ c)) →
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
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h15.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.mergeHintC (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)
      (Lean.Grind.CommRing.Poly.mulConstC_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.mulMonC_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        Lean.Grind.CommRing.Mon.unit (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h15.prem0)

-- Lean.Grind.CommRing.Stepwise.d_stepkC, hypothesis 16: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h16.inst : Not
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
          (Lean.Grind.CommRing.Poly.mergeHintC (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)
            (Lean.Grind.CommRing.Poly.mulConstC_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
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
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h16.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h16 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k₁ k : Int) (init p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int)
        (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHintC c hs (Lean.Grind.CommRing.Poly.mulConstC_k k₁ p₁ c)
              (Lean.Grind.CommRing.Poly.mulMonC_k k₂ m₂ p₂ c)) →
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
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h16.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.mergeHintC (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)
      (Lean.Grind.CommRing.Poly.mulConstC_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
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
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepkC.h16.prem0)

-- Lean.Grind.CommRing.Stepwise.d_stepsP, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsP.h13.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsP.h13.prem0 : @Eq Bool
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsP.h13.prem1 : @Eq Lean.Grind.CommRing.PPoly
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsP.h13.prem2 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsP.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k : Int)
        (init : Lean.Grind.CommRing.Poly) (B : Nat) (p₁ p : Lean.Grind.CommRing.Poly) (P : Lean.Grind.CommRing.PPoly)
        (t : Lean.Grind.CommRing.PSumTree),
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
                  (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsP.h13.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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
      (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsP.h13.prem0 rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsP.h13.prem1 HypCheckProof.Lean.Grind.CommRing.Stepwise.d_stepsP.h13.prem2)

-- Lean.Grind.CommRing.lt_norm_exprC_nc, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_exprC_nc.h3.inst : Not
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
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_exprC_nc.h3.prem0 : @Eq Bool
      (Lean.Grind.CommRing.norm_cnstrC_nc_cert
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_exprC_nc.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Ring α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst) inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.norm_cnstrC_nc_cert lhs rhs lhs' rhs' c) Bool.true →
          @Eq Prop
            (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α inst ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α inst ctx rhs))
            (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α inst ctx lhs')
              (@Lean.Grind.CommRing.Expr.denote α inst ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm_exprC_nc.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.lt_norm_exprC_nc.h3.prem0)

-- Lean.Grind.CommRing.lt_norm_exprC_nc, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_exprC_nc.h14.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_exprC_nc.h14 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Ring α]
        [inst_1 : @Lean.Grind.IsCharP α (@Lean.Grind.Ring.toSemiring α inst) c] [inst_2 : LE α] [inst_3 : LT α]
        [inst_4 : @Std.LawfulOrderLT α inst_3 inst_2] [inst_5 : @Std.IsPreorder α inst_2]
        [inst_6 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst) inst_2 inst_3 inst_5]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
        @Eq Prop
          (@LT.lt α inst_3 (@Lean.Grind.CommRing.Expr.denote α inst ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α inst ctx rhs))
          (@LT.lt α inst_3 (@Lean.Grind.CommRing.Expr.denote α inst ctx lhs')
            (@Lean.Grind.CommRing.Expr.denote α inst ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm_exprC_nc.h14.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))

-- Lean.Grind.CommRing.Expr.eq_of_kronQ, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h12.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h12.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h12.prem2 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degQOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h12.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQEq_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h12 : Not
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
                  @Eq α
                    (@Lean.Grind.CommRing.Expr.denote α
                      (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx a)
                    (@Lean.Grind.CommRing.Expr.denote α
                      (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h12.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h12.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h12.prem1 (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h12.prem2 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h12.prem3)

-- Lean.Grind.CommRing.Expr.eq_of_kronQ, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h13.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h13.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h13.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h13.prem2 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degQOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h13.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h13 : Not
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
                  @Eq α
                    (@Lean.Grind.CommRing.Expr.denote α
                      (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx a)
                    (@Lean.Grind.CommRing.Expr.denote α
                      (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h13.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h13.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h13.prem1 (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h13.prem2 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronQ.h13.prem3)

-- Lean.Grind.CommRing.Stepwise.d_step1C, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h13.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h13.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h13.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h13 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k : Int) (init p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int)
        (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
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
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h13.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@List.nil Nat) HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h13.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h13.prem1)

-- Lean.Grind.CommRing.Stepwise.d_step1C, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h14.inst : Not
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
          (Lean.Grind.CommRing.Poly.mergeHintC (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
            (Lean.Grind.CommRing.Poly.mulMonC_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
              Lean.Grind.CommRing.Mon.unit
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h14.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h14 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k : Int) (init p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int)
        (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHintC c hs p₁ (Lean.Grind.CommRing.Poly.mulMonC_k k₂ m₂ p₂ c)) →
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
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h14.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.mergeHintC (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Poly.mulMonC_k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        Lean.Grind.CommRing.Mon.unit (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h14.prem0)

-- Lean.Grind.CommRing.Stepwise.d_step1C, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h15.inst : Not
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
          (Lean.Grind.CommRing.Poly.mergeHintC (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Poly.mulMonC_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              Lean.Grind.CommRing.Mon.unit
              (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h15.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h15 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k : Int) (init p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int)
        (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHintC c hs p₁ (Lean.Grind.CommRing.Poly.mulMonC_k k₂ m₂ p₂ c)) →
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
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h15.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.mergeHintC (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.mulMonC_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        Lean.Grind.CommRing.Mon.unit
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.d_step1C.h15.prem0)

-- Lean.Grind.CommRing.lt_false_of_kron, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kron.h12.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        False) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kron.h12.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kron.h12.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kron.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronEval_k K B a) (Lean.Grind.CommRing.Expr.kronEval_k K B b) →
            @Eq Prop
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_kron.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_kron.h12.prem0 HypCheckProof.Lean.Grind.CommRing.lt_false_of_kron.h12.prem1)

-- Lean.Grind.CommRing.lt_false_of_kron, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kron.h13.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kron.h13.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kron.h13.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kron.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Prop
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_kron.h13.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_kron.h13.prem0 HypCheckProof.Lean.Grind.CommRing.lt_false_of_kron.h13.prem1)

-- Lean.Grind.CommRing.eq_norm_poly, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr) (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
          @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (lp.combine_k
                  (Lean.Grind.CommRing.Poly.mulConst_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) rp)) →
              @Eq Prop
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combine_k
      (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl rfl)

-- Lean.Grind.CommRing.eq_norm_poly, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h12.prem0 : @Eq Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combine_k
        (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr) (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (lhs.sub rhs)) →
          @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (lp.combine_k
                  (Lean.Grind.CommRing.Poly.mulConst_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) rp)) →
              @Eq Prop
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h12.prem0)

-- Lean.Grind.CommRing.eq_norm_poly, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h13.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h13.prem0 : @Eq Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combine_k
        (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr) (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (lhs.sub rhs)) →
          @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (lp.combine_k
                  (Lean.Grind.CommRing.Poly.mulConst_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) rp)) →
              @Eq Prop
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h13.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h13.prem0)

-- Lean.Grind.CommRing.eq_norm_poly, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h14.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h14 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr) (p lp rp : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (lhs.sub rhs)) →
          @Eq Lean.Grind.CommRing.Expr lhs' lp.toExpr_k →
            @Eq Lean.Grind.CommRing.Expr rhs' rp.toExpr_k →
              @Eq Prop
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
                (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_norm_poly.h14.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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

-- Lean.Grind.CommRing.sub_eq_of_toExpr, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h11.inst : Not
      (@Eq Int
        (@HSub.hSub Int Int Int
          (@instHSub Int (@Lean.Grind.Ring.toSub Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@HSub.hSub Int Int Int
          (@instHSub Int (@Lean.Grind.Ring.toSub Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
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
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (a b a' b' : Lean.Grind.CommRing.Expr) (p pa pb : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Expr a' pa.toExpr_k →
          @Eq Lean.Grind.CommRing.Expr b' pb.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (pa.combine_k
                  (Lean.Grind.CommRing.Poly.mulConst_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) pb)) →
              @Eq α
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).toExpr_k) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combine_k
      (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl rfl)

-- Lean.Grind.CommRing.sub_eq_of_toExpr, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h12.inst : Not
      (@Eq Int
        (@HSub.hSub Int Int Int
          (@instHSub Int (@Lean.Grind.Ring.toSub Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@HSub.hSub Int Int Int
          (@instHSub Int (@Lean.Grind.Ring.toSub Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h12.prem0 : @Eq Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combine_k
        (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (a b a' b' : Lean.Grind.CommRing.Expr) (p pa pb : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (a.sub b)) →
          @Eq Lean.Grind.CommRing.Expr b' pb.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (pa.combine_k
                  (Lean.Grind.CommRing.Poly.mulConst_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) pb)) →
              @Eq α
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h12.prem0)

-- Lean.Grind.CommRing.sub_eq_of_toExpr, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h13.inst : Not
      (@Eq Int
        (@HSub.hSub Int Int Int
          (@instHSub Int (@Lean.Grind.Ring.toSub Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@HSub.hSub Int Int Int
          (@instHSub Int (@Lean.Grind.Ring.toSub Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k)
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h13.prem0 : @Eq Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combine_k
        (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (a b a' b' : Lean.Grind.CommRing.Expr) (p pa pb : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (a.sub b)) →
          @Eq Lean.Grind.CommRing.Expr a' pa.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (pa.combine_k
                  (Lean.Grind.CommRing.Poly.mulConst_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) pb)) →
              @Eq α
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h13.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h13.prem0)

-- Lean.Grind.CommRing.sub_eq_of_toExpr, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h14.inst : Not
      (@Eq Int
        (@HSub.hSub Int Int Int
          (@instHSub Int (@Lean.Grind.Ring.toSub Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@HSub.hSub Int Int Int
          (@instHSub Int (@Lean.Grind.Ring.toSub Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
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
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h14 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (a b a' b' : Lean.Grind.CommRing.Expr) (p pa pb : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (a.sub b)) →
          @Eq Lean.Grind.CommRing.Expr a' pa.toExpr_k →
            @Eq Lean.Grind.CommRing.Expr b' pb.toExpr_k →
              @Eq α
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExpr.h14.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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

-- Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h9.inst : Not
      (@LE.le Int Int.instLEInt
        (@HSMul.hSMul Int Int Int
          (@instHSMul Int Int
            (@Lean.Grind.IntModule.zsmul Int
              (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@HSMul.hSMul Int Int Int
          (@instHSMul Int Int
            (@Lean.Grind.IntModule.zsmul Int
              (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h9.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h9.prem1 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h9.prem2 : @LE.le Int Int.instLEInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h9 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : @Std.IsPreorder M inst] [inst_2 : Lean.Grind.IntModule M]
        [inst_3 :
          @Lean.Grind.OrderedAdd M
            (@instHAdd M
              (@Lean.Grind.AddCommMonoid.toAdd M
                (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2))))
            inst inst_1]
        {k₁ k₂ : Int} {x y : M},
        @LE.le M inst x y →
          @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k₁ →
            @LE.le M inst
                (@OfNat.ofNat M (nat_lit 0)
                  (@Zero.toOfNat0 M
                    (@Lean.Grind.AddCommMonoid.toZero M
                      (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2)))))
                x →
              @LE.le M inst (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k₁ x)
                (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k₂ y)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h9.inst (@hc_h (Int) (Int.instLEInt) _ (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h9.prem0 HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h9.prem1 HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h9.prem2)

-- Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h10.inst : Not
      (@LE.le Int Int.instLEInt
        (@HSMul.hSMul Int Int Int
          (@instHSMul Int Int
            (@Lean.Grind.IntModule.zsmul Int
              (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@HSMul.hSMul Int Int Int
          (@instHSMul Int Int
            (@Lean.Grind.IntModule.zsmul Int
              (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h10.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h10.prem1 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h10.prem2 : @LE.le Int Int.instLEInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h10 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : @Std.IsPreorder M inst] [inst_2 : Lean.Grind.IntModule M]
        [inst_3 :
          @Lean.Grind.OrderedAdd M
            (@instHAdd M
              (@Lean.Grind.AddCommMonoid.toAdd M
                (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2))))
            inst inst_1]
        {k₁ k₂ : Int} {x y : M},
        @LE.le Int Int.instLEInt k₁ k₂ →
          @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k₁ →
            @LE.le M inst
                (@OfNat.ofNat M (nat_lit 0)
                  (@Zero.toOfNat0 M
                    (@Lean.Grind.AddCommMonoid.toZero M
                      (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2)))))
                x →
              @LE.le M inst (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k₁ x)
                (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k₂ y)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h10.inst (@hc_h (Int) (Int.instLEInt) _ (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h10.prem0 HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h10.prem1 HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h10.prem2)

-- Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h11.prem0 : @LE.le Int Int.instLEInt (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h11.prem1 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h11.prem2 : @LE.le Int Int.instLEInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h11 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : @Std.IsPreorder M inst] [inst_2 : Lean.Grind.IntModule M]
        [inst_3 :
          @Lean.Grind.OrderedAdd M
            (@instHAdd M
              (@Lean.Grind.AddCommMonoid.toAdd M
                (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2))))
            inst inst_1]
        {k₁ k₂ : Int} {x y : M},
        @LE.le Int Int.instLEInt k₁ k₂ →
          @LE.le M inst x y →
            @LE.le M inst
                (@OfNat.ofNat M (nat_lit 0)
                  (@Zero.toOfNat0 M
                    (@Lean.Grind.AddCommMonoid.toZero M
                      (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2)))))
                x →
              @LE.le M inst (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k₁ x)
                (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k₂ y)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h11.inst (@hc_h (Int) (Int.instLEInt) _ (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h11.prem0 HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h11.prem1 HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h11.prem2)

-- Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h12.inst : Not
      (@LE.le Int Int.instLEInt
        (@HSMul.hSMul Int Int Int
          (@instHSMul Int Int
            (@Lean.Grind.IntModule.zsmul Int
              (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@HSMul.hSMul Int Int Int
          (@instHSMul Int Int
            (@Lean.Grind.IntModule.zsmul Int
              (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h12.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h12.prem1 : @LE.le Int Int.instLEInt (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h12.prem2 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h12 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : @Std.IsPreorder M inst] [inst_2 : Lean.Grind.IntModule M]
        [inst_3 :
          @Lean.Grind.OrderedAdd M
            (@instHAdd M
              (@Lean.Grind.AddCommMonoid.toAdd M
                (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2))))
            inst inst_1]
        {k₁ k₂ : Int} {x y : M},
        @LE.le Int Int.instLEInt k₁ k₂ →
          @LE.le M inst x y →
            @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k₁ →
              @LE.le M inst (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k₁ x)
                (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k₂ y)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h12.inst (@hc_h (Int) (Int.instLEInt) _ (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h12.prem0 HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h12.prem1 HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul_of_le_of_le_of_nonneg_of_nonneg.h12.prem2)

-- Lean.Grind.AC.superpose, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose.h12.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose.h12.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose.h12.prem1 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.superpose.h12.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.superpose.h12 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op}
        (p c s lhs₁ rhs₁ lhs₂ rhs₂ lhs rhs : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₂ →
            Lean.Grind.AC.Seq.denote ctx lhs = Lean.Grind.AC.Seq.denote ctx rhs := fun hc_h => HypCheckProof.Lean.Grind.AC.superpose.h12.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.superpose.h12.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.superpose.h12.prem1 HypCheckProof.Lean.Grind.AC.superpose.h12.prem2)

-- Lean.Grind.Order.lt_of_not_le_k, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le_k.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le_k.h11.prem0 : Not
      (@LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le_k.h11 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsLinearPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1
            (@Std.IsLinearPreorder.toIsPreorder α inst inst_3)]
        {a b : α} {k k' : Int},
        Not
            (@LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) →
          @LT.lt α inst_1 b
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k'))) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_of_not_le_k.h11.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_of_not_le_k.h11.prem0)

-- Lean.Grind.Order.lt_of_not_le_k, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le_k.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le_k.h12.prem0 : @Eq Bool
      (Int.beq' (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le_k.h12 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsLinearPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst :
          @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1
            (@Std.IsLinearPreorder.toIsPreorder α inst inst_3)]
        {a b : α} {k k' : Int},
        @Eq Bool (k'.beq' (@Neg.neg Int Int.instNegInt k)) Bool.true →
          @LT.lt α inst_1 b
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k'))) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_of_not_le_k.h12.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_of_not_le_k.h12.prem0)

-- Lean.Grind.CommRing.not_le_norm, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.not_le_norm.h6.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.not_le_norm.h6.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.core_cert
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.not_le_norm.h6.prem1 : Not
      (@LE.le UInt8 instLEUInt8
        (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
          (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
          (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.not_le_norm.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsLinearOrder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.core_cert rhs lhs p) Bool.true →
          Not
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) →
            @LT.lt α inst_2 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.not_le_norm.h6.inst (@hc_h (UInt8) (Lean.Grind.instCommRingUInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) HypCheckProof.Lean.Grind.CommRing.not_le_norm.h6.prem0 HypCheckProof.Lean.Grind.CommRing.not_le_norm.h6.prem1)

-- Lean.Grind.CommRing.not_le_norm, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.not_le_norm.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.not_le_norm.h11.prem0 : Not
      (@LE.le Int Int.instLEInt
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.not_le_norm.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsLinearOrder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2
            (@Std.IsLinearPreorder.toIsPreorder α inst_1 (@Std.IsLinearOrder.toIsLinearPreorder α inst_1 inst_4))]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        Not
            (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) →
          @LT.lt α inst_2 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.not_le_norm.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.not_le_norm.h11.prem0)

-- Lean.Grind.CommRing.not_le_norm, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.not_le_norm.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.not_le_norm.h12.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.core_cert
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.not_le_norm.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsLinearOrder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2
            (@Std.IsLinearPreorder.toIsPreorder α inst_1 (@Std.IsLinearOrder.toIsLinearPreorder α inst_1 inst_4))]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.core_cert rhs lhs p) Bool.true →
          @LT.lt α inst_2 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.not_le_norm.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.not_le_norm.h12.prem0)

-- Lean.Grind.CommRing.not_lt_norm, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h6.inst : Not
      (@LE.le UInt8 instLEUInt8
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
theorem HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h6.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.core_cert
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h6.prem1 : Not
      (@LT.lt UInt8 instLTUInt8
        (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
          (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
          (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsLinearOrder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.core_cert rhs lhs p) Bool.true →
          Not
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) →
            @LE.le α inst_1 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h6.inst (@hc_h (UInt8) (Lean.Grind.instCommRingUInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h6.prem0 HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h6.prem1)

-- Lean.Grind.CommRing.not_lt_norm, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h11.inst : Not
      (@LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h11.prem0 : Not
      (@LT.lt Int Int.instLTInt
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsLinearOrder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2
            (@Std.IsLinearPreorder.toIsPreorder α inst_1 (@Std.IsLinearOrder.toIsLinearPreorder α inst_1 inst_4))]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        Not
            (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) →
          @LE.le α inst_1 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h11.prem0)

-- Lean.Grind.CommRing.not_lt_norm, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h12.inst : Not
      (@LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h12.prem0 : @Eq Bool
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
theorem HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsLinearOrder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2
            (@Std.IsLinearPreorder.toIsPreorder α inst_1 (@Std.IsLinearOrder.toIsLinearPreorder α inst_1 inst_4))]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.core_cert rhs lhs p) Bool.true →
          @LE.le α inst_1 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.not_lt_norm.h12.prem0)

-- Lean.Grind.OrderedAdd.add_lt_add, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_add.h6.inst : ¬0 + 1 ≠ 1 + 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_add.h6.prem0 : 0 ≠ 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_add.h6.prem1 : 1 ≠ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_add.h6 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M]
        [inst : Lean.Grind.OrderedAdd M] [inst : LT M] {a b c d : M}, a < b → c < d → a + c < b + d := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_lt_add.h6.inst (@hc_h (Nat) (instLENat) _ (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) _ ({ lt := fun (a b : Nat) => a ≠ b : LT Nat }) (0) (1) (1) (0) HypCheckProof.Lean.Grind.OrderedAdd.add_lt_add.h6.prem0 HypCheckProof.Lean.Grind.OrderedAdd.add_lt_add.h6.prem1)

-- Lean.Grind.CommRing.lt_false_of_toPoly_eq, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPoly_eq.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPoly_eq.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (bal₁ bal₂ : Bool) (lhs rhs : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal₂ rhs) →
          @Eq Prop
            (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPoly_eq.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) rfl)

-- Lean.Grind.CommRing.lt_false_of_toPoly_eq, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPoly_eq.h13.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPoly_eq.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (bal₁ bal₂ : Bool) (lhs rhs : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal₁ lhs) →
          @Eq Prop
            (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPoly_eq.h13.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl)

-- Lean.Grind.CommRing.le_true_of_poly, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_poly.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_poly.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs : Lean.Grind.CommRing.Expr) (n : Nat),
        @Eq Prop
          (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
          True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_poly.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))

-- Lean.Grind.Linarith.diseq_split, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split.h6.inst : Not
      (Or
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
                      (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))))))
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
                      (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split.h6.prem0 : @Eq Bool
      (Lean.Grind.Linarith.diseq_split_cert
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split.h6.prem1 : @Ne UInt8
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
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsLinearOrder α inst_1]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.diseq_split_cert p₁ p₂) Bool.true →
          @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            Or
              (@LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
                (@OfNat.ofNat α (nat_lit 0)
                  (@Zero.toOfNat0 α
                    (@Lean.Grind.AddCommMonoid.toZero α
                      (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))))
              (@LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
                (@OfNat.ofNat α (nat_lit 0)
                  (@Zero.toOfNat0 α
                    (@Lean.Grind.AddCommMonoid.toZero α
                      (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.diseq_split.h6.inst (@hc_h (UInt8) (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)) (instLEUInt8) (instLTUInt8) _ _ (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.diseq_split.h6.prem0 HypCheckProof.Lean.Grind.Linarith.diseq_split.h6.prem1)

-- Lean.Grind.Linarith.diseq_split, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split.h10.inst : Not
      (Or
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
                    (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))))
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.Linarith.Poly.denote' Int
            (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
          (@OfNat.ofNat Int (nat_lit 0)
            (@Zero.toOfNat0 Int
              (@Lean.Grind.AddCommMonoid.toZero Int
                (@Lean.Grind.NatModule.toAddCommMonoid Int
                  (@Lean.Grind.IntModule.toNatModule Int
                    (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split.h10.prem0 : @Ne Int
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
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split.h10 : Not
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
          Or
            (@LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))))
            (@LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.diseq_split.h10.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.diseq_split.h10.prem0)

-- Lean.Grind.Linarith.diseq_split, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split.h11.inst : Not
      (Or
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.Linarith.Poly.denote' Int
            (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
          (@OfNat.ofNat Int (nat_lit 0)
            (@Zero.toOfNat0 Int
              (@Lean.Grind.AddCommMonoid.toZero Int
                (@Lean.Grind.NatModule.toAddCommMonoid Int
                  (@Lean.Grind.IntModule.toNatModule Int
                    (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))))
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.Linarith.Poly.denote' Int
            (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
          (@OfNat.ofNat Int (nat_lit 0)
            (@Zero.toOfNat0 Int
              (@Lean.Grind.AddCommMonoid.toZero Int
                (@Lean.Grind.NatModule.toAddCommMonoid Int
                  (@Lean.Grind.IntModule.toNatModule Int
                    (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split.h11.prem0 : @Eq Bool (Lean.Grind.Linarith.diseq_split_cert Lean.Grind.Linarith.Poly.nil Lean.Grind.Linarith.Poly.nil) Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split.h11 : Not
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
          Or
            (@LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))))
            (@LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.diseq_split.h11.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.diseq_split.h11.prem0)

-- Lean.Grind.CommRing.Stepwise.imp_1eqK, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqK.h9.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqK.h9.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            ((Lean.Grind.CommRing.Expr.var
                  (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))).beq'
        (Lean.Grind.CommRing.Poly.kron_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqK.h9.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqK.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (lhs rhs : Lean.Grind.CommRing.Expr) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq Bool ((Lean.Grind.CommRing.Expr.kronEval_k K B (lhs.sub rhs)).beq' (Lean.Grind.CommRing.Poly.kron_k K B p₁))
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
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqK.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqK.h9.prem0 rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqK.h9.prem1)

-- Lean.Grind.CommRing.Stepwise.imp_1eqK, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqK.h10.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqK.h10.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.impOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqK.h10.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqK.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (lhs rhs : Lean.Grind.CommRing.Expr) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq Bool
            (Lean.Grind.CommRing.Stepwise.impOk_k K B (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (lhs.sub rhs) p₁ (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
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
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqK.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqK.h10.prem0 rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.imp_1eqK.h10.prem1)

-- Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_left, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_left.h10.inst : ¬-1 * 0 ≤ -1 * 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_left.h10.prem0 : -1 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_left.h10 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Lean.Grind.OrderedRing R] [inst_5 : Std.LawfulOrderLT R] {a b c : R}, c ≤ 0 → c * b ≤ c * a := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_left.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt.toRing) (Int.instLEInt) (Int.instLTInt) _ _ _ (1) (0) (-1) HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_left.h10.prem0)

-- Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_left, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_left.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_left.h11.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_left.h11 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.IsPartialOrder R inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2
            (@Std.IsPartialOrder.toIsPreorder R inst_1 inst_3)]
        [inst_5 : @Std.LawfulOrderLT R inst_2 inst_1] {a b c : R},
        @LE.le R inst_1 a b →
          @LE.le R inst_1
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) c b)
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) c a)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_left.h11.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_left.h11.prem0)

-- Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_right, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_right.h10.inst : ¬0 * -1 ≤ 1 * -1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_right.h10.prem0 : -1 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_right.h10 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Lean.Grind.OrderedRing R] [inst_5 : Std.LawfulOrderLT R] {a b c : R}, c ≤ 0 → b * c ≤ a * c := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_right.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt.toRing) (Int.instLEInt) (Int.instLTInt) _ _ _ (1) (0) (-1) HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_right.h10.prem0)

-- Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_right, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_right.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_right.h11.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_right.h11 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.IsPartialOrder R inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2
            (@Std.IsPartialOrder.toIsPreorder R inst_1 inst_3)]
        [inst_5 : @Std.LawfulOrderLT R inst_2 inst_1] {a b c : R},
        @LE.le R inst_1 a b →
          @LE.le R inst_1
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) b c)
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) a c)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_right.h11.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonpos_right.h11.prem0)

-- Lean.Grind.Linarith.eq_diseq_subst, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h9.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h9.prem1 : @Ne Int
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
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α]
        [inst_1 : @Lean.Grind.NoNatZeroDivisors α (@Lean.Grind.IntModule.toNatModule α inst)]
        (ctx : Lean.Grind.Linarith.Context α) (k₁ k₂ : Int) (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
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
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h9.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h9.prem0 HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h9.prem1)

-- Lean.Grind.Linarith.eq_diseq_subst, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h10.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h10.prem0 : @Eq Bool
      (Lean.Grind.Linarith.eq_diseq_subst_cert (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        Lean.Grind.Linarith.Poly.nil)
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h10.prem1 : @Ne Int
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
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α]
        [inst_1 : @Lean.Grind.NoNatZeroDivisors α (@Lean.Grind.IntModule.toNatModule α inst)]
        (ctx : Lean.Grind.Linarith.Context α) (k₁ k₂ : Int) (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.eq_diseq_subst_cert k₁ k₂ p₁ p₂ p₃) Bool.true →
          @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₃)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h10.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h10.prem0 HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h10.prem1)

-- Lean.Grind.Linarith.eq_diseq_subst, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h11.prem0 : @Eq Bool
      (Lean.Grind.Linarith.eq_diseq_subst_cert (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil Lean.Grind.Linarith.Poly.nil
        Lean.Grind.Linarith.Poly.nil)
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h11.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α]
        [inst_1 : @Lean.Grind.NoNatZeroDivisors α (@Lean.Grind.IntModule.toNatModule α inst)]
        (ctx : Lean.Grind.Linarith.Context α) (k₁ k₂ : Int) (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.eq_diseq_subst_cert k₁ k₂ p₁ p₂ p₃) Bool.true →
          @Eq α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₃)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h11.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h11.prem0 HypCheckProof.Lean.Grind.Linarith.eq_diseq_subst.h11.prem1)

-- Lean.Grind.AC.eq_simp_lhs_prefix, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h9.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h9.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h9.prem1 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h9.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h9 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op}
        (lhs₁ rhs₁ tail lhs₂ rhs₂ lhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₂ →
            Lean.Grind.AC.Seq.denote ctx lhs₂' = Lean.Grind.AC.Seq.denote ctx rhs₂ := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h9.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h9.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h9.prem1 HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h9.prem2)

-- Lean.Grind.AC.eq_simp_lhs_prefix, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h11.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h11.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h11.prem1 : Lean.Grind.AC.simp_prefix_cert (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0)
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h11.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h11 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op}
        (lhs₁ rhs₁ tail lhs₂ rhs₂ lhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.simp_prefix_cert lhs₁ rhs₁ tail lhs₂ lhs₂' = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
            Lean.Grind.AC.Seq.denote ctx lhs₂' = Lean.Grind.AC.Seq.denote ctx rhs₂ := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h11.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h11.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h11.prem1 HypCheckProof.Lean.Grind.AC.eq_simp_lhs_prefix.h11.prem2)

-- Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_pos_left, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_pos_left.h10.inst : Not
      (Iff
        (@LE.le Rat Rat.instLE
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
        (@LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_pos_left.h10 : Not
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
              c a)
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              c b))
          (@LE.le R inst_1 a b)) := fun hc_h => HypCheckProof.Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_pos_left.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.OrderedAdd.add_le_add, hypothesis 4: necessary
/- FAILED: 11:176: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 } | 47:123: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_add.h4.inst : ¬(0 + 1) % 2 ≤ (1 + 1) % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_add.h4.prem0 : 0 % 2 ≤ 1 % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_add.h4.prem1 : 1 % 2 ≤ 1 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_add.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M] {a b c d : M},
        a ≤ b → c ≤ d → a + c ≤ b + d := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_le_add.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) (0) (1) (1) (1) HypCheckProof.Lean.Grind.OrderedAdd.add_le_add.h4.prem0 HypCheckProof.Lean.Grind.OrderedAdd.add_le_add.h4.prem1)
-/

-- Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff.h4.inst : ¬(-1 • UInt8.ofNat 0 < -1 • UInt8.ofNat 1 ↔ 0 < -1) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff.h4.prem0 : UInt8.ofNat 0 < UInt8.ofNat 1 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.IntModule M] [inst_3 : LT M]
        [inst : Std.LawfulOrderLT M] (k : Int) {a b : M}, a < b → (k • a < k • b ↔ 0 < k) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff.h4.inst (@hc_h (UInt8) (instLEUInt8) _ (Lean.Grind.Ring.toIntModule) (instLTUInt8) _ (-1) (UInt8.ofNat 0) (UInt8.ofNat 1) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff.h4.prem0)

-- Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff.h10.inst : Not
      (Iff
        (@LT.lt Int Int.instLTInt
          (@HSMul.hSMul Int Int Int
            (@instHSMul Int Int
              (@Lean.Grind.IntModule.zsmul Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (@HSMul.hSMul Int Int Int
            (@instHSMul Int Int
              (@Lean.Grind.IntModule.zsmul Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff.h10 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : @Std.IsPreorder M inst] [inst_2 : Lean.Grind.IntModule M]
        [inst_3 :
          @Lean.Grind.OrderedAdd M
            (@instHAdd M
              (@Lean.Grind.AddCommMonoid.toAdd M
                (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2))))
            inst inst_1]
        [inst_4 : LT M] [inst : @Std.LawfulOrderLT M inst_4 inst] (k : Int) {a b : M},
        Iff
          (@LT.lt M inst_4 (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k a)
            (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k b))
          (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff.h10.inst (@hc_h (Int) (Int.instLEInt) _ (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (Int.instLTInt) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_pos_right, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_pos_right.h10.inst : Not
      (Iff
        (@LE.le Rat Rat.instLE
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
        (@LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_pos_right.h10 : Not
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
          (@LE.le R inst_1 a b)) := fun hc_h => HypCheckProof.Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_pos_right.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.Linarith.le_of_eq, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_of_eq.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.le_of_eq.h9.prem0 : @Eq Int
      (@Lean.Grind.Linarith.Expr.denote_k Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Expr.zero)
      (@Lean.Grind.Linarith.Expr.denote_k Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Expr.zero) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.Linarith.le_of_eq.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        [inst_3 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 inst_2]
        (ctx : Lean.Grind.Linarith.Context α) (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @Eq α (@Lean.Grind.Linarith.Expr.denote_k α inst ctx lhs) (@Lean.Grind.Linarith.Expr.denote_k α inst ctx rhs) →
          @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.le_of_eq.h9.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.le_of_eq.h9.prem0)

-- Lean.Grind.Linarith.le_of_eq, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_of_eq.h10.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.le_of_eq.h10.prem0 : @Eq Bool
      (Lean.Grind.Linarith.norm_cert
        (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        Lean.Grind.Linarith.Expr.zero
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.le_of_eq.h10 : Not
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
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.le_of_eq.h10.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.le_of_eq.h10.prem0)

-- Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_neg_left, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_neg_left.h10.inst : Not
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
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
        (@LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_neg_left.h10 : Not
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
              c a)
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              c b))
          (@LE.le R inst_1 b a)) := fun hc_h => HypCheckProof.Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_neg_left.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.CommRing.Stepwise.divC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h3.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h3.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.div_certC
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h3.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        [inst_1 :
          @Lean.Grind.NoNatZeroDivisors α
            (@Lean.Grind.Semiring.toNatModule α
              (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))]
        (p₁ : Lean.Grind.CommRing.Poly) (k : Int) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.div_certC p₁ k p c) Bool.true →
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) _ (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h3.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h3.prem1)

-- Lean.Grind.CommRing.Stepwise.divC, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h9.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h9 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α)
        [inst_2 :
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
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h9.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) _ (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h9.prem0)

-- Lean.Grind.CommRing.Stepwise.divC, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h10.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h10.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Stepwise.div_certC
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h10 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α)
        [inst_2 :
          @Lean.Grind.NoNatZeroDivisors α
            (@Lean.Grind.Semiring.toNatModule α
              (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))]
        (p₁ : Lean.Grind.CommRing.Poly) (k : Int) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.Stepwise.div_certC p₁ k p c) Bool.true →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h10.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) _ (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.divC.h10.prem0)

-- Lean.Grind.CommRing.Expr.eq_of_toPPX_eq, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eq.h9.inst : Not
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
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eq.h9.prem0 : @Eq Lean.Grind.CommRing.PPoly
      (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Bool.false
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Bool.false
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eq.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool)
        (a b : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.PPoly),
        @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a) →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eq.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.branch Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Bool.false
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) rfl HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eq.h9.prem0)

-- Lean.Grind.CommRing.Expr.eq_of_toPPX_eq, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eq.h10.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eq.h10.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eq.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool)
        (a b : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.PPoly),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eq.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Bool.false
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eq.h10.prem0 rfl)

-- Lean.Grind.CommRing.Expr.eq_of_toPPX_eq, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eq.h11.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eq.h11.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eq.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool)
        (a b : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.PPoly),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eq.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPPX_eq.h11.prem0 rfl)

-- Lean.Grind.CommRing.le_norm_expr_nc, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_expr_nc.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_expr_nc.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.Ring α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst) inst_1 inst_2 inst_3]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
        @Eq Prop
          (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α inst ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α inst ctx rhs))
          (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α inst ctx lhs')
            (@Lean.Grind.CommRing.Expr.denote α inst ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_expr_nc.h11.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))

-- Lean.Grind.OrderedRing.natCast_lt_natCast_of_lt, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.natCast_lt_natCast_of_lt.h9.inst : Not
      (@LT.lt Int Int.instLTInt
        (@Nat.cast Int
          (@Lean.Grind.Semiring.natCast Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Nat.cast Int
          (@Lean.Grind.Semiring.natCast Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.natCast_lt_natCast_of_lt.h9 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1]
        [inst_5 : @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2 inst_4] (a b : Nat),
        @LT.lt R inst_2 (@Nat.cast R (@Lean.Grind.Semiring.natCast R (@Lean.Grind.Ring.toSemiring R inst)) a)
          (@Nat.cast R (@Lean.Grind.Semiring.natCast R (@Lean.Grind.Ring.toSemiring R inst)) b)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.natCast_lt_natCast_of_lt.h9.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))

-- Lean.Grind.Preorder.lt_of_le_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Preorder.lt_of_le_of_lt.h3.inst : ¬0 ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Preorder.lt_of_le_of_lt.h3.prem0 : 0 ≤ 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Preorder.lt_of_le_of_lt.h3.prem1 : 1 ≠ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.Preorder.lt_of_le_of_lt.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.IsPreorder α] {a b c : α}, a ≤ b → b < c → a < c := fun hc_h => HypCheckProof.Lean.Grind.Preorder.lt_of_le_of_lt.h3.inst (@hc_h (Nat) (instLENat) ({ lt := fun (a b : Nat) => a ≠ b : LT Nat }) _ (0) (1) (0) HypCheckProof.Lean.Grind.Preorder.lt_of_le_of_lt.h3.prem0 HypCheckProof.Lean.Grind.Preorder.lt_of_le_of_lt.h3.prem1)

-- Lean.Grind.OrderedAdd.nsmul_pos_iff, hypothesis 4: necessary
/- FAILED: 8:225: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 } | 53:123: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_pos_iff.h4.inst : ¬(0 % 2 < 2 • 1 % 2 ↔ 0 < 2) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_pos_iff.h4.prem0 : 0 % 2 < 1 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_pos_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.NatModule M] [inst_3 : LT M]
        [inst : Std.LawfulOrderLT M] {k : Nat} {a : M}, 0 < a → (0 < k • a ↔ 0 < k) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.nsmul_pos_iff.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule) ({ lt := fun (a b : Nat) => a % 2 < b % 2 : LT Nat }) (@Std.LawfulOrderLT.mk _ _ _ (by (try dsimp only);   (intros; omega))) (2) (1) HypCheckProof.Lean.Grind.OrderedAdd.nsmul_pos_iff.h4.prem0)
-/

-- Lean.Grind.OrderedAdd.nsmul_pos_iff, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_pos_iff.h6.inst : ¬(0 ≤ 0 • 0 ↔ 0 < 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_pos_iff.h6.prem0 : 0 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_pos_iff.h6 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.NatModule M]
        [inst : Lean.Grind.OrderedAdd M] [inst : LT M] {k : Nat} {a : M}, 0 < a → (0 < k • a ↔ 0 < k) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.nsmul_pos_iff.h6.inst (@hc_h (Nat) (instLENat) _ (Lean.Grind.Semiring.toNatModule) _ ({ lt := fun (a b : Nat) => a ≤ b : LT Nat }) (0) (0) HypCheckProof.Lean.Grind.OrderedAdd.nsmul_pos_iff.h6.prem0)

-- Lean.Grind.AC.eq_erase_dup, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup.h3.inst : ¬Lean.Grind.AC.Seq.denote
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
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup.h3.prem0 : Std.Associative
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup.h3.prem1 : Lean.Grind.AC.eq_erase_dup_cert (Lean.Grind.AC.Seq.var 1) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0))
        (Lean.Grind.AC.Seq.var 1) (Lean.Grind.AC.Seq.var 0) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup.h3.prem2 : Lean.Grind.AC.Seq.denote
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
theorem HypCheckProof.Lean.Grind.AC.eq_erase_dup.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} (lhs rhs lhs' rhs' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.eq_erase_dup_cert lhs rhs lhs' rhs' = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs = Lean.Grind.AC.Seq.denote ctx rhs →
            Lean.Grind.AC.Seq.denote ctx lhs' = Lean.Grind.AC.Seq.denote ctx rhs' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_erase_dup.h3.inst (@hc_h (Nat) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
      op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_erase_dup.h3.prem0 (Lean.Grind.AC.Seq.var 1) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 1) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.eq_erase_dup.h3.prem1 HypCheckProof.Lean.Grind.AC.eq_erase_dup.h3.prem2)

-- Lean.Grind.CommRing.Expr.sub_eq_of_kronLin, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.sub_eq_of_kronLin.h8.inst : Not
      (@Eq Int
        (@HSub.hSub Int Int Int
          (@instHSub Int (@Lean.Grind.Ring.toSub Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.sub_eq_of_kronLin.h8.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).linOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.sub_eq_of_kronLin.h8.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.sub_eq_of_kronLin.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K : Nat)
        (a b : Lean.Grind.CommRing.Expr) (k : Int),
        @Eq Bool (a.linOk_k (b.add (Lean.Grind.CommRing.Expr.num k))) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K a)
              (Lean.Grind.CommRing.Expr.kronLinEval_k K (b.add (Lean.Grind.CommRing.Expr.num k))) →
            @Eq α
              (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.sub_eq_of_kronLin.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.CommRing.Expr.sub_eq_of_kronLin.h8.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.sub_eq_of_kronLin.h8.prem1)

-- Lean.Grind.CommRing.Expr.sub_eq_of_kronLin, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.sub_eq_of_kronLin.h9.inst : Not
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
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.sub_eq_of_kronLin.h9.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linOk_k
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.sub_eq_of_kronLin.h9.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.sub_eq_of_kronLin.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K : Nat)
        (a b : Lean.Grind.CommRing.Expr) (k : Int),
        @Eq Bool (a.linOk_k (b.add (Lean.Grind.CommRing.Expr.num k))) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a (b.add (Lean.Grind.CommRing.Expr.num k))) Bool.true →
            @Eq α
              (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.sub_eq_of_kronLin.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.CommRing.Expr.sub_eq_of_kronLin.h9.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.sub_eq_of_kronLin.h9.prem1)

-- Lean.Grind.CommRing.PPoly.denote_eq_of_kron, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denote_eq_of_kron.h8.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.PPoly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (fun (a : Nat) => @OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.PPoly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (fun (a : Nat) => @OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denote_eq_of_kron.h8.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 3) (@instOfNat (nat_lit 3))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denote_eq_of_kron.h8.prem1 : @LT.lt Int Int.instLTInt
      (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))
        (@Nat.cast Int instNatCastInt
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).norm1
            (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).norm1)))
      (@OfNat.ofNat Int (nat_lit 3) (@instOfNat (nat_lit 3))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denote_eq_of_kron.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.Ring α] (f : Nat → α) (B : Nat) (X : Int),
        @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) X →
          ∀ (p q : Lean.Grind.CommRing.PPoly),
            @LT.lt Int Int.instLTInt
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))
                  (@Nat.cast Int instNatCastInt (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) p.norm1 q.norm1)))
                X →
              @Eq α (@Lean.Grind.CommRing.PPoly.denote α inst f B p) (@Lean.Grind.CommRing.PPoly.denote α inst f B q)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.PPoly.denote_eq_of_kron.h8.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (fun (a : Nat) => @OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 3) (@instOfNat (nat_lit 3))) HypCheckProof.Lean.Grind.CommRing.PPoly.denote_eq_of_kron.h8.prem0 (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.PPoly.denote_eq_of_kron.h8.prem1)

-- Lean.Grind.CommRing.Expr.denote_neg_ofC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_ofC.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).neg)
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.mulConstC_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_ofC.h3.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_ofC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (a : Lean.Grind.CommRing.Expr) (pa p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq Lean.Grind.CommRing.Poly p
              (Lean.Grind.CommRing.Poly.mulConstC_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                pa c) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a.neg)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_ofC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.mulConstC_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_ofC.h3.prem0 rfl)

-- Lean.Grind.CommRing.Expr.denote_neg_ofC, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_ofC.h8.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).neg)
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.mulConstC_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_ofC.h8 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr) (pa p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mulConstC_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) pa
              c) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a.neg)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_ofC.h8.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.mulConstC_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) rfl)

-- Lean.Grind.CommRing.Expr.denote_neg_ofC, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_ofC.h9.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).neg)
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_ofC.h9.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_ofC.h9 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr) (pa p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a.neg)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_ofC.h9.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_ofC.h9.prem0)

-- Lean.Grind.CommRing.eq_cancel_var, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h7.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h7.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h7.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (c : Int)
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h7.prem0 HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h7.prem1)

-- Lean.Grind.CommRing.eq_cancel_var, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h8.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h8.prem0 : @Eq Bool
      (Lean.Grind.CommRing.cancel_var_cert (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h8.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
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
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (c : Int)
        (x : Lean.Grind.CommRing.Var) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.cancel_var_cert c x p₁ p₂) Bool.true →
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h8.prem0 HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h8.prem1)

-- Lean.Grind.CommRing.eq_cancel_var, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h9.prem0 : @Eq Bool
      (Lean.Grind.CommRing.cancel_var_cert (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h9.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (c : Int)
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
            @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h9.prem0 HypCheckProof.Lean.Grind.CommRing.eq_cancel_var.h9.prem1)

-- Int.Internal.Linear.eq_of_dvd_ediv, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_dvd_ediv.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_dvd_ediv.h6.prem0 : Int.Internal.Linear.eq_of_dvd_ediv_cert (-1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.num 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) 0 =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_dvd_ediv.h6.prem1 : -1 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_of_dvd_ediv.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (d : Int) (e : Int.Internal.Linear.Expr) (p p' : Int.Internal.Linear.Poly)
        (x : Int.Internal.Linear.Var),
        Int.Internal.Linear.eq_of_dvd_ediv_cert d e p p' x = Bool.true →
          d ∣ Int.Internal.Linear.Poly.denote' ctx p → Int.Internal.Linear.Poly.denote' ctx p' = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_of_dvd_ediv.h6.inst (@hc_h (Lean.RArray.leaf 1) (-1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) HypCheckProof.Int.Internal.Linear.eq_of_dvd_ediv.h6.prem0 HypCheckProof.Int.Internal.Linear.eq_of_dvd_ediv.h6.prem1)

-- Int.Internal.Linear.eq_of_dvd_ediv, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_dvd_ediv.h7.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_dvd_ediv.h7.prem0 : Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0 =
      Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0) / 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_dvd_ediv.h7.prem1 : 1 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_of_dvd_ediv.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (d : Int) (e : Int.Internal.Linear.Expr) (p p' : Int.Internal.Linear.Poly)
        (x : Int.Internal.Linear.Var),
        Int.Internal.Linear.Var.denote ctx x = Int.Internal.Linear.Expr.denote_k ctx e / d →
          d ∣ Int.Internal.Linear.Poly.denote' ctx p → Int.Internal.Linear.Poly.denote' ctx p' = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_of_dvd_ediv.h7.inst (@hc_h (Lean.RArray.leaf 1) (1) (Int.Internal.Linear.Expr.var 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) HypCheckProof.Int.Internal.Linear.eq_of_dvd_ediv.h7.prem0 HypCheckProof.Int.Internal.Linear.eq_of_dvd_ediv.h7.prem1)

-- Lean.Grind.CommRing.eq_true_of_kronLin, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLin.h7.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLin.h7.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).linOk_k
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLin.h7.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLin.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linOk_k b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K a) (Lean.Grind.CommRing.Expr.kronLinEval_k K b) →
            @Eq Prop
              (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLin.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLin.h7.prem0 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLin.h7.prem1)

-- Lean.Grind.CommRing.eq_true_of_kronLin, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLin.h8.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLin.h8.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linOk_k
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLin.h8.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLin.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linOk_k b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Prop
              (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLin.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLin.h8.prem0 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLin.h8.prem1)

-- Lean.Grind.CommRing.Stepwise.unsat_eqC, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eqC.h7.inst : Not False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eqC.h7.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eqC.h7 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (p : Lean.Grind.CommRing.Poly) (k : Int),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
          False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eqC.h7.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eqC.h7.prem0)

-- Lean.Grind.CommRing.Stepwise.unsat_eqC, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eqC.h8.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eqC.h8.prem0 : Lean.Grind.CommRing.Stepwise.unsat_eq_certC (Lean.Grind.CommRing.Poly.num 1) 1 0 = Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eqC.h8 : ¬∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] [inst : Lean.Grind.IsCharP α c]
        (ctx : Lean.Grind.CommRing.Context α) (p : Lean.Grind.CommRing.Poly) (k : Int),
        Lean.Grind.CommRing.Stepwise.unsat_eq_certC p k c = Bool.true → False := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eqC.h8.inst (@hc_h (Int) (0) (Lean.Grind.instCommRingInt) _ (Lean.RArray.leaf 1) (Lean.Grind.CommRing.Poly.num 1) (1) HypCheckProof.Lean.Grind.CommRing.Stepwise.unsat_eqC.h8.prem0)

-- Lean.Grind.LinearOrder.le_of_not_lt, hypothesis 3: necessary
/- FAILED: 7:364: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => b ≤ a } | 13:266: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => b ≤ a }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.LinearOrder.le_of_not_lt.h3.inst : ¬1 ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.LinearOrder.le_of_not_lt.h3.prem0 : ¬1 < 0 := by
  decide
theorem HypCheckProof.Lean.Grind.LinearOrder.le_of_not_lt.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.IsLinearOrder α] {a b : α}, ¬a < b → b ≤ a := fun hc_h => HypCheckProof.Lean.Grind.LinearOrder.le_of_not_lt.h3.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => b ≤ a : LE Nat }) (instLTNat) (@Std.IsLinearOrder.mk _ _ (@Std.IsPartialOrder.mk _ _ (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (1) (0) HypCheckProof.Lean.Grind.LinearOrder.le_of_not_lt.h3.prem0)
-/

-- Lean.Grind.LinearOrder.le_of_not_lt, hypothesis 4: necessary
/- FAILED: 7:309: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a < b } | 13:211: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a < b }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.LinearOrder.le_of_not_lt.h4.inst : ¬0 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.LinearOrder.le_of_not_lt.h4.prem0 : ¬0 < 0 := by
  decide
theorem HypCheckProof.Lean.Grind.LinearOrder.le_of_not_lt.h4 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α] {a b : α}, ¬a < b → b ≤ a := fun hc_h => HypCheckProof.Lean.Grind.LinearOrder.le_of_not_lt.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a < b : LE Nat }) (instLTNat) (@Std.LawfulOrderLT.mk _ _ _ (by (try dsimp only);   (intros; omega))) (0) (0) HypCheckProof.Lean.Grind.LinearOrder.le_of_not_lt.h4.prem0)
-/

-- Lean.Grind.OrderedAdd.neg_pos_iff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.neg_pos_iff.h4.inst : ¬(0 < -UInt8.ofNat 1 ↔ UInt8.ofNat 1 < 0) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.neg_pos_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommGroup M] [inst_3 : LT M]
        [inst : Std.LawfulOrderLT M] {a : M}, 0 < -a ↔ a < 0 := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.neg_pos_iff.h4.inst (@hc_h (UInt8) (instLEUInt8) _ (Lean.Grind.Ring.toAddCommGroup) (instLTUInt8) _ (UInt8.ofNat 1))

-- Lean.Grind.OrderedAdd.nsmul_nonneg, hypothesis 7: necessary
/- FAILED: 5:204: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => b ≤ a } | 27:239: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => b ≤ a }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_nonneg.h7.inst : ¬1 • 1 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_nonneg.h7 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.NatModule M]
        [inst_3 : Lean.Grind.OrderedAdd M] {k : Nat} {a : M}, 0 ≤ k • a := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.nsmul_nonneg.h7.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => b ≤ a : LE Nat }) (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule) (@Lean.Grind.OrderedAdd.mk _ _ _ _ (by (try dsimp only);   (intros; omega))) (1) (1))
-/

-- Int.Internal.Linear.cooper_dvd_left_split_ineq, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.cooper_dvd_left_split_ineq.h8.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.cooper_dvd_left_split_ineq.h8.prem0 : Int.Internal.Linear.cooper_dvd_left_split_ineq_cert (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0)
        (↑1) 1 (Int.Internal.Linear.Poly.num 1) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.cooper_dvd_left_split_ineq.h8 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly) (d : Int) (k : Nat) (b : Int)
        (p' : Int.Internal.Linear.Poly),
        Int.Internal.Linear.cooper_dvd_left_split_ineq_cert p₁ p₂ (↑k) b p' = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p' ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.cooper_dvd_left_split_ineq.h8.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (0) (1) (1) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.cooper_dvd_left_split_ineq.h8.prem0)

-- Lean.Grind.Order.le_trans, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans.h2.inst : ¬Bool.false ≠ Bool.false := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans.h2.prem0 : Bool.false ≠ Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans.h2.prem1 : Bool.true ≠ Bool.false := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_trans.h2 : ¬∀ {α : Type} [inst : LE α] {a b c : α}, a ≤ b → b ≤ c → a ≤ c := fun hc_h => HypCheckProof.Lean.Grind.Order.le_trans.h2.inst (@hc_h (Bool) ({ le := fun (a b : Bool) => a ≠ b : LE Bool }) (Bool.false) (Bool.true) (Bool.false) HypCheckProof.Lean.Grind.Order.le_trans.h2.prem0 HypCheckProof.Lean.Grind.Order.le_trans.h2.prem1)

-- Int.Internal.Linear.cooper_dvd_right_split_ineq, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.cooper_dvd_right_split_ineq.h8.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.cooper_dvd_right_split_ineq.h8.prem0 : Int.Internal.Linear.cooper_dvd_right_split_ineq_cert (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.num 0)
        (↑0) 1 (Int.Internal.Linear.Poly.num 1) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.cooper_dvd_right_split_ineq.h8 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly) (d : Int) (k : Nat) (a : Int)
        (p' : Int.Internal.Linear.Poly),
        Int.Internal.Linear.cooper_dvd_right_split_ineq_cert p₁ p₂ (↑k) a p' = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p' ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.cooper_dvd_right_split_ineq.h8.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (0) (0) (1) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.cooper_dvd_right_split_ineq.h8.prem0)

-- Int.Internal.Linear.cooper_dvd_left_split_dvd2, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.cooper_dvd_left_split_dvd2.h8.inst : ¬0 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.cooper_dvd_left_split_dvd2.h8.prem0 : Int.Internal.Linear.cooper_dvd_left_split_dvd2_cert (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) 0
        1 0 (Int.Internal.Linear.Poly.num 1) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.cooper_dvd_left_split_dvd2.h8 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly) (d : Int) (k : Nat) (d' : Int)
        (p' : Int.Internal.Linear.Poly),
        Int.Internal.Linear.cooper_dvd_left_split_dvd2_cert p₁ p₃ d k d' p' = Bool.true →
          d' ∣ Int.Internal.Linear.Poly.denote' ctx p' := fun hc_h => HypCheckProof.Int.Internal.Linear.cooper_dvd_left_split_dvd2.h8.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (0) (1) (0) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.cooper_dvd_left_split_dvd2.h8.prem0)

-- Lean.Grind.CommRing.Poly.denote_substInv, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_substInv.h7.inst : Not
      (@Eq Rat
        (@Lean.Grind.CommRing.PolyQ.denote Rat Lean.Grind.instFieldRat
          (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).substInv
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
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_substInv.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (ctx : Lean.Grind.CommRing.Context α) (p : Lean.Grind.CommRing.Poly) (x : Lean.Grind.CommRing.Var) (c : Nat),
        @Eq α (@Lean.Grind.CommRing.PolyQ.denote α inst ctx (p.substInv x c))
          (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_substInv.h7.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))

-- Lean.Grind.CommRing.Poly.denote_mulByMonC_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulByMonC_k.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mulByMonC_k
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
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulByMonC_k.h3.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).isMon_k
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulByMonC_k.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        {p : Lean.Grind.CommRing.Poly} (q : Lean.Grind.CommRing.Poly),
        @Eq Bool p.isMon_k Bool.true →
          @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (p.mulByMonC_k q c))
            (@HMul.hMul α α α
              (@instHMul α
                (@Lean.Grind.Semiring.toMul α
                  (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx q))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulByMonC_k.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulByMonC_k.h3.prem0)

-- Lean.Grind.CommRing.Poly.denote_mulByMonC_k, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulByMonC_k.h7.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).mulByMonC_k
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulByMonC_k.h7 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) {p : Lean.Grind.CommRing.Poly} (q : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (p.mulByMonC_k q c))
          (@HMul.hMul α α α
            (@instHMul α
              (@Lean.Grind.Semiring.toMul α
                (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx q))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulByMonC_k.h7.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))

-- Int.Internal.Linear.cooper_right_split_ineq, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.cooper_right_split_ineq.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.cooper_right_split_ineq.h6.prem0 : Int.Internal.Linear.cooper_right_split_ineq_cert (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.num 0) (↑0)
        1 (Int.Internal.Linear.Poly.num 1) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.cooper_right_split_ineq.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly) (k : Nat) (a : Int)
        (p' : Int.Internal.Linear.Poly),
        Int.Internal.Linear.cooper_right_split_ineq_cert p₁ p₂ (↑k) a p' = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p' ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.cooper_right_split_ineq.h6.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.num 0) (0) (1) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.cooper_right_split_ineq.h6.prem0)

-- Lean.Grind.OrderedAdd.neg_le_iff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.neg_le_iff.h4.inst : ¬(-UInt8.ofNat 0 ≤ UInt8.ofNat 1 ↔ -UInt8.ofNat 1 ≤ UInt8.ofNat 0) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.neg_le_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommGroup M] {a b : M}, -a ≤ b ↔ -b ≤ a := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.neg_le_iff.h4.inst (@hc_h (UInt8) (instLEUInt8) _ (Lean.Grind.Ring.toAddCommGroup) (UInt8.ofNat 0) (UInt8.ofNat 1))

-- Int.Internal.Linear.dvd_bmod_coeffs, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_bmod_coeffs.h5.inst : ¬0 ∣
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_bmod_coeffs.h5.prem0 : 0 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_bmod_coeffs.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (d : Int) (p₁ p₂ : Int.Internal.Linear.Poly) (a : Int),
        d ∣ Int.Internal.Linear.Poly.denote' ctx p₁ → d ∣ Int.Internal.Linear.Poly.denote' ctx p₂ := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_bmod_coeffs.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) HypCheckProof.Int.Internal.Linear.dvd_bmod_coeffs.h5.prem0)

-- Int.Internal.Linear.dvd_bmod_coeffs, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_bmod_coeffs.h6.inst : ¬0 ∣
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_bmod_coeffs.h6.prem0 : Int.Internal.Linear.dvd_bmod_coeffs_cert 0 (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) 1 =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_bmod_coeffs.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (d : Int) (p₁ p₂ : Int.Internal.Linear.Poly) (a : Int),
        Int.Internal.Linear.dvd_bmod_coeffs_cert d p₁ p₂ a = Bool.true → d ∣ Int.Internal.Linear.Poly.denote' ctx p₂ := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_bmod_coeffs.h6.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (1) HypCheckProof.Int.Internal.Linear.dvd_bmod_coeffs.h6.prem0)

-- Int.Internal.Linear.of_var_eq_mul, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.of_var_eq_mul.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.of_var_eq_mul.h5.prem0 : Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0 = 1 * Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.of_var_eq_mul.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (k : Int) (y : Int.Internal.Linear.Var)
        (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Var.denote ctx x = k * Int.Internal.Linear.Var.denote ctx y →
          Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.of_var_eq_mul.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (1) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.of_var_eq_mul.h5.prem0)

-- Lean.Grind.PartialOrder.le_iff_lt_or_eq, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.PartialOrder.le_iff_lt_or_eq.h3.inst : ¬(1 ≤ 0 ↔ 1 ≠ 0 ∨ 1 = 0) := by
  decide
theorem HypCheckProof.Lean.Grind.PartialOrder.le_iff_lt_or_eq.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.IsPartialOrder α] {a b : α}, a ≤ b ↔ a < b ∨ a = b := fun hc_h => HypCheckProof.Lean.Grind.PartialOrder.le_iff_lt_or_eq.h3.inst (@hc_h (Nat) (instLENat) ({ lt := fun (a b : Nat) => a ≠ b : LT Nat }) _ (1) (0))

-- Lean.Grind.PartialOrder.le_iff_lt_or_eq, hypothesis 4: necessary
/- FAILED: 4:324: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a < b } | 14:232: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a < b }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.PartialOrder.le_iff_lt_or_eq.h4.inst : ¬(0 < 0 ↔ 0 < 0 ∨ 0 = 0) := by
  decide
theorem HypCheckProof.Lean.Grind.PartialOrder.le_iff_lt_or_eq.h4 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α] {a b : α}, a ≤ b ↔ a < b ∨ a = b := fun hc_h => HypCheckProof.Lean.Grind.PartialOrder.le_iff_lt_or_eq.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a < b : LE Nat }) (instLTNat) (@Std.LawfulOrderLT.mk _ _ _ (by (try dsimp only);   (intros; omega))) (0) (0))
-/

-- Lean.Grind.AC.imp_eq, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.imp_eq.h5.inst : ¬Lean.Grind.AC.Expr.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)) =
        Lean.Grind.AC.Expr.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Expr.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.imp_eq.h5.prem0 : Lean.Grind.AC.Expr.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Expr.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.imp_eq.h5 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (lhs rhs : Lean.Grind.AC.Expr) (s : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Expr.denote ctx rhs = Lean.Grind.AC.Seq.denote ctx s →
          Lean.Grind.AC.Expr.denote ctx lhs = Lean.Grind.AC.Expr.denote ctx rhs := fun hc_h => HypCheckProof.Lean.Grind.AC.imp_eq.h5.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)) (Lean.Grind.AC.Expr.var 0) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.imp_eq.h5.prem0)

-- Lean.Grind.AC.imp_eq, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.imp_eq.h6.inst : ¬Lean.Grind.AC.Expr.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Expr.var 0) =
        Lean.Grind.AC.Expr.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.imp_eq.h6.prem0 : Lean.Grind.AC.Expr.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Expr.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.imp_eq.h6 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (lhs rhs : Lean.Grind.AC.Expr) (s : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Expr.denote ctx lhs = Lean.Grind.AC.Seq.denote ctx s →
          Lean.Grind.AC.Expr.denote ctx lhs = Lean.Grind.AC.Expr.denote ctx rhs := fun hc_h => HypCheckProof.Lean.Grind.AC.imp_eq.h6.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (Lean.Grind.AC.Expr.var 0) ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.imp_eq.h6.prem0)

-- Lean.Grind.AC.norm_a, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.norm_a.h2.inst : ¬Lean.Grind.AC.Expr.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)).op (Lean.Grind.AC.Expr.var 0)) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.cons 1 (Lean.Grind.AC.Seq.var 0))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.norm_a.h2.prem0 : (((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)).op (Lean.Grind.AC.Expr.var 0)).toSeq.beq'
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.cons 1 (Lean.Grind.AC.Seq.var 0))) =
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.AC.norm_a.h2 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (e : Lean.Grind.AC.Expr) (s : Lean.Grind.AC.Seq),
        e.toSeq.beq' s = Bool.true → Lean.Grind.AC.Expr.denote ctx e = Lean.Grind.AC.Seq.denote ctx s := fun hc_h => HypCheckProof.Lean.Grind.AC.norm_a.h2.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)).op (Lean.Grind.AC.Expr.var 0)) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.cons 1 (Lean.Grind.AC.Seq.var 0))) HypCheckProof.Lean.Grind.AC.norm_a.h2.prem0)

-- Lean.Grind.AC.norm_a, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.norm_a.h5.inst : ¬Lean.Grind.AC.Expr.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Expr.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.norm_a.h5.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
theorem HypCheckProof.Lean.Grind.AC.norm_a.h5 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} (e : Lean.Grind.AC.Expr)
        (s : Lean.Grind.AC.Seq), Lean.Grind.AC.Expr.denote ctx e = Lean.Grind.AC.Seq.denote ctx s := fun hc_h => HypCheckProof.Lean.Grind.AC.norm_a.h5.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.norm_a.h5.prem0 (Lean.Grind.AC.Expr.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)))

-- Int.Internal.Linear.dvd_norm, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_norm.h4.inst : ¬0 ∣
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_norm.h4.prem0 : 0 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_norm.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (d : Int) (p₁ p₂ : Int.Internal.Linear.Poly),
        d ∣ Int.Internal.Linear.Poly.denote' ctx p₁ → d ∣ Int.Internal.Linear.Poly.denote' ctx p₂ := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_norm.h4.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.dvd_norm.h4.prem0)

-- Int.Internal.Linear.dvd_norm, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_norm.h5.inst : ¬0 ∣
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_norm.h5.prem0 : (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).norm_k.beq'
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_norm.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (d : Int) (p₁ p₂ : Int.Internal.Linear.Poly),
        p₁.norm_k.beq' p₂ = Bool.true → d ∣ Int.Internal.Linear.Poly.denote' ctx p₂ := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_norm.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.dvd_norm.h5.prem0)

-- Int.Internal.Linear.le_weaken, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_weaken.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_weaken.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_weaken.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly) (k : Int),
        Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_weaken.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) HypCheckProof.Int.Internal.Linear.le_weaken.h4.prem0)

-- Int.Internal.Linear.le_weaken, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_weaken.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_weaken.h5.prem0 : Int.Internal.Linear.le_weaken_cert (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) 0 =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_weaken.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly) (k : Int),
        Int.Internal.Linear.le_weaken_cert p₁ p₂ k = Bool.true → Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_weaken.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) HypCheckProof.Int.Internal.Linear.le_weaken.h5.prem0)

-- Int.Internal.Linear.eq_of_core, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_core.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_core.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) =
      Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Int.Internal.Linear.eq_of_core.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ = Int.Internal.Linear.Poly.denote' ctx p₂ →
          Int.Internal.Linear.Poly.denote' ctx p₃ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_of_core.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_of_core.h4.prem0)

-- Int.Internal.Linear.eq_of_core, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_core.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_core.h5.prem0 : Int.Internal.Linear.eq_of_core_cert (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
        (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_of_core.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.eq_of_core_cert p₁ p₂ p₃ = Bool.true → Int.Internal.Linear.Poly.denote' ctx p₃ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_of_core.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_of_core.h5.prem0)

-- Int.Internal.Linear.of_var_eq, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.of_var_eq.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.of_var_eq.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (k : Int) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Var.denote ctx x = k → Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.of_var_eq.h4.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) rfl)

-- Int.Internal.Linear.of_var_eq, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.of_var_eq.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.of_var_eq.h5.prem0 : Int.Internal.Linear.of_var_eq_cert 0 0 (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) = Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.of_var_eq.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (k : Int) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.of_var_eq_cert x k p = Bool.true → Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.of_var_eq.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.of_var_eq.h5.prem0)

-- Int.Internal.Linear.eq_norm_expr, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm_expr.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm_expr.h4.prem0 : Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
      Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Int.Internal.Linear.eq_norm_expr.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Expr.denote_k ctx lhs = Int.Internal.Linear.Expr.denote_k ctx rhs →
          Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_norm_expr.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_norm_expr.h4.prem0)

-- Int.Internal.Linear.eq_norm_expr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm_expr.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm_expr.h5.prem0 : Int.Internal.Linear.norm_eq_cert (Int.Internal.Linear.Expr.var 0) (Int.Internal.Linear.Expr.num 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_norm_expr.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.norm_eq_cert lhs rhs p = Bool.true → Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_norm_expr.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_norm_expr.h5.prem0)

-- Int.Internal.Linear.eq_of_core_rfl, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_core_rfl.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_core_rfl.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) =
      Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Int.Internal.Linear.eq_of_core_rfl.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ = Int.Internal.Linear.Poly.denote' ctx p₂ →
          Int.Internal.Linear.Poly.denote' ctx p₃ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_of_core_rfl.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_of_core_rfl.h4.prem0)

-- Int.Internal.Linear.eq_of_core_rfl, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_of_core_rfl.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.combine_mul_k 1 (-1) (Int.Internal.Linear.Poly.num 0)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) =
        0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_of_core_rfl.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        p₃ = Int.Internal.Linear.Poly.combine_mul_k 1 (-1) p₁ p₂ → Int.Internal.Linear.Poly.denote' ctx p₃ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_of_core_rfl.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.combine_mul_k 1 (-1) (Int.Internal.Linear.Poly.num 0)
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) rfl)

-- Int.Internal.Linear.le_coeff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_coeff.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_coeff.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_coeff.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly) (k : Int),
        Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_coeff.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) HypCheckProof.Int.Internal.Linear.le_coeff.h4.prem0)

-- Int.Internal.Linear.le_coeff, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_coeff.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_coeff.h5.prem0 : Int.Internal.Linear.le_coeff_cert (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) 1 =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_coeff.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly) (k : Int),
        Int.Internal.Linear.le_coeff_cert p₁ p₂ k = Bool.true → Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_coeff.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (1) HypCheckProof.Int.Internal.Linear.le_coeff.h5.prem0)

-- Int.Internal.Linear.eq_def'_rfl, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def'_rfl.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def'_rfl.h4.prem0 : Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0 =
      Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_def'_rfl.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (e : Int.Internal.Linear.Expr)
        (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Var.denote ctx x = Int.Internal.Linear.Expr.denote_k ctx e →
          Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_def'_rfl.h4.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Expr.var 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_def'_rfl.h4.prem0)

-- Int.Internal.Linear.eq_def'_rfl, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def'_rfl.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add (-1) 0 (Int.Internal.Linear.Expr.num 0).norm_k) =
        0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_def'_rfl.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (e : Int.Internal.Linear.Expr)
        (p : Int.Internal.Linear.Poly),
        p = Int.Internal.Linear.Poly.add (-1) x e.norm_k → Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_def'_rfl.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add (-1) 0 (Int.Internal.Linear.Expr.num 0).norm_k) rfl)

-- Int.Internal.Linear.diseq_split, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_split.h4.inst : ¬(Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
          0 ∨
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
          0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_split.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≠
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_split.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ ≠ 0 →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 ∨ Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_split.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.diseq_split.h4.prem0)

-- Int.Internal.Linear.diseq_split, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_split.h5.inst : ¬(Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) ≤ 0 ∨
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) ≤ 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_split.h5.prem0 : Int.Internal.Linear.diseq_split_cert (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 1)
        (Int.Internal.Linear.Poly.num 1) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_split.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.diseq_split_cert p₁ p₂ p₃ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 ∨ Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_split.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.diseq_split.h5.prem0)

-- Int.Internal.Linear.eq_def_rfl, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def_rfl.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def_rfl.h4.prem0 : Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0 =
      Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_def_rfl.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (xPoly p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Var.denote ctx x = Int.Internal.Linear.Poly.denote' ctx xPoly →
          Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_def_rfl.h4.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_def_rfl.h4.prem0)

-- Int.Internal.Linear.eq_def_rfl, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def_rfl.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add (-1) 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_def_rfl.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (xPoly p : Int.Internal.Linear.Poly),
        p = Int.Internal.Linear.Poly.add (-1) x xPoly → Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_def_rfl.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add (-1) 0 (Int.Internal.Linear.Poly.num 0)) rfl)

-- Int.Internal.Linear.not_eq_norm_expr, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.not_eq_norm_expr.h4.inst : ¬¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.not_eq_norm_expr.h4.prem0 : ¬Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
        Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.not_eq_norm_expr.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        ¬Int.Internal.Linear.Expr.denote_k ctx lhs = Int.Internal.Linear.Expr.denote_k ctx rhs →
          ¬Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.not_eq_norm_expr.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.var 0) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.not_eq_norm_expr.h4.prem0)

-- Int.Internal.Linear.not_eq_norm_expr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.not_eq_norm_expr.h5.inst : ¬¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.not_eq_norm_expr.h5.prem0 : Int.Internal.Linear.norm_eq_cert (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0)
        (Int.Internal.Linear.Poly.num 0) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.not_eq_norm_expr.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.norm_eq_cert lhs rhs p = Bool.true → ¬Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.not_eq_norm_expr.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.not_eq_norm_expr.h5.prem0)

-- Int.Internal.Linear.diseq_coeff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_coeff.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_coeff.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≠
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_coeff.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly) (k : Int),
        Int.Internal.Linear.Poly.denote' ctx p ≠ 0 → Int.Internal.Linear.Poly.denote' ctx p' ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_coeff.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) (0) HypCheckProof.Int.Internal.Linear.diseq_coeff.h4.prem0)

-- Int.Internal.Linear.diseq_coeff, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_coeff.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_coeff.h5.prem0 : Int.Internal.Linear.eq_coeff_cert (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) 1 = Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_coeff.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly) (k : Int),
        Int.Internal.Linear.eq_coeff_cert p p' k = Bool.true → Int.Internal.Linear.Poly.denote' ctx p' ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_coeff.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (1) HypCheckProof.Int.Internal.Linear.diseq_coeff.h5.prem0)

-- Int.Internal.Linear.of_var_eq_var, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.of_var_eq_var.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.of_var_eq_var.h4.prem0 : Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0 = Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Int.Internal.Linear.of_var_eq_var.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (x y : Int.Internal.Linear.Var) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Var.denote ctx x = Int.Internal.Linear.Var.denote ctx y →
          Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.of_var_eq_var.h4.inst (@hc_h (Lean.RArray.leaf 1) (0) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.of_var_eq_var.h4.prem0)

-- Int.Internal.Linear.of_var_eq_var, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.of_var_eq_var.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.branch 1 (Lean.RArray.leaf 1) (Lean.RArray.leaf 2))
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0))) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.of_var_eq_var.h5.prem0 : Int.Internal.Linear.of_var_eq_var_cert 0 1
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0))) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.of_var_eq_var.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (x y : Int.Internal.Linear.Var) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.of_var_eq_var_cert x y p = Bool.true → Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.of_var_eq_var.h5.inst (@hc_h (Lean.RArray.branch 1 (Lean.RArray.leaf 1) (Lean.RArray.leaf 2)) (0) (1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0))) HypCheckProof.Int.Internal.Linear.of_var_eq_var.h5.prem0)

-- Lean.Grind.beq_eq_true_of_eq, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.beq_eq_true_of_eq.h2.inst : ¬(0 != 0) = Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.beq_eq_true_of_eq.h2 : ¬∀ {α : Type} {x : BEq α} {a b : α}, a = b → (a == b) = Bool.true := fun hc_h => HypCheckProof.Lean.Grind.beq_eq_true_of_eq.h2.inst (@hc_h (Nat) ({ beq := fun (a b : Nat) => a != b : BEq Nat }) (0) (0) rfl)

-- Lean.Grind.CommRing.PPoly.dsum_mul_pow, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.dsum_mul_pow.h4.inst : ¬Lean.Grind.CommRing.PPoly.dsum 2 (2 * 2 ^ 0) = 2 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.dsum_mul_pow.h4.prem0 : 1 < 2 := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.dsum_mul_pow.h4 : ¬∀ {B : Nat}, 1 < B → ∀ (x k : Nat), Lean.Grind.CommRing.PPoly.dsum B (k * B ^ x) = k := fun hc_h => HypCheckProof.Lean.Grind.CommRing.PPoly.dsum_mul_pow.h4.inst (@hc_h (2) HypCheckProof.Lean.Grind.CommRing.PPoly.dsum_mul_pow.h4.prem0 (0) (2))

-- Lean.Grind.AC.Seq.denote_sort, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_sort.h3.inst : ¬Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 1 (Lean.Grind.AC.Seq.var 0)).sort =
        Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 1 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_sort.h3.prem0 : Std.Associative
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   (intros; simp_all; done)))
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_sort.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op} (s : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx s.sort = Lean.Grind.AC.Seq.denote ctx s := fun hc_h => HypCheckProof.Lean.Grind.AC.Seq.denote_sort.h3.inst (@hc_h (Nat) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
      op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.Seq.denote_sort.h3.prem0 (Lean.Grind.AC.Seq.cons 1 (Lean.Grind.AC.Seq.var 0)))

-- Lean.Grind.CommRing.Poly.denote_signBC_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_signBC_k.h3.inst : ¬Lean.Grind.CommRing.Poly.denote (Lean.RArray.leaf 1)
          ((Lean.Grind.CommRing.Poly.add 1
                (Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num 0)).signBC_k
            1 Bool.true) =
        bif Bool.true then
          -Lean.Grind.CommRing.Poly.denote (Lean.RArray.leaf 1)
              (Lean.Grind.CommRing.Poly.add 1
                (Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num 0))
        else
          Lean.Grind.CommRing.Poly.denote (Lean.RArray.leaf 1)
            (Lean.Grind.CommRing.Poly.add 1
              (Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num 0)) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_signBC_k.h3 : ¬∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (p : Lean.Grind.CommRing.Poly) (s : Bool),
        Lean.Grind.CommRing.Poly.denote ctx (p.signBC_k c s) =
          bif s then -Lean.Grind.CommRing.Poly.denote ctx p else Lean.Grind.CommRing.Poly.denote ctx p := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_signBC_k.h3.inst (@hc_h (Int) (1) (Lean.Grind.instCommRingInt) (Lean.RArray.leaf 1) (Lean.Grind.CommRing.Poly.add 1
      (Lean.Grind.CommRing.Mon.mult { x := 0, k := 1 : Lean.Grind.CommRing.Power } Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num 0)) (Bool.true))

-- Lean.Grind.CommRing.Poly.denoteList_pairs_k, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteList_pairs_k.h4.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denoteList Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.pairs_k
            (fun (a a_1 : Lean.Grind.CommRing.Poly) =>
              Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (@List.cons Lean.Grind.CommRing.Poly
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
              (@List.nil Lean.Grind.CommRing.Poly))
            (@Option.some Lean.Grind.CommRing.Poly
              (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
          (@Option.rec Lean.Grind.CommRing.Poly (fun (x : Option Lean.Grind.CommRing.Poly) => Int)
            (@OfNat.ofNat Int (nat_lit 0)
              (@Zero.toOfNat0 Int
                (@Lean.Grind.AddCommMonoid.toZero Int
                  (@Lean.Grind.NatModule.toAddCommMonoid Int
                    (@Lean.Grind.Semiring.toNatModule Int
                      (@Lean.Grind.CommSemiring.toSemiring Int
                        (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))
            (fun (p : Lean.Grind.CommRing.Poly) =>
              @Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
                (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) p)
            (@Option.some Lean.Grind.CommRing.Poly
              (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))
          (@Lean.Grind.CommRing.Poly.denoteList Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@List.cons Lean.Grind.CommRing.Poly
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
              (@List.nil Lean.Grind.CommRing.Poly))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteList_pairs_k.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (f : Lean.Grind.CommRing.Poly → Lean.Grind.CommRing.Poly → Lean.Grind.CommRing.Poly)
        (ps : List Lean.Grind.CommRing.Poly) (pend : Option Lean.Grind.CommRing.Poly),
        @Eq α
          (@Lean.Grind.CommRing.Poly.denoteList α (@Lean.Grind.CommRing.toRing α inst) ctx
            (Lean.Grind.CommRing.Poly.pairs_k f ps pend))
          (@HAdd.hAdd α α α
            (@instHAdd α
              (@Lean.Grind.Semiring.toAdd α
                (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
            (@Option.rec Lean.Grind.CommRing.Poly (fun (x : Option Lean.Grind.CommRing.Poly) => α)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))
              (fun (p : Lean.Grind.CommRing.Poly) =>
                @Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
              pend)
            (@Lean.Grind.CommRing.Poly.denoteList α (@Lean.Grind.CommRing.toRing α inst) ctx ps))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denoteList_pairs_k.h4.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (fun (a a_1 : Lean.Grind.CommRing.Poly) =>
      Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@List.cons Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@List.nil Lean.Grind.CommRing.Poly)) (@Option.some Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))

-- Lean.Grind.CommRing.Poly.denote_mulC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulC.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mulC
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
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (p₁.mulC p₂ c))
          (@HMul.hMul α α α
            (@instHMul α
              (@Lean.Grind.Semiring.toMul α
                (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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

-- Lean.Grind.CommRing.eq_norm_unsat_expr, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_unsat_expr.h6.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_norm_unsat_expr.h6 : Not
      (∀ (ctx : Lean.Grind.CommRing.Context Int) (lhs rhs : Lean.Grind.CommRing.Expr) (q : Lean.Grind.CommRing.Poly)
        (k c : Int),
        @Eq Prop
          (@Eq Int
            (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) ctx rhs))
          False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_norm_unsat_expr.h6.inst (@hc_h (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Lean.Grind.Linarith.eq_normN, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.eq_normN.h5.inst : Not
      (@Eq Int
        (@Lean.Grind.Linarith.Expr.denoteN Int
          (@Lean.Grind.Semiring.toNatModule Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Expr.zero)
        (@Lean.Grind.Linarith.Expr.denoteN Int
          (@Lean.Grind.Semiring.toNatModule Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.eq_normN.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.NatModule α] (ctx : Lean.Grind.Linarith.Context α)
        (lhs rhs : Lean.Grind.Linarith.Expr),
        @Eq α (@Lean.Grind.Linarith.Expr.denoteN α inst ctx lhs) (@Lean.Grind.Linarith.Expr.denoteN α inst ctx rhs)) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.eq_normN.h5.inst (@hc_h (Int) (@Lean.Grind.Semiring.toNatModule Int
      (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))

-- Int.Internal.Linear.lt_norm_expr_k, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.lt_norm_expr_k.h5.inst : ¬(Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) <
          Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        (Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) <
          Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0)) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.lt_norm_expr_k.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs lhs' rhs' : Int.Internal.Linear.Expr),
        (Int.Internal.Linear.Expr.denote_k ctx lhs < Int.Internal.Linear.Expr.denote_k ctx rhs) =
          (Int.Internal.Linear.Expr.denote_k ctx lhs' < Int.Internal.Linear.Expr.denote_k ctx rhs') := fun hc_h => HypCheckProof.Int.Internal.Linear.lt_norm_expr_k.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.var 0))

-- Int.Internal.Linear.norm_eq_var_const_k, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.norm_eq_var_const_k.h5.inst : ¬(Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
          Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        (Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0 = 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.norm_eq_var_const_k.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (x : Int.Internal.Linear.Var) (k : Int),
        (Int.Internal.Linear.Expr.denote_k ctx lhs = Int.Internal.Linear.Expr.denote_k ctx rhs) =
          (Int.Internal.Linear.Var.denote ctx x = k) := fun hc_h => HypCheckProof.Int.Internal.Linear.norm_eq_var_const_k.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (0) (0))

-- Int.Internal.Linear.le_unsat, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_unsat.h2.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_unsat.h2.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_unsat.h2 : ¬∀ (ctx : Int.Internal.Linear.Context) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p ≤ 0 → False := fun hc_h => HypCheckProof.Int.Internal.Linear.le_unsat.h2.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.le_unsat.h2.prem0)

-- Int.Internal.Linear.le_unsat, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_unsat.h3.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_unsat.h3.prem0 : (Int.Internal.Linear.Poly.num 1).isUnsatLe_k = Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_unsat.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p : Int.Internal.Linear.Poly), p.isUnsatLe_k = Bool.true → False := fun hc_h => HypCheckProof.Int.Internal.Linear.le_unsat.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.le_unsat.h3.prem0)

-- Int.Internal.Linear.norm_le_coeff_k, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.norm_le_coeff_k.h5.inst : ¬(Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) ≤
          Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        (Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
          0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.norm_le_coeff_k.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly) (k : Int),
        (Int.Internal.Linear.Expr.denote_k ctx lhs ≤ Int.Internal.Linear.Expr.denote_k ctx rhs) =
          (Int.Internal.Linear.Poly.denote' ctx p ≤ 0) := fun hc_h => HypCheckProof.Int.Internal.Linear.norm_le_coeff_k.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0))

-- Int.Internal.Linear.le_norm_expr_k, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm_expr_k.h5.inst : ¬(Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) ≤
          Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        (Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0) ≤
          Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_norm_expr_k.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs lhs' rhs' : Int.Internal.Linear.Expr),
        (Int.Internal.Linear.Expr.denote_k ctx lhs ≤ Int.Internal.Linear.Expr.denote_k ctx rhs) =
          (Int.Internal.Linear.Expr.denote_k ctx lhs' ≤ Int.Internal.Linear.Expr.denote_k ctx rhs') := fun hc_h => HypCheckProof.Int.Internal.Linear.le_norm_expr_k.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.var 0) (Int.Internal.Linear.Expr.num 0))

-- Lean.Grind.CommRing.Poly.denote_foldr_k, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_foldr_k.h4.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.foldr_k
            (fun (a a_1 : Lean.Grind.CommRing.Poly) =>
              Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
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
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_foldr_k.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (f : Lean.Grind.CommRing.Poly → Lean.Grind.CommRing.Poly → Lean.Grind.CommRing.Poly)
        (ps : List Lean.Grind.CommRing.Poly),
        @Eq α
          (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
            (Lean.Grind.CommRing.Poly.foldr_k f ps))
          (@Lean.Grind.CommRing.Poly.denoteList α (@Lean.Grind.CommRing.toRing α inst) ctx ps)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_foldr_k.h4.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (fun (a a_1 : Lean.Grind.CommRing.Poly) =>
      Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@List.cons Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@List.nil Lean.Grind.CommRing.Poly)))

-- Lean.Grind.CommRing.Poly.normEq0_eq, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.normEq0_eq.h5.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).normEq0
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.normEq0_eq.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (p : Lean.Grind.CommRing.Poly)
        (c : Nat),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (p.normEq0 c))
          (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.normEq0_eq.h5.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))

-- Lean.Grind.CommRing.Poly.denote_mulByMon_k, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulByMon_k.h5.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).mulByMon_k
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulByMon_k.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) {p : Lean.Grind.CommRing.Poly}
        (q : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (p.mulByMon_k q))
          (@HMul.hMul α α α
            (@instHMul α
              (@Lean.Grind.Semiring.toMul α
                (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx q))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_mulByMon_k.h5.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))

-- Lean.Grind.CommRing.Poly.denote_sumB_k, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_sumB_k.h4.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.sumB_k
            (fun (a a_1 : Lean.Grind.CommRing.Poly) =>
              Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (@List.cons Lean.Grind.CommRing.Poly
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
              (@List.cons Lean.Grind.CommRing.Poly
                (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  (Lean.Grind.CommRing.Mon.mult
                    { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                      k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                    Lean.Grind.CommRing.Mon.unit)
                  (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
                (@List.nil Lean.Grind.CommRing.Poly)))))
        (@Lean.Grind.CommRing.Poly.denoteList Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@List.cons Lean.Grind.CommRing.Poly
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (@List.cons Lean.Grind.CommRing.Poly
              (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
              (@List.nil Lean.Grind.CommRing.Poly))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_sumB_k.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (f : Lean.Grind.CommRing.Poly → Lean.Grind.CommRing.Poly → Lean.Grind.CommRing.Poly)
        (ps : List Lean.Grind.CommRing.Poly),
        @Eq α
          (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
            (Lean.Grind.CommRing.Poly.sumB_k f ps))
          (@Lean.Grind.CommRing.Poly.denoteList α (@Lean.Grind.CommRing.toRing α inst) ctx ps)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_sumB_k.h4.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (fun (a a_1 : Lean.Grind.CommRing.Poly) =>
      Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@List.cons Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@List.cons Lean.Grind.CommRing.Poly
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@List.nil Lean.Grind.CommRing.Poly))))

-- Int.Internal.Linear.norm_eq_var, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.norm_eq_var.h5.inst : ¬(Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
          Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0)) =
        (Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0 = Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.norm_eq_var.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (x y : Int.Internal.Linear.Var),
        (Int.Internal.Linear.Expr.denote ctx lhs = Int.Internal.Linear.Expr.denote ctx rhs) =
          (Int.Internal.Linear.Var.denote ctx x = Int.Internal.Linear.Var.denote ctx y) := fun hc_h => HypCheckProof.Int.Internal.Linear.norm_eq_var.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.var 0) (0) (0))

-- Lean.Grind.CommRing.Expr.denote_pow_one_of, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_one_of.h5.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).pow
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_one_of.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr)
        (pa : Lean.Grind.CommRing.Poly),
        @Eq α
          (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
            (a.pow (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_pow_one_of.h5.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))

-- Lean.Grind.CommRing.lt_int_module, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_int_module.h5.inst : Not
      (@LT.lt Int Int.instLTInt
        (@Lean.Grind.CommRing.Poly.denoteAsIntModule Int Lean.Grind.instCommRingInt
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_int_module.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LT α] (ctx : Lean.Grind.CommRing.Context α)
        (p : Lean.Grind.CommRing.Poly),
        @LT.lt α inst_1 (@Lean.Grind.CommRing.Poly.denoteAsIntModule α inst ctx p)
          (@OfNat.ofNat α (nat_lit 0)
            (@Zero.toOfNat0 α
              (@Lean.Grind.AddCommMonoid.toZero α
                (@Lean.Grind.NatModule.toAddCommMonoid α
                  (@Lean.Grind.Semiring.toNatModule α
                    (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_int_module.h5.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLTInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))

-- Lean.Grind.CommRing.le_int_module, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_int_module.h5.inst : Not
      (@LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.CommRing.le_int_module.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] (ctx : Lean.Grind.CommRing.Context α)
        (p : Lean.Grind.CommRing.Poly),
        @LE.le α inst_1 (@Lean.Grind.CommRing.Poly.denoteAsIntModule α inst ctx p)
          (@OfNat.ofNat α (nat_lit 0)
            (@Zero.toOfNat0 α
              (@Lean.Grind.AddCommMonoid.toZero α
                (@Lean.Grind.NatModule.toAddCommMonoid α
                  (@Lean.Grind.Semiring.toNatModule α
                    (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_int_module.h5.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))

-- Int.Internal.Linear.eq_norm_expr_k, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm_expr_k.h5.inst : ¬(Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
          Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        (Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
          Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0)) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_norm_expr_k.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs lhs' rhs' : Int.Internal.Linear.Expr),
        (Int.Internal.Linear.Expr.denote_k ctx lhs = Int.Internal.Linear.Expr.denote_k ctx rhs) =
          (Int.Internal.Linear.Expr.denote_k ctx lhs' = Int.Internal.Linear.Expr.denote_k ctx rhs') := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_norm_expr_k.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.var 0))

-- Lean.Grind.CommRing.Expr.denote_toPolyC_nc, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPolyC_nc.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).toPolyC_nc
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPolyC_nc.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α)
        (e : Lean.Grind.CommRing.Expr),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α inst ctx (e.toPolyC_nc c))
          (@Lean.Grind.CommRing.Expr.denote α inst ctx e)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPolyC_nc.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))

-- Lean.Grind.CommRing.Expr.eq_of_toPoly_eq, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPoly_eq.h5.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPoly_eq.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
          (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPoly_eq.h5.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))

-- Int.Internal.Linear.norm_eq_var_k, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.norm_eq_var_k.h5.inst : ¬(Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
          Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0)) =
        (Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0 = Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.norm_eq_var_k.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (x y : Int.Internal.Linear.Var),
        (Int.Internal.Linear.Expr.denote_k ctx lhs = Int.Internal.Linear.Expr.denote_k ctx rhs) =
          (Int.Internal.Linear.Var.denote ctx x = Int.Internal.Linear.Var.denote ctx y) := fun hc_h => HypCheckProof.Int.Internal.Linear.norm_eq_var_k.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.var 0) (0) (0))

-- Int.Internal.Linear.norm_eq_coeff_k, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.norm_eq_coeff_k.h5.inst : ¬(Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
          Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        (Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
          0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.norm_eq_coeff_k.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly) (k : Int),
        (Int.Internal.Linear.Expr.denote_k ctx lhs = Int.Internal.Linear.Expr.denote_k ctx rhs) =
          (Int.Internal.Linear.Poly.denote' ctx p = 0) := fun hc_h => HypCheckProof.Int.Internal.Linear.norm_eq_coeff_k.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0))

-- Lean.Grind.IsCharP.intCast_ext_iff, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.IsCharP.intCast_ext_iff.h3.inst : Not
      (Iff
        (@Eq Int
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@Eq Int
          (@HMod.hMod Int Int Int (@instHMod Int Int.instMod) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HMod.hMod Int Int Int (@instHMod Int Int.instMod) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.IsCharP.intCast_ext_iff.h3 : Not
      (∀ (p : Nat) {α : Type} [inst : Lean.Grind.Ring α] {x y : Int},
        Iff (@Eq α (@Int.cast α (@Lean.Grind.Ring.intCast α inst) x) (@Int.cast α (@Lean.Grind.Ring.intCast α inst) y))
          (@Eq Int (@HMod.hMod Int Int Int (@instHMod Int Int.instMod) x (@Nat.cast Int instNatCastInt p))
            (@HMod.hMod Int Int Int (@instHMod Int Int.instMod) y (@Nat.cast Int instNatCastInt p)))) := fun hc_h => HypCheckProof.Lean.Grind.IsCharP.intCast_ext_iff.h3.inst (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))

-- Lean.Grind.CommRing.Expr.denote_toPolyC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPolyC.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).toPolyC
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPolyC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (e : Lean.Grind.CommRing.Expr),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (e.toPolyC c))
          (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx e)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPolyC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))

-- Lean.Grind.CommRing.Expr.eq_of_toPoly_nc_eq, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPoly_nc_eq.h5.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPoly_nc_eq.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α inst ctx a) (@Lean.Grind.CommRing.Expr.denote α inst ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPoly_nc_eq.h5.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))

-- Lean.Grind.Field.zpow_add, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.zpow_add.h3.inst : Not
      (@Eq Rat
        (@HPow.hPow Rat Int Rat (@Lean.Grind.Field.zpow Rat Lean.Grind.instFieldRat)
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        (@HMul.hMul Rat Rat Rat
          (@instHMul Rat
            (@Lean.Grind.Semiring.toMul Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@HPow.hPow Rat Int Rat (@Lean.Grind.Field.zpow Rat Lean.Grind.instFieldRat)
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@HPow.hPow Rat Int Rat (@Lean.Grind.Field.zpow Rat Lean.Grind.instFieldRat)
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.zpow_add.h3 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] {a : α} (m n : Int),
        @Eq α
          (@HPow.hPow α Int α (@Lean.Grind.Field.zpow α inst) a (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) m n))
          (@HMul.hMul α α α
            (@instHMul α
              (@Lean.Grind.Semiring.toMul α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
            (@HPow.hPow α Int α (@Lean.Grind.Field.zpow α inst) a m)
            (@HPow.hPow α Int α (@Lean.Grind.Field.zpow α inst) a n))) := fun hc_h => HypCheckProof.Lean.Grind.Field.zpow_add.h3.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))

-- Lean.Grind.Field.div_add, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.div_add.h5.inst : Not
      (@Eq Rat
        (@HAdd.hAdd Rat Rat Rat
          (@instHAdd Rat
            (@Lean.Grind.Semiring.toAdd Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat (@Lean.Grind.Field.toDiv Rat Lean.Grind.instFieldRat))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
        (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat (@Lean.Grind.Field.toDiv Rat Lean.Grind.instFieldRat))
          (@HAdd.hAdd Rat Rat Rat
            (@instHAdd Rat
              (@Lean.Grind.Semiring.toAdd Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@HMul.hMul Rat Rat Rat
              (@instHMul Rat
                (@Lean.Grind.Semiring.toMul Rat
                  (@Lean.Grind.CommSemiring.toSemiring Rat
                    (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
              (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
              (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.div_add.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] {x y z : α},
        @Eq α
          (@HAdd.hAdd α α α
            (@instHAdd α
              (@Lean.Grind.Semiring.toAdd α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
            (@HDiv.hDiv α α α (@instHDiv α (@Lean.Grind.Field.toDiv α inst)) x y) z)
          (@HDiv.hDiv α α α (@instHDiv α (@Lean.Grind.Field.toDiv α inst))
            (@HAdd.hAdd α α α
              (@instHAdd α
                (@Lean.Grind.Semiring.toAdd α
                  (@Lean.Grind.CommSemiring.toSemiring α
                    (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
              x
              (@HMul.hMul α α α
                (@instHMul α
                  (@Lean.Grind.Semiring.toMul α
                    (@Lean.Grind.CommSemiring.toSemiring α
                      (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
                y z))
            y)) := fun hc_h => HypCheckProof.Lean.Grind.Field.div_add.h5.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))

-- Lean.Grind.CommRing.Poly.denote_cancelInvs, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_cancelInvs.h5.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  (Lean.Grind.CommRing.Mon.mult
                    { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1)),
                      k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                    Lean.Grind.CommRing.Mon.unit))
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).cancelInvs
            (@List.cons (Prod Lean.Grind.CommRing.Var Lean.Grind.CommRing.Var)
              (@Prod.mk Lean.Grind.CommRing.Var Lean.Grind.CommRing.Var
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@List.nil (Prod Lean.Grind.CommRing.Var Lean.Grind.CommRing.Var)))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_cancelInvs.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (p : Lean.Grind.CommRing.Poly)
        (ainvs : Lean.Grind.CommRing.InvAtoms),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (p.cancelInvs ainvs))
          (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_cancelInvs.h5.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit))
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@List.cons (Prod Lean.Grind.CommRing.Var Lean.Grind.CommRing.Var)
      (@Prod.mk Lean.Grind.CommRing.Var Lean.Grind.CommRing.Var (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Lean.Grind.CommRing.Var))))

-- Lean.Grind.bne_eq_decide_not_eq, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.bne_eq_decide_not_eq.h2.inst : Not
      (@Eq Bool
        (@bne Nat
          (@BEq.mk Nat fun (a b : Nat) =>
            @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
              (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Decidable.decide
          (Not
            (@Eq Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@instDecidableNot
            (@Eq Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (instDecidableEqNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.bne_eq_decide_not_eq.h2 : Not
      (∀ {α : Type} {x : BEq α} [inst : DecidableEq α] (a b : α),
        @Eq Bool (@bne α x a b) (@Decidable.decide (Not (@Eq α a b)) (@instDecidableNot (@Eq α a b) (inst a b)))) := fun hc_h => HypCheckProof.Lean.Grind.bne_eq_decide_not_eq.h2.inst (@hc_h (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))

-- Int.Internal.Linear.norm_dvd_k, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.norm_dvd_k.h4.inst : ¬(0 ∣ Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        (0 ∣
          Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.norm_dvd_k.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (k : Int) (e : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        (k ∣ Int.Internal.Linear.Expr.denote_k ctx e) = (k ∣ Int.Internal.Linear.Poly.denote' ctx p) := fun hc_h => HypCheckProof.Int.Internal.Linear.norm_dvd_k.h4.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)))

-- Lean.Grind.AC.Expr.denote_toSeq', hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Expr.denote_toSeq'.h2.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)).toSeq' (Lean.Grind.AC.Seq.var 0)) =
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b :
              Lean.Grind.AC.Context Nat }.op
          (Lean.Grind.AC.Expr.denote
            { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b :
              Lean.Grind.AC.Context Nat }
            ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)))
          (Lean.Grind.AC.Seq.denote
            { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b :
              Lean.Grind.AC.Context Nat }
            (Lean.Grind.AC.Seq.var 0)) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.Expr.denote_toSeq'.h2 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (e : Lean.Grind.AC.Expr) (s : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx (e.toSeq' s) =
          ctx.op (Lean.Grind.AC.Expr.denote ctx e) (Lean.Grind.AC.Seq.denote ctx s) := fun hc_h => HypCheckProof.Lean.Grind.AC.Expr.denote_toSeq'.h2.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)) (Lean.Grind.AC.Seq.var 0))

-- Lean.Grind.AC.eq_orient, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_orient.h4.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.eq_orient.h4 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) (lhs rhs : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx rhs = Lean.Grind.AC.Seq.denote ctx lhs := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_orient.h4.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a - b : Lean.Grind.AC.Context Nat }) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)))

-- Lean.Grind.Preorder.lt_irrefl, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Preorder.lt_irrefl.h3.inst : ¬¬0 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.Preorder.lt_irrefl.h3 : ¬∀ {α : Type} [inst : LE α] [inst : LT α] (a : α), ¬a < a := fun hc_h => HypCheckProof.Lean.Grind.Preorder.lt_irrefl.h3.inst (@hc_h (Nat) (instLENat) ({ lt := fun (a b : Nat) => a ≤ b : LT Nat }) (0))

-- Lean.Grind.Order.lt_eq_false, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false.h3.inst : ¬(0 ≤ 0) = False := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false.h3 : ¬∀ {α : Type} [inst : LE α] [inst : LT α] {a : α}, (a < a) = False := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_eq_false.h3.inst (@hc_h (Nat) (instLENat) ({ lt := fun (a b : Nat) => a ≤ b : LT Nat }) (0))

-- Int.Internal.Linear.eq_eq_false_of_divCoeff_k, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_false_of_divCoeff_k.h4.inst : ¬(Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
          Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        False := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_eq_false_of_divCoeff_k.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (k : Int),
        (Int.Internal.Linear.Expr.denote_k ctx lhs = Int.Internal.Linear.Expr.denote_k ctx rhs) = False := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_eq_false_of_divCoeff_k.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (0))

-- Lean.Grind.IsCharP.intCast_emod, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.IsCharP.intCast_emod.h3.inst : Not
      (@Eq Int
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@HMod.hMod Int Int Int (@instHMod Int Int.instMod) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.IsCharP.intCast_emod.h3 : Not
      (∀ (p : Nat) {α : Type} [inst : Lean.Grind.Ring α] (x : Int),
        @Eq α
          (@Int.cast α (@Lean.Grind.Ring.intCast α inst)
            (@HMod.hMod Int Int Int (@instHMod Int Int.instMod) x (@Nat.cast Int instNatCastInt p)))
          (@Int.cast α (@Lean.Grind.Ring.intCast α inst) x)) := fun hc_h => HypCheckProof.Lean.Grind.IsCharP.intCast_emod.h3.inst (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))

-- Lean.Grind.CommRing.diseq_int_module, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.diseq_int_module.h4.inst : Not
      (@Ne Int
        (@Lean.Grind.CommRing.Poly.denoteAsIntModule Int Lean.Grind.instCommRingInt
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
theorem HypCheckProof.Lean.Grind.CommRing.diseq_int_module.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (p : Lean.Grind.CommRing.Poly),
        @Ne α (@Lean.Grind.CommRing.Poly.denoteAsIntModule α inst ctx p)
          (@OfNat.ofNat α (nat_lit 0)
            (@Zero.toOfNat0 α
              (@Lean.Grind.AddCommMonoid.toZero α
                (@Lean.Grind.NatModule.toAddCommMonoid α
                  (@Lean.Grind.Semiring.toNatModule α
                    (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.diseq_int_module.h4.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))

-- Lean.Grind.Ring.neg_ofNat_sub, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Ring.neg_ofNat_sub.h4.inst : Not
      (@Eq Int
        (@Neg.neg Int (@Lean.Grind.Ring.toNeg Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Lean.Grind.Semiring.ofNat Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (@HSub.hSub Int Int Int
          (@instHSub Int (@Lean.Grind.Ring.toSub Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@OfNat.ofNat Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Lean.Grind.Semiring.ofNat Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@OfNat.ofNat Int (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@Lean.Grind.Semiring.ofNat Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Ring.neg_ofNat_sub.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Ring α] {x y : Nat},
        @Eq α
          (@Neg.neg α (@Lean.Grind.Ring.toNeg α inst)
            (@OfNat.ofNat α (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) x y)
              (@Lean.Grind.Semiring.ofNat α (@Lean.Grind.Ring.toSemiring α inst)
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) x y))))
          (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α inst))
            (@OfNat.ofNat α y (@Lean.Grind.Semiring.ofNat α (@Lean.Grind.Ring.toSemiring α inst) y))
            (@OfNat.ofNat α x (@Lean.Grind.Semiring.ofNat α (@Lean.Grind.Ring.toSemiring α inst) x)))) := fun hc_h => HypCheckProof.Lean.Grind.Ring.neg_ofNat_sub.h4.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))

-- Lean.Grind.CommRing.diseq_to_eq, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.diseq_to_eq.h4.inst : Not
      (@Eq Rat
        (@HMul.hMul Rat Rat Rat
          (@instHMul Rat
            (@Lean.Grind.Semiring.toMul Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@HSub.hSub Rat Rat Rat
            (@instHSub Rat
              (@Lean.Grind.Ring.toSub Rat
                (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
            (@HSub.hSub Rat Rat Rat
              (@instHSub Rat
                (@Lean.Grind.Ring.toSub Rat
                  (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
              (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
              (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))))
        (@OfNat.ofNat Rat (nat_lit 1)
          (@Lean.Grind.Semiring.ofNat Rat
            (@Lean.Grind.CommSemiring.toSemiring Rat
              (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))
            (nat_lit 1)))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.CommRing.diseq_to_eq.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (a b : α),
        @Eq α
          (@HMul.hMul α α α
            (@instHMul α
              (@Lean.Grind.Semiring.toMul α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
            (@HSub.hSub α α α
              (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))))
              a b)
            (@Inv.inv α (@Lean.Grind.Field.toInv α inst)
              (@HSub.hSub α α α
                (@instHSub α
                  (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))))
                a b)))
          (@OfNat.ofNat α (nat_lit 1)
            (@Lean.Grind.Semiring.ofNat α
              (@Lean.Grind.CommSemiring.toSemiring α
                (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
              (nat_lit 1)))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.diseq_to_eq.h4.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.Field.eq_inv_of_mul_eq_one, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.eq_inv_of_mul_eq_one.h4.inst : Not
      (@Eq Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.eq_inv_of_mul_eq_one.h4 : Not (∀ {α : Type} [inst : Lean.Grind.Field α] {a b : α}, @Eq α a (@Inv.inv α (@Lean.Grind.Field.toInv α inst) b)) := fun hc_h => HypCheckProof.Lean.Grind.Field.eq_inv_of_mul_eq_one.h4.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))

-- Lean.Grind.Field.of_pow_eq_zero, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.of_pow_eq_zero.h4.inst : Not
      (@Eq Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
        (@OfNat.ofNat Rat (nat_lit 0)
          (@Zero.toOfNat0 Rat
            (@Lean.Grind.AddCommMonoid.toZero Rat
              (@Lean.Grind.NatModule.toAddCommMonoid Rat
                (@Lean.Grind.Semiring.toNatModule Rat
                  (@Lean.Grind.CommSemiring.toSemiring Rat
                    (@Lean.Grind.CommRing.toCommSemiring Rat
                      (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Field.of_pow_eq_zero.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (a : α) (n : Nat),
        @Eq α a
          (@OfNat.ofNat α (nat_lit 0)
            (@Zero.toOfNat0 α
              (@Lean.Grind.AddCommMonoid.toZero α
                (@Lean.Grind.NatModule.toAddCommMonoid α
                  (@Lean.Grind.Semiring.toNatModule α
                    (@Lean.Grind.CommSemiring.toSemiring α
                      (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))))))) := fun hc_h => HypCheckProof.Lean.Grind.Field.of_pow_eq_zero.h4.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))

-- Int.Internal.Linear.eq_eq_false_of_divCoeff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_eq_false_of_divCoeff.h4.inst : ¬(Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) =
          Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        False := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_eq_false_of_divCoeff.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (k : Int),
        (Int.Internal.Linear.Expr.denote ctx lhs = Int.Internal.Linear.Expr.denote ctx rhs) = False := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_eq_false_of_divCoeff.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (0))

-- Int.Internal.Linear.norm_le, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.norm_le.h4.inst : ¬(Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) ≤
          Int.Internal.Linear.Expr.denote (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0)) =
        (Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
          0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.norm_le.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        (Int.Internal.Linear.Expr.denote ctx lhs ≤ Int.Internal.Linear.Expr.denote ctx rhs) =
          (Int.Internal.Linear.Poly.denote' ctx p ≤ 0) := fun hc_h => HypCheckProof.Int.Internal.Linear.norm_le.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)))

-- Lean.Grind.Field.zpow_sub_one, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.zpow_sub_one.h3.inst : Not
      (@Eq Rat
        (@HPow.hPow Rat Int Rat (@Lean.Grind.Field.zpow Rat Lean.Grind.instFieldRat)
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@HMul.hMul Rat Rat Rat
          (@instHMul Rat
            (@Lean.Grind.Semiring.toMul Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@HPow.hPow Rat Int Rat (@Lean.Grind.Field.zpow Rat Lean.Grind.instFieldRat)
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.zpow_sub_one.h3 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] {a : α} (n : Int),
        @Eq α
          (@HPow.hPow α Int α (@Lean.Grind.Field.zpow α inst) a
            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) n (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@HMul.hMul α α α
            (@instHMul α
              (@Lean.Grind.Semiring.toMul α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
            (@HPow.hPow α Int α (@Lean.Grind.Field.zpow α inst) a n) (@Inv.inv α (@Lean.Grind.Field.toInv α inst) a))) := fun hc_h => HypCheckProof.Lean.Grind.Field.zpow_sub_one.h3.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))

-- Lean.Grind.CommRing.diseq0_to_eq, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.diseq0_to_eq.h3.inst : Not
      (@Eq Rat
        (@HMul.hMul Rat Rat Rat
          (@instHMul Rat
            (@Lean.Grind.Semiring.toMul Rat
              (@Lean.Grind.CommSemiring.toSemiring Rat
                (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
        (@OfNat.ofNat Rat (nat_lit 1)
          (@Lean.Grind.Semiring.ofNat Rat
            (@Lean.Grind.CommSemiring.toSemiring Rat
              (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))
            (nat_lit 1)))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.CommRing.diseq0_to_eq.h3 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (a : α),
        @Eq α
          (@HMul.hMul α α α
            (@instHMul α
              (@Lean.Grind.Semiring.toMul α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
            a (@Inv.inv α (@Lean.Grind.Field.toInv α inst) a))
          (@OfNat.ofNat α (nat_lit 1)
            (@Lean.Grind.Semiring.ofNat α
              (@Lean.Grind.CommSemiring.toSemiring α
                (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
              (nat_lit 1)))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.diseq0_to_eq.h3.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.CommRing.PPoly.denote_kron, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denote_kron.h2.inst : ¬Lean.Grind.CommRing.PPoly.denote (fun (i : Nat) => 0 ^ 0 ^ i) 0
          (Lean.Grind.CommRing.PPoly.add 2 1 1 (Lean.Grind.CommRing.PPoly.num 0)) =
        Lean.Grind.CommRing.PPoly.kron 0 (Lean.Grind.CommRing.PPoly.add 2 1 1 (Lean.Grind.CommRing.PPoly.num 0)) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denote_kron.h2 : ¬∀ (X : Int) {B : Nat} (p : Lean.Grind.CommRing.PPoly),
        Lean.Grind.CommRing.PPoly.denote (fun (i : Nat) => X ^ B ^ i) B p = Lean.Grind.CommRing.PPoly.kron X p := fun hc_h => HypCheckProof.Lean.Grind.CommRing.PPoly.denote_kron.h2.inst (@hc_h (0) (0) (Lean.Grind.CommRing.PPoly.add 2 1 1 (Lean.Grind.CommRing.PPoly.num 0)))

-- Lean.Grind.CommRing.Expr.of_degS_k, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.of_degS_k.h2.inst : ¬((Lean.Grind.CommRing.Expr.var 0).neg.semi_k = Bool.true ∧
        (Lean.Grind.CommRing.Expr.var 0).neg.degB_k ≤
          Lean.Grind.CommRing.Expr.degS_k 0 (Lean.Grind.CommRing.Expr.var 0).neg) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.of_degS_k.h2 : ¬∀ (B : Nat) (e : Lean.Grind.CommRing.Expr), e.semi_k = Bool.true ∧ e.degB_k ≤ Lean.Grind.CommRing.Expr.degS_k B e := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.of_degS_k.h2.inst (@hc_h (0) ((Lean.Grind.CommRing.Expr.var 0).neg))

-- Lean.Grind.CommRing.Expr.of_linSOk_k, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.of_linSOk_k.h2.inst : ¬(Bool.rec Bool.false ((Lean.Grind.CommRing.Expr.var 0).mul (Lean.Grind.CommRing.Expr.var 0)).semi_k
            (Lean.Grind.CommRing.Expr.num 0).semi_k =
          Bool.true ∧
        (Lean.Grind.CommRing.Expr.num 0).linOk_k ((Lean.Grind.CommRing.Expr.var 0).mul (Lean.Grind.CommRing.Expr.var 0)) =
          Bool.true) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.of_linSOk_k.h2 : ¬∀ {a b : Lean.Grind.CommRing.Expr}, Bool.rec Bool.false b.semi_k a.semi_k = Bool.true ∧ a.linOk_k b = Bool.true := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.of_linSOk_k.h2.inst (@hc_h (Lean.Grind.CommRing.Expr.num 0) ((Lean.Grind.CommRing.Expr.var 0).mul (Lean.Grind.CommRing.Expr.var 0)))

-- Lean.Grind.CommRing.PPoly.NonNeg.coeff, hypothesis 1: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.NonNeg.coeff.h1.inst : ¬0 ≤ Lean.Grind.CommRing.PPoly.coeff 0 (Lean.Grind.CommRing.PPoly.num (-1)) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.NonNeg.coeff.h1 : ¬∀ {p : Lean.Grind.CommRing.PPoly} (c : Nat), 0 ≤ Lean.Grind.CommRing.PPoly.coeff c p := fun hc_h => HypCheckProof.Lean.Grind.CommRing.PPoly.NonNeg.coeff.h1.inst (@hc_h (Lean.Grind.CommRing.PPoly.num (-1)) (0))

