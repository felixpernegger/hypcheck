import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.CommRing.le_norm_polyC, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_polyC.h6 : ¬∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] [inst : Lean.Grind.IsCharP α c] [inst : LE α] [inst_1 : LT α]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        p = Lean.Grind.CommRing.Expr.toPolyXC_k bal (rhs.sub lhs) c →
          lhs' = lp.toExpr_k →
            rhs' = rp.toExpr_k →
              p = rp.combineC_k c (Lean.Grind.CommRing.Poly.mulConstC_k (Int.negSucc 0) lp c) → Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (0) (Lean.Grind.instCommRingInt) _ (⟨fun _ _ => False⟩ : LE Int) (Int.instLTInt) (.leaf 1 : Lean.RArray Int) (Bool.false) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) _ _ _ (.num 0 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) rfl rfl rfl (by
  rfl)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.CommRing.lt_norm_poly, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly.h5 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (p lp rp : Lean.Grind.CommRing.Poly),
        p = Lean.Grind.CommRing.Expr.toPolyX_k bal (rhs.sub lhs) →
          lhs' = lp.toExpr_k →
            rhs' = rp.toExpr_k →
              p = rp.combine_k (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc 0) lp) → Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (.leaf 1 : Lean.RArray Int) (Bool.false) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) _ _ _ (.num 0 : Lean.Grind.CommRing.Poly) (.num 0 : Lean.Grind.CommRing.Poly) rfl rfl rfl (by
  rfl)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.CommRing.lt_of_kron_rel, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kron_rel.h4 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α]
        (ctx : Lean.Grind.CommRing.Context α) (K B : Nat) (l r l' r' : Lean.Grind.CommRing.Expr),
        Lean.Grind.CommRing.Expr.degOk_k B (l.sub r) (l'.sub r') = Bool.true →
          Lean.Grind.CommRing.Expr.kronOk_k K (l.sub r) (l'.sub r') = Bool.true →
            Lean.Grind.CommRing.Expr.kronEval_k K B (l.sub r) = Lean.Grind.CommRing.Expr.kronEval_k K B (l'.sub r') →
              Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (.leaf 1 : Lean.RArray Int) (0) (2) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (by
  decide) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.Order.le_lt_trans_k, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h3 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.IsPreorder α inst] [inst_3 : Lean.Grind.Ring α]
        [inst_4 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_3) inst inst_1 inst_2] {a b c : α}
        {k₁ k₂ : Int} (k : Int),
        @LE.le α inst a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₁)) →
          @LT.lt α inst_1 b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₂)) →
            @Eq Bool
                (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k
                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁))
                Bool.true →
              @LT.lt α inst_1 a
                (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) c
                  (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k))) := fun hc_h => absurd (@hc_h (Int : Type) (⟨fun _ _ => True⟩ : LE Int) (Int.instLTInt) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (x x_1 : Int) => True) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.Grind.OrderedRing.mk (Int) (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (x x_1 : Int) => True) (Int.instLTInt) (@Std.IsPreorder.mk Int (@LE.mk Int fun (x x_1 : Int) => True) (fun (a : Int) => True.intro)
      fun (a b c : Int) (a_1 a_2 : True) => a_2) (@Lean.Grind.OrderedAdd.mk (Int) (@instHAdd Int
      (@Lean.Grind.Semiring.toAdd Int
        (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))) (@LE.mk Int fun (x x_1 : Int) => True) (@Std.IsPreorder.mk Int (@LE.mk Int fun (x x_1 : Int) => True) (fun (a : Int) => True.intro)
      fun (a b c : Int) (a_1 a_2 : True) => a_2) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   decide) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) _ (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide) (beq_self_eq_true _)) (by
  decide +kernel)

-- Lean.Grind.Order.le_lt_trans_k, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h4.inst : Not (@Std.IsPreorder Int (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b)) := by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h4.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h4.prem1 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h4 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst] [inst_3 : Lean.Grind.Ring α]
        {a b c : α} {k₁ k₂ : Int} (k : Int),
        @LE.le α inst a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₁)) →
          @LT.lt α inst_1 b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₂)) →
            @Eq Bool
                (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k
                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁))
                Bool.true →
              @Std.IsPreorder α inst) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h4.inst (@hc_h (Int) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h4.prem0 HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h4.prem1 (beq_self_eq_true _))

-- Lean.Grind.CommRing.lt_of_kronLin_rel, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_of_kronLin_rel.h4 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (l r l' r' : Lean.Grind.CommRing.Expr),
        (l.sub r).linOk_k (l'.sub r') = Bool.true →
          Lean.Grind.CommRing.Expr.kronOk_k K (l.sub r) (l'.sub r') = Bool.true →
            Lean.Grind.CommRing.Expr.kronLinEval_k K (l.sub r) = Lean.Grind.CommRing.Expr.kronLinEval_k K (l'.sub r') →
              Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (.leaf 1 : Lean.RArray Int) (0) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (by
  decide) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.CommRing.lt_false_of_toPPX_eq, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h4.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        False) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h4.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h4.prem1 : @Eq Lean.Grind.CommRing.PPoly
      (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Bool.false
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Bool.false
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.PPoly),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a) →
            @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b) →
              @Eq Prop
                (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
                False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h4.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (@LT.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt a b) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h4.prem0 rfl HypCheckProof.Lean.Grind.CommRing.lt_false_of_toPPX_eq.h4.prem1)

-- Lean.Grind.CommRing.le_true_of_toPPX_eqS, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h4.inst : ¬False = True := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h4.prem0 : Lean.Grind.CommRing.Expr.degSOk_k 2 (Lean.Grind.CommRing.Expr.num 0) (Lean.Grind.CommRing.Expr.num 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h4.prem1 : Lean.Grind.CommRing.Expr.toPPX_k 2 Bool.false (Lean.Grind.CommRing.Expr.num 0) =
      Lean.Grind.CommRing.Expr.toPPX_k 2 Bool.false (Lean.Grind.CommRing.Expr.num 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h4 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] [inst_1 : Lean.Grind.AddRightCancel α] [inst_2 : LE α]
        (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.PPoly),
        Lean.Grind.CommRing.Expr.degSOk_k B a b = Bool.true →
          p = Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a →
            p = Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b →
              (Lean.Grind.CommRing.Expr.denoteS ctx a ≤ Lean.Grind.CommRing.Expr.denoteS ctx b) = True := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h4.inst (@hc_h (Int) (Lean.Grind.instCommRingInt.toCommSemiring) (@Lean.Grind.AddRightCancel.mk (Int) (@Lean.Grind.Semiring.toAdd Int
      (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))) (by (try dsimp only);   (intros; omega))) ({ le := fun (x x_1 : Int) => False : LE Int }) (Lean.RArray.leaf 1) (2) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.num 0) (Lean.Grind.CommRing.Expr.num 0) (Lean.Grind.CommRing.Expr.toPPX_k 2 Bool.false (Lean.Grind.CommRing.Expr.num 0)) HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h4.prem0 rfl HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eqS.h4.prem1)

-- Lean.Grind.IntModule.OfNatModule.of_not_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.IntModule.OfNatModule.of_not_lt.h5 : ¬∀ {α : Type} [inst : Lean.Grind.NatModule α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α] {a b : α}
        {a' b' : Lean.Grind.IntModule.OfNatModule.Q α},
        Lean.Grind.IntModule.OfNatModule.toQ a = a' →
          Lean.Grind.IntModule.OfNatModule.toQ b = b' → ¬a < b → Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.Semiring.toNatModule) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (0) (0) _ _ rfl rfl (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.IntModule.OfNatModule.of_not_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.IntModule.OfNatModule.of_not_lt.h6 : ¬∀ {α : Type} [inst : Lean.Grind.NatModule α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
        [inst_4 : Std.IsPreorder α] {a b : α} {a' b' : Lean.Grind.IntModule.OfNatModule.Q α},
        Lean.Grind.IntModule.OfNatModule.toQ a = a' →
          Lean.Grind.IntModule.OfNatModule.toQ b = b' → ¬a < b → Lean.Grind.OrderedAdd α := fun hc_h => absurd (@hc_h (Nat) (Lean.Grind.Semiring.toNatModule) (⟨fun a b => a % 2 ≤ b % 2⟩ : LE Nat) (⟨fun a b => a % 2 < b % 2⟩ : LT Nat) (@Std.LawfulOrderLT.mk (Nat) (@LT.mk Nat fun (a b : Nat) =>
      @LT.lt Nat instLTNat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega))) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (0) (0) _ _ rfl rfl (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.add_le_left_iff (a := (0 : Nat)) (b := (1 : Nat)) (1 : Nat))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

