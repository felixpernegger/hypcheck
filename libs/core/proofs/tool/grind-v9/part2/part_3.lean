import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.Order.lt_eq_false_of_le_k, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h3 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.IsPreorder α inst] [inst_3 : Lean.Grind.Ring α]
        [inst_4 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_3) inst inst_1 inst_2] (a b : α)
        (k₁ k₂ : Int),
        @Eq Bool
            ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁).ble'
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
          @LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₁)) →
            @Eq Prop
              (@LT.lt α inst_1 b
                (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) a
                  (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₂)))
              False) := fun hc_h => absurd (@hc_h (Int : Type) (⟨fun _ _ => True⟩ : LE Int) (Int.instLTInt) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (x x_1 : Int) => True) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.Grind.OrderedRing.mk (Int) (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (x x_1 : Int) => True) (Int.instLTInt) (@Std.IsPreorder.mk Int (@LE.mk Int fun (x x_1 : Int) => True) (fun (a : Int) => True.intro)
      fun (a b c : Int) (a_1 a_2 : True) => a_2) (@Lean.Grind.OrderedAdd.mk (Int) (@instHAdd Int
      (@Lean.Grind.Semiring.toAdd Int
        (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))) (@LE.mk Int fun (x x_1 : Int) => True) (@Std.IsPreorder.mk Int (@LE.mk Int fun (x x_1 : Int) => True) (fun (a : Int) => True.intro)
      fun (a b c : Int) (a_1 a_2 : True) => a_2) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   decide) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Lean.Grind.Order.lt_eq_false_of_le_k, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h4.inst : Not (@Std.IsPreorder Int (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b)) := by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h4.prem0 : @Eq Bool
      ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).ble'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h4.prem1 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h4 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst] [inst_3 : Lean.Grind.Ring α]
        (a b : α) (k₁ k₂ : Int),
        @Eq Bool
            ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁).ble'
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
          @LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₁)) →
            @Std.IsPreorder α inst) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h4.inst (@hc_h (Int) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h4.prem0 HypCheckProof.Lean.Grind.Order.lt_eq_false_of_le_k.h4.prem1)

-- Lean.Grind.Order.le_eq_false_of_lt_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h3.inst : Not (@Eq Prop True False) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h3.prem0 : @Eq Bool
      ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).ble'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h3.prem1 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h3 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.IsPreorder α inst] [inst_3 : Lean.Grind.Ring α]
        [inst_4 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_3) inst inst_1 inst_2] (a b : α)
        (k₁ k₂ : Int),
        @Eq Bool
            ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁).ble'
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
          @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₁)) →
            @Eq Prop
              (@LE.le α inst b
                (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) a
                  (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₂)))
              False) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h3.inst (@hc_h (Int) (@LE.mk Int fun (x x_1 : Int) => True) (Int.instLTInt) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (x x_1 : Int) => True) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.Grind.OrderedRing.mk (Int) (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (x x_1 : Int) => True) (Int.instLTInt) (@Std.IsPreorder.mk Int (@LE.mk Int fun (x x_1 : Int) => True) (fun (a : Int) => True.intro)
      fun (a b c : Int) (a_1 a_2 : True) => a_2) (@Lean.Grind.OrderedAdd.mk (Int) (@instHAdd Int
      (@Lean.Grind.Semiring.toAdd Int
        (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))) (@LE.mk Int fun (x x_1 : Int) => True) (@Std.IsPreorder.mk Int (@LE.mk Int fun (x x_1 : Int) => True) (fun (a : Int) => True.intro)
      fun (a b c : Int) (a_1 a_2 : True) => a_2) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   decide) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h3.prem0 HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h3.prem1)

-- Lean.Grind.Order.le_eq_false_of_lt_k, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_lt_k.h4 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst] [inst_3 : Lean.Grind.Ring α]
        (a b : α) (k₁ k₂ : Int),
        @Eq Bool
            ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁).ble'
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
          @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₁)) →
            @Std.IsPreorder α inst) := fun hc_h => absurd (@hc_h (Int : Type) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.Order.lt_eq_false_of_lt_k, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_false_of_lt_k.h4 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst] [inst_3 : Lean.Grind.Ring α]
        (a b : α) (k₁ k₂ : Int),
        @Eq Bool
            ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁).ble'
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
          @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₁)) →
            @Std.IsPreorder α inst) := fun hc_h => absurd (@hc_h (Int : Type) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.Order.le_eq_true_of_le_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h3.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@HAdd.hAdd Int Int Int
            (@instHAdd Int
              (@Lean.Grind.Semiring.toAdd Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        True) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h3.prem0 : @Eq Bool
      (Int.ble' (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h3.prem1 : @LE.le Int Int.instLEInt
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h3 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.IsPreorder α inst] [inst_3 : Lean.Grind.Ring α]
        [inst_4 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_3) inst inst_1 inst_2] {a b : α}
        {k₁ k₂ : Int},
        @Eq Bool (k₁.ble' k₂) Bool.true →
          @LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₁)) →
            @Eq Prop
              (@LE.le α inst a
                (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) b
                  (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₂)))
              True) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h3.inst (@hc_h (Int) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (Int.instLTInt) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.Grind.OrderedRing.mk (Int) (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (Int.instLTInt) (@Std.IsPreorder.mk Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
      (fun (a : Int) =>
        @Decidable.byContradiction (@LE.le Int Int.instLEInt a a) (a.decLe a)
          fun (a_1 : Not (@LE.le Int Int.instLEInt a a)) =>
          (fun (a : Int) (a_2 : Not (@LE.le Int Int.instLEInt a a)) =>
              @Lean.Omega.Constraint.not_sat'_of_isImpossible
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                  Lean.Omega.Constraint }
                (@of_decide_eq_true
                  (@Eq Bool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (instDecidableEqBool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (@id
                    (@Eq Bool
                      (@Decidable.decide
                        (@Eq Bool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true)
                        (instDecidableEqBool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true))
                      Bool.true)
                    (@Eq.refl Bool Bool.true)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                  (@Lean.Omega.Constraint.addInequality_sat
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                    (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                      Int.instLEInt
                      (@Int.sub_nonneg_of_le a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Int.add_one_le_of_lt a a (@Lean.Omega.Int.lt_of_not_le a a a_2)))
                      (@Eq.trans Int
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                        (@Lean.Omega.Int.sub_congr a
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@Eq.symm Int
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                          (@Eq.trans Int
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                            ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            (@Lean.Omega.Int.add_congr a
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                              (@id
                                (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                            (@Eq.symm Int
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                              (Lean.Omega.LinearCombo.add_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) : Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))))
                        (@Eq.symm Int
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ({
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                          (Lean.Omega.LinearCombo.sub_eval
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))))))))
            a a_1)
      fun (a b c : Int) (a_1 : @LE.le Int Int.instLEInt b a) (a_2 : @LE.le Int Int.instLEInt c b) =>
      @Decidable.byContradiction (@LE.le Int Int.instLEInt c a) (c.decLe a)
        fun (a_3 : Not (@LE.le Int Int.instLEInt c a)) =>
        (fun (a b c : Int) (a_4 : @LE.le Int Int.instLEInt b a) (a_5 : @LE.le Int Int.instLEInt c b)
              (a_6 : Not (@LE.le Int Int.instLEInt c a)) =>
            @Lean.Omega.Constraint.not_sat'_of_isImpossible
              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                upperBound :=
                  @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                Lean.Omega.Constraint }
              (@of_decide_eq_true
                (@Eq Bool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (instDecidableEqBool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (@id
                  (@Eq Bool
                    (@Decidable.decide
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true))
                    Bool.true)
                  (@Eq.refl Bool Bool.true)))
              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.nil Int))))
              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
              (@Lean.Omega.Constraint.combine_sat'
                { lowerBound := @Option.none Int,
                  upperBound :=
                    @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                  Lean.Omega.Constraint }
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                  upperBound := @Option.none Int : Lean.Omega.Constraint }
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.nil Int))))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (Lean.Omega.combo_sat'
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound := @Option.none Int : Lean.Omega.Constraint }
                    { lowerBound := @Option.none Int,
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int)))
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int))))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                    (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int)))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        Int.instLEInt (@Int.sub_nonneg_of_le a b a_4)
                        (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          (@Lean.Omega.Int.sub_congr a
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            b
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              a
                              (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int)))))
                          (@Eq.symm Int
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            (Lean.Omega.LinearCombo.sub_eval
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@Lean.Omega.Constraint.addInequality_sat
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                        (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          Int.instLEInt
                          (@Int.sub_nonneg_of_le c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@Int.add_one_le_of_lt a c (@Lean.Omega.Int.lt_of_not_le c a a_6)))
                          (@Eq.trans Int
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Lean.Omega.Int.sub_congr c
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int)))
                              (@Eq.trans Int
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@Lean.Omega.Int.add_congr a
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    a
                                    (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                      (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                                  (@id
                                    (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                    (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                (@Eq.symm Int
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                  (Lean.Omega.LinearCombo.add_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))
                            (@Eq.symm Int
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                              (Lean.Omega.LinearCombo.sub_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))))))
                (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                    ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                          (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }).eval
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                    Int.instLEInt (@Int.sub_nonneg_of_le b c a_5)
                    (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                              Lean.Omega.LinearCombo }
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int))) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                      (@Lean.Omega.Int.sub_congr b
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        c
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int))))
                      (@Eq.symm Int
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                        (Lean.Omega.LinearCombo.sub_eval
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))))
          a b c a_1 a_2 a_3) (@Lean.Grind.OrderedAdd.mk (Int) (@instHAdd Int
      (@Lean.Grind.Semiring.toAdd Int
        (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (@Std.IsPreorder.mk Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
      (fun (a : Int) =>
        @Decidable.byContradiction (@LE.le Int Int.instLEInt a a) (a.decLe a)
          fun (a_1 : Not (@LE.le Int Int.instLEInt a a)) =>
          (fun (a : Int) (a_2 : Not (@LE.le Int Int.instLEInt a a)) =>
              @Lean.Omega.Constraint.not_sat'_of_isImpossible
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                  Lean.Omega.Constraint }
                (@of_decide_eq_true
                  (@Eq Bool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (instDecidableEqBool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (@id
                    (@Eq Bool
                      (@Decidable.decide
                        (@Eq Bool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true)
                        (instDecidableEqBool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true))
                      Bool.true)
                    (@Eq.refl Bool Bool.true)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                  (@Lean.Omega.Constraint.addInequality_sat
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                    (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                      Int.instLEInt
                      (@Int.sub_nonneg_of_le a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Int.add_one_le_of_lt a a (@Lean.Omega.Int.lt_of_not_le a a a_2)))
                      (@Eq.trans Int
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                        (@Lean.Omega.Int.sub_congr a
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@Eq.symm Int
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                          (@Eq.trans Int
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                            ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            (@Lean.Omega.Int.add_congr a
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                              (@id
                                (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                            (@Eq.symm Int
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                              (Lean.Omega.LinearCombo.add_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) : Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))))
                        (@Eq.symm Int
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ({
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                          (Lean.Omega.LinearCombo.sub_eval
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))))))))
            a a_1)
      fun (a b c : Int) (a_1 : @LE.le Int Int.instLEInt b a) (a_2 : @LE.le Int Int.instLEInt c b) =>
      @Decidable.byContradiction (@LE.le Int Int.instLEInt c a) (c.decLe a)
        fun (a_3 : Not (@LE.le Int Int.instLEInt c a)) =>
        (fun (a b c : Int) (a_4 : @LE.le Int Int.instLEInt b a) (a_5 : @LE.le Int Int.instLEInt c b)
              (a_6 : Not (@LE.le Int Int.instLEInt c a)) =>
            @Lean.Omega.Constraint.not_sat'_of_isImpossible
              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                upperBound :=
                  @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                Lean.Omega.Constraint }
              (@of_decide_eq_true
                (@Eq Bool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (instDecidableEqBool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (@id
                  (@Eq Bool
                    (@Decidable.decide
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true))
                    Bool.true)
                  (@Eq.refl Bool Bool.true)))
              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.nil Int))))
              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
              (@Lean.Omega.Constraint.combine_sat'
                { lowerBound := @Option.none Int,
                  upperBound :=
                    @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                  Lean.Omega.Constraint }
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                  upperBound := @Option.none Int : Lean.Omega.Constraint }
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.nil Int))))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (Lean.Omega.combo_sat'
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound := @Option.none Int : Lean.Omega.Constraint }
                    { lowerBound := @Option.none Int,
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int)))
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int))))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                    (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int)))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        Int.instLEInt (@Int.sub_nonneg_of_le a b a_4)
                        (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          (@Lean.Omega.Int.sub_congr a
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            b
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              a
                              (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int)))))
                          (@Eq.symm Int
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            (Lean.Omega.LinearCombo.sub_eval
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@Lean.Omega.Constraint.addInequality_sat
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                        (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          Int.instLEInt
                          (@Int.sub_nonneg_of_le c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@Int.add_one_le_of_lt a c (@Lean.Omega.Int.lt_of_not_le c a a_6)))
                          (@Eq.trans Int
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Lean.Omega.Int.sub_congr c
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int)))
                              (@Eq.trans Int
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@Lean.Omega.Int.add_congr a
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    a
                                    (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                      (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                                  (@id
                                    (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                    (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                (@Eq.symm Int
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                  (Lean.Omega.LinearCombo.add_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))
                            (@Eq.symm Int
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                              (Lean.Omega.LinearCombo.sub_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))))))
                (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                    ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                          (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }).eval
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                    Int.instLEInt (@Int.sub_nonneg_of_le b c a_5)
                    (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                              Lean.Omega.LinearCombo }
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int))) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                      (@Lean.Omega.Int.sub_congr b
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        c
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int))))
                      (@Eq.symm Int
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                        (Lean.Omega.LinearCombo.sub_eval
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))))
          a b c a_1 a_2 a_3) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   decide) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h3.prem0 HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h3.prem1)

-- Lean.Grind.Order.le_eq_true_of_le_k, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h4.inst : Not (@Std.IsPreorder Int (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b)) := by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h4.prem0 : @Eq Bool
      (Int.ble' (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h4.prem1 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h4 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst] [inst_3 : Lean.Grind.Ring α]
        {a b : α} {k₁ k₂ : Int},
        @Eq Bool (k₁.ble' k₂) Bool.true →
          @LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₁)) →
            @Std.IsPreorder α inst) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h4.inst (@hc_h (Int) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h4.prem0 HypCheckProof.Lean.Grind.Order.le_eq_true_of_le_k.h4.prem1)

-- Lean.Grind.Order.le_eq_false_of_le_k, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_le_k.h3.inst : Not (@Eq Prop True False) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_le_k.h3.prem0 : @Eq Bool
      ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).blt'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_le_k.h3.prem1 : True := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_of_le_k.h3 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.IsPreorder α inst] [inst_3 : Lean.Grind.Ring α]
        [inst_4 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_3) inst inst_1 inst_2] {a b : α}
        {k₁ k₂ : Int},
        @Eq Bool
            ((@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁).blt'
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
          @LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₁)) →
            @Eq Prop
              (@LE.le α inst b
                (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) a
                  (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k₂)))
              False) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_false_of_le_k.h3.inst (@hc_h (Int) (@LE.mk Int fun (x x_1 : Int) => True) (Int.instLTInt) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (x x_1 : Int) => True) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.Grind.OrderedRing.mk (Int) (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (x x_1 : Int) => True) (Int.instLTInt) (@Std.IsPreorder.mk Int (@LE.mk Int fun (x x_1 : Int) => True) (fun (a : Int) => True.intro)
      fun (a b c : Int) (a_1 a_2 : True) => a_2) (@Lean.Grind.OrderedAdd.mk (Int) (@instHAdd Int
      (@Lean.Grind.Semiring.toAdd Int
        (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))) (@LE.mk Int fun (x x_1 : Int) => True) (@Std.IsPreorder.mk Int (@LE.mk Int fun (x x_1 : Int) => True) (fun (a : Int) => True.intro)
      fun (a b c : Int) (a_1 a_2 : True) => a_2) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   decide) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.Order.le_eq_false_of_le_k.h3.prem0 HypCheckProof.Lean.Grind.Order.le_eq_false_of_le_k.h3.prem1)

-- Lean.Grind.CommRing.lt_false_of_kronLin, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLin.h4.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLin.h4.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linOk_k
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLin.h4.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLin.h4.prem2 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLin.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linOk_k b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K a) (Lean.Grind.CommRing.Expr.kronLinEval_k K b) →
              @Eq Prop
                (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
                False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLin.h4.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (@LT.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt a b) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLin.h4.prem0 HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLin.h4.prem1 HypCheckProof.Lean.Grind.CommRing.lt_false_of_kronLin.h4.prem2)

-- Lean.Grind.Linarith.not_le_norm, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.not_le_norm.h5.inst : Not (@Std.IsLinearOrder Int (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b)) := by
  exact fun hc_c =>
    absurd (hc_c.toIsPartialOrder.toIsPreorder.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.not_le_norm.h5.prem0 : @Eq Bool
      (Lean.Grind.Linarith.norm_cert Lean.Grind.Linarith.Expr.zero Lean.Grind.Linarith.Expr.zero
        Lean.Grind.Linarith.Poly.nil)
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.not_le_norm.h5.prem1 : Not
      (@LT.lt Int Int.instLTInt
        (@Lean.Grind.Linarith.Expr.denote_k Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Expr.zero)
        (@Lean.Grind.Linarith.Expr.denote_k Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Expr.zero)) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.not_le_norm.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] (ctx : Lean.Grind.Linarith.Context α)
        (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.norm_cert rhs lhs p) Bool.true →
          Not
              (@LE.le α inst_1 (@Lean.Grind.Linarith.Expr.denote_k α inst ctx lhs)
                (@Lean.Grind.Linarith.Expr.denote_k α inst ctx rhs)) →
            @Std.IsLinearOrder α inst_1) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.not_le_norm.h5.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.not_le_norm.h5.prem0 HypCheckProof.Lean.Grind.Linarith.not_le_norm.h5.prem1)

-- Lean.Grind.CommRing.lt_true_of_poly, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_true_of_poly.h5 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs : Lean.Grind.CommRing.Expr) (n : Nat),
        Lean.Grind.CommRing.Expr.toPolyX_k bal (rhs.sub lhs) = Lean.Grind.CommRing.Poly.num (Int.ofNat (n + 1)) →
          Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (.leaf 1 : Lean.RArray Int) (Bool.false) (.num 0 : Lean.Grind.CommRing.Expr) (.num 1 : Lean.Grind.CommRing.Expr) (0) (by
  rfl)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h4.inst : Not (@Std.IsPartialOrder Int (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b)) := by
  exact fun hc_c =>
    absurd (hc_c.toIsPreorder.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h4.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h4.prem1 : @LT.lt Int Int.instLTInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h4 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        {a b c : R},
        @LE.le R inst_1 a b →
          @LE.le R inst_1
              (@OfNat.ofNat R (nat_lit 0)
                (@Zero.toOfNat0 R
                  (@Lean.Grind.AddCommMonoid.toZero R
                    (@Lean.Grind.NatModule.toAddCommMonoid R
                      (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
              c →
            @Std.IsPartialOrder R inst_1) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h4.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h4.prem0 HypCheckProof.Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left.h4.prem1)

-- Lean.Grind.Linarith.diseq_split, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split.h4.inst : Not (Or False False) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split.h4.prem0 : @Eq Bool
      (Lean.Grind.Linarith.diseq_split_cert
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split.h4.prem1 : @Ne Int
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
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split.h4 : Not
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
                      (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.diseq_split.h4.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (@LT.mk Int fun (x x_1 : Int) => False) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.diseq_split.h4.prem0 HypCheckProof.Lean.Grind.Linarith.diseq_split.h4.prem1)

-- Lean.Grind.Linarith.diseq_split, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_split.h5 : ¬∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ : Lean.Grind.Linarith.Poly),
        Lean.Grind.Linarith.diseq_split_cert p₁ p₂ = Bool.true →
          Lean.Grind.Linarith.Poly.denote' ctx p₁ ≠ 0 → Std.IsLinearOrder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.Ring.toIntModule) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (.leaf 1 : Lean.RArray Int) (.add 1 0 .nil : Lean.Grind.Linarith.Poly) (.add (-1) 0 .nil : Lean.Grind.Linarith.Poly) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPartialOrder.toIsPreorder.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedRing.mul_lt_mul_of_neg_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_left.h4 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R] {a b c : R},
        a < b → c < 0 → Std.IsPartialOrder R := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (0) (1) (-1) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPreorder.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.CommRing.le_true_of_kronLinS, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h4.inst : ¬False = True := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h4.prem0 : (Lean.Grind.CommRing.Expr.num 0).linSOk_k (Lean.Grind.CommRing.Expr.num 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h4.prem1 : Lean.Grind.CommRing.Expr.kronOk_k 0 (Lean.Grind.CommRing.Expr.num 0) (Lean.Grind.CommRing.Expr.num 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h4.prem2 : Lean.Grind.CommRing.Expr.kronLinEval_k 0 (Lean.Grind.CommRing.Expr.num 0) =
      Lean.Grind.CommRing.Expr.kronLinEval_k 0 (Lean.Grind.CommRing.Expr.num 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h4 : ¬∀ {α : Type} [inst : Lean.Grind.CommSemiring α] [inst_1 : Lean.Grind.AddRightCancel α] [inst_2 : LE α]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b : Lean.Grind.CommRing.Expr),
        a.linSOk_k b = Bool.true →
          Lean.Grind.CommRing.Expr.kronOk_k K a b = Bool.true →
            Lean.Grind.CommRing.Expr.kronLinEval_k K a = Lean.Grind.CommRing.Expr.kronLinEval_k K b →
              (Lean.Grind.CommRing.Expr.denoteS ctx a ≤ Lean.Grind.CommRing.Expr.denoteS ctx b) = True := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h4.inst (@hc_h (Int) (Lean.Grind.instCommRingInt.toCommSemiring) (@Lean.Grind.AddRightCancel.mk (Int) (@Lean.Grind.Semiring.toAdd Int
      (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))) (by (try dsimp only);   (intros; omega))) ({ le := fun (x x_1 : Int) => False : LE Int }) (Lean.RArray.leaf 1) (0) (Lean.Grind.CommRing.Expr.num 0) (Lean.Grind.CommRing.Expr.num 0) HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h4.prem0 HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h4.prem1 HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLinS.h4.prem2)

-- Lean.Grind.CommRing.le_false_of_sub, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_false_of_sub.h4.inst : Not (@Eq Prop True False) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_false_of_sub.h4.prem0 : @Eq Int
      (@HSub.hSub Int Int Int
        (@instHSub Int (@Lean.Grind.Ring.toSub Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (Int.ofNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_false_of_sub.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (n : Nat),
        @Eq α
            (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst))
              (Int.ofNat
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          @Eq Prop
            (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_false_of_sub.h4.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@LE.mk Int fun (x x_1 : Int) => True) (Int.instLTInt) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (x x_1 : Int) => True) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.OrderedRing.mk (Int) (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (x x_1 : Int) => True) (Int.instLTInt) (@Std.IsPreorder.mk Int (@LE.mk Int fun (x x_1 : Int) => True) (fun (a : Int) => True.intro)
      fun (a b c : Int) (a_1 a_2 : True) => a_2) (@Lean.Grind.OrderedAdd.mk (Int) (@instHAdd Int
      (@Lean.Grind.Semiring.toAdd Int
        (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))) (@LE.mk Int fun (x x_1 : Int) => True) (@Std.IsPreorder.mk Int (@LE.mk Int fun (x x_1 : Int) => True) (fun (a : Int) => True.intro)
      fun (a b c : Int) (a_1 a_2 : True) => a_2) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   decide) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Lean.Grind.CommRing.le_false_of_sub.h4.prem0)

-- Lean.Grind.CommRing.le_false_of_sub, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.le_false_of_sub.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] (ctx : Lean.Grind.CommRing.Context α)
        (lhs rhs : Lean.Grind.CommRing.Expr) (n : Nat),
        @Eq α
            (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst))
              (Int.ofNat
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          @Std.IsPreorder α inst_1) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (.leaf 1 : Lean.RArray Int) (.var 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.CommRing.le_true_of_kron, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h3.inst : ¬False = True := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h3.prem0 : Lean.Grind.CommRing.Expr.degOk_k 2 (Lean.Grind.CommRing.Expr.num 0) (Lean.Grind.CommRing.Expr.num 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h3.prem1 : Lean.Grind.CommRing.Expr.kronOk_k 0 (Lean.Grind.CommRing.Expr.num 0) (Lean.Grind.CommRing.Expr.num 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h3.prem2 : Lean.Grind.CommRing.Expr.kronEval_k 0 2 (Lean.Grind.CommRing.Expr.num 0) =
      Lean.Grind.CommRing.Expr.kronEval_k 0 2 (Lean.Grind.CommRing.Expr.num 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h3 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        Lean.Grind.CommRing.Expr.degOk_k B a b = Bool.true →
          Lean.Grind.CommRing.Expr.kronOk_k K a b = Bool.true →
            Lean.Grind.CommRing.Expr.kronEval_k K B a = Lean.Grind.CommRing.Expr.kronEval_k K B b →
              (Lean.Grind.CommRing.Expr.denote ctx a ≤ Lean.Grind.CommRing.Expr.denote ctx b) = True := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h3.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) ({ le := fun (x x_1 : Int) => False : LE Int }) (Lean.RArray.leaf 1) (0) (2) (Lean.Grind.CommRing.Expr.num 0) (Lean.Grind.CommRing.Expr.num 0) HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h3.prem0 HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h3.prem1 HypCheckProof.Lean.Grind.CommRing.le_true_of_kron.h3.prem2)

-- Lean.Grind.CommRing.lt_true_of_sub, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_true_of_sub.h5 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] (ctx : Lean.Grind.CommRing.Context α)
        (lhs rhs : Lean.Grind.CommRing.Expr) (n : Nat),
        @Eq α
            (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs))
            (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst))
              (Int.ofNat
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          @Std.IsPreorder α inst_1) := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (.leaf 1 : Lean.RArray Int) (.num 0 : Lean.Grind.CommRing.Expr) (.var 0 : Lean.Grind.CommRing.Expr) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.Linarith.zero_lt_one, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Linarith.zero_lt_one.h5 : ¬∀ {α : Type} [inst : Lean.Grind.Ring α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : Std.LawfulOrderLT α]
        (ctx : Lean.Grind.Linarith.Context α) (p : Lean.Grind.Linarith.Poly),
        Lean.Grind.Linarith.zero_lt_one_cert p = Bool.true →
          Lean.Grind.Linarith.Var.denote ctx 0 = One.one → Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (.leaf 1 : Lean.RArray Int) (.add (-1) 0 .nil : Lean.Grind.Linarith.Poly) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h4.inst : Not (@Std.IsPartialOrder Int (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b)) := by
  exact fun hc_c =>
    absurd (hc_c.toIsPreorder.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h4.prem0 : @LT.lt Int Int.instLTInt (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h4.prem1 : @LT.lt Int Int.instLTInt (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h4 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        {a b : R},
        @LE.le R inst_1 a
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst)))))) →
          @LE.le R inst_1 b
              (@OfNat.ofNat R (nat_lit 0)
                (@Zero.toOfNat0 R
                  (@Lean.Grind.AddCommMonoid.toZero R
                    (@Lean.Grind.NatModule.toAddCommMonoid R
                      (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst)))))) →
            @Std.IsPartialOrder R inst_1) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h4.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h4.prem0 HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h4.prem1)

-- Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h5 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Std.LawfulOrderLT R] {a b : R}, a ≤ 0 → b ≤ 0 → 0 ≤ a * b := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (⟨fun a b => b ≤ a⟩ : LE Int) (⟨fun a b => b < a⟩ : LT Int) (@Std.IsPartialOrder.mk (Int) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (@Std.LawfulOrderLT.mk (Int) (@LT.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt b a) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (by (try dsimp only);   (intros; omega))) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos, hypothesis 6: necessary
/- FAILED: 1202:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, a ≤ 0 → b ≤ 0 → 0 ≤ a * b
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.253 hc_h a b a_1 a_2 a_3 ≠ ?m.254 hc_h a b a_1 a_2 a_3 | 1225:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, a ≤ 0 → b ≤ 0 → 0 ≤ a * b
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.229 hc_h a b a_1 a_2 a_3 ≠ ?m.230 hc_h a b a_1 a_2 a_3 | 1202:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, a ≤ 0 → b ≤ 0 → 0 ≤ a * b
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.253 hc_h a b a_1 a_2 a_3 ≠ ?m.254 hc_h a b a_1 a_2 a_3 | 1222:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, a ≤ 0 → b ≤ 0 → 0 ≤ a * b
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.233 hc_h a b a_1 a_2 a_3 ≠ ?m.234 hc_h a b a_1 a_2 a_3 | 1976:212: Application type mismatch: The argument
  h6.prem0
has type
  (0 : Nat) ≤ 1
but is expected to have type
  (1 : Int) ≤ 0
in the application
  hc_h h6.prem0 | 1259:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, a ≤ 0 → b ≤ 0 → 0 ≤ a * b
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.219 hc_h a b a_1 a_2 a_3 ≠ ?m.220 hc_h a b a_1 a_2 a_3 | 1976:212: Application type mismatch: The argument
  h6.prem0
has type
  (0 : Nat) ≤ 1
but is expected to have type
  (1 : Int) ≤ 0
in the application
  hc_h h6.prem0 | 1256:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, a ≤ 0 → b ≤ 0 → 0 ≤ a * b
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.223 hc_h a b a_1 a_2 a_3 ≠ ?m.224 hc_h a b a_1 a_2 a_3
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg_of_nonpos_of_nonpos.h6 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, a ≤ 0 → b ≤ 0 → 0 ≤ a * b := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (⟨fun a b => b ≤ a⟩ : LE Int) (Int.instLTInt) (@Std.IsPartialOrder.mk (Int) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.OrderedRing.mk (Int) (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (Int.instLTInt) (@Std.IsPartialOrder.toIsPreorder Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
      (@Std.IsPartialOrder.mk Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
        (@Std.IsPreorder.mk Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
          (fun (a : Int) =>
            @Decidable.byContradiction (@LE.le Int Int.instLEInt a a) (a.decLe a)
              fun (a_1 : Not (@LE.le Int Int.instLEInt a a)) =>
              (fun (a : Int) (a_2 : Not (@LE.le Int Int.instLEInt a a)) =>
                  @Lean.Omega.Constraint.not_sat'_of_isImpossible
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                      upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                      Lean.Omega.Constraint }
                    (@of_decide_eq_true
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                            upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                            upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (@id
                        (@Eq Bool
                          (@Decidable.decide
                            (@Eq Bool
                              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                                  Lean.Omega.Constraint }.isImpossible
                              Bool.true)
                            (instDecidableEqBool
                              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                                  Lean.Omega.Constraint }.isImpossible
                              Bool.true))
                          Bool.true)
                        (@Eq.refl Bool Bool.true)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                      (@Lean.Omega.Constraint.addInequality_sat
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                        (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          Int.instLEInt
                          (@Int.sub_nonneg_of_le a
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@Int.add_one_le_of_lt a a (@Lean.Omega.Int.lt_of_not_le a a a_2)))
                          (@Eq.trans Int
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            (@Lean.Omega.Int.sub_congr a
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                              (@Eq.trans Int
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                (@Lean.Omega.Int.add_congr a
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                    a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                                  (@id
                                    (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                    (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                (@Eq.symm Int
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                  (Lean.Omega.LinearCombo.add_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))))
                            (@Eq.symm Int
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                              (Lean.Omega.LinearCombo.sub_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))))))))
                a a_1)
          fun (a b c : Int) (a_1 : @LE.le Int Int.instLEInt b a) (a_2 : @LE.le Int Int.instLEInt c b) =>
          @Decidable.byContradiction (@LE.le Int Int.instLEInt c a) (c.decLe a)
            fun (a_3 : Not (@LE.le Int Int.instLEInt c a)) =>
            (fun (a b c : Int) (a_4 : @LE.le Int Int.instLEInt b a) (a_5 : @LE.le Int Int.instLEInt c b)
                  (a_6 : Not (@LE.le Int Int.instLEInt c a)) =>
                @Lean.Omega.Constraint.not_sat'_of_isImpossible
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                    upperBound :=
                      @Option.some Int
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                    Lean.Omega.Constraint }
                  (@of_decide_eq_true
                    (@Eq Bool
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                          upperBound :=
                            @Option.some Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                          Lean.Omega.Constraint }.isImpossible
                      Bool.true)
                    (instDecidableEqBool
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                          upperBound :=
                            @Option.some Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                          Lean.Omega.Constraint }.isImpossible
                      Bool.true)
                    (@id
                      (@Eq Bool
                        (@Decidable.decide
                          (@Eq Bool
                            { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                                upperBound :=
                                  @Option.some Int
                                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                                Lean.Omega.Constraint }.isImpossible
                            Bool.true)
                          (instDecidableEqBool
                            { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                                upperBound :=
                                  @Option.some Int
                                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                                Lean.Omega.Constraint }.isImpossible
                            Bool.true))
                        Bool.true)
                      (@Eq.refl Bool Bool.true)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (@Lean.Omega.Constraint.combine_sat'
                    { lowerBound := @Option.none Int,
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound := @Option.none Int : Lean.Omega.Constraint }
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int))))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (Lean.Omega.combo_sat'
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                          upperBound := @Option.none Int : Lean.Omega.Constraint }
                        { lowerBound := @Option.none Int,
                          upperBound :=
                            @Option.some Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                          Lean.Omega.Constraint }
                        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                          (@List.cons Int
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.nil Int)))
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@List.nil Int))))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                        (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                            (@List.cons Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@List.nil Int)))
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                          (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            Int.instLEInt (@Int.sub_nonneg_of_le a b a_4)
                            (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@Lean.Omega.Int.sub_congr a
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                b
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@Eq.symm Int
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  a
                                  (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                    (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                                (@Eq.symm Int
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int)))))
                              (@Eq.symm Int
                                ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                  ({
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  ({
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                (Lean.Omega.LinearCombo.sub_eval
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))
                        (@Lean.Omega.tidy_sat
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                            upperBound := @Option.none Int : Lean.Omega.Constraint }
                          (@List.cons Int
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                          (@Lean.Omega.Constraint.addInequality_sat
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.cons Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                            (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              Int.instLEInt
                              (@Int.sub_nonneg_of_le c
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@Int.add_one_le_of_lt a c (@Lean.Omega.Int.lt_of_not_le c a a_6)))
                              (@Eq.trans Int
                                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int))) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@Lean.Omega.Int.sub_congr c
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int)))
                                  (@Eq.trans Int
                                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                      ((Lean.Omega.LinearCombo.coordinate
                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                    ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                          (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                          {
                                            coeffs :=
                                              @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int) :
                                            Lean.Omega.LinearCombo }
                                          { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    (@Lean.Omega.Int.add_congr a
                                      ((Lean.Omega.LinearCombo.coordinate
                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                      (@Eq.symm Int
                                        ((Lean.Omega.LinearCombo.coordinate
                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                          (Lean.Omega.Coeffs.ofList
                                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                        a
                                        (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                          (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                                      (@id
                                        (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                                Lean.Omega.LinearCombo }.eval
                                            (Lean.Omega.Coeffs.ofList
                                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                        (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                    (@Eq.symm Int
                                      ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                            (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                            {
                                              coeffs :=
                                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int) :
                                              Lean.Omega.LinearCombo }
                                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                              Lean.Omega.LinearCombo }).eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                      (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        ({
                                              coeffs :=
                                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int) :
                                              Lean.Omega.LinearCombo }.eval
                                          (Lean.Omega.Coeffs.ofList
                                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                        ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                              Lean.Omega.LinearCombo }.eval
                                          (Lean.Omega.Coeffs.ofList
                                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                      (Lean.Omega.LinearCombo.add_eval
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))
                                (@Eq.symm Int
                                  ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int))) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int))) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                  (Lean.Omega.LinearCombo.sub_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))))))
                    (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                          (@List.cons Int
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        Int.instLEInt (@Int.sub_nonneg_of_le b c a_5)
                        (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int)) :
                                  Lean.Omega.LinearCombo }
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          (@Lean.Omega.Int.sub_congr b
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            c
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int))))
                          (@Eq.symm Int
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            (Lean.Omega.LinearCombo.sub_eval
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))))
              a b c a_1 a_2 a_3)
        fun (a b : ⋯) (a_1 : ⋯) (a_2 : ⋯) =>
        @Decidable.byContradiction (@Eq Int a b) (a.instDecidableEq b) fun (a_3 : ⋯) =>
          (fun (a b : ⋯) (a_4 : ⋯) (a_5 : ⋯) (a_6 : ⋯) =>
              @Or.elim (@LT.lt Int Int.instLTInt a b) (@LT.lt Int Int.instLTInt b a) False (@Int.lt_or_gt_of_ne a b a_6)
                (fun (h₁ : ⋯) =>
                  @Lean.Omega.Constraint.not_sat'_of_isImpossible
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                      upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                      Lean.Omega.Constraint }
                    (@of_decide_eq_true
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                            upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                            upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (@id
                        (@Eq Bool
                          (@Decidable.decide
                            (@Eq Bool
                              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                                  Lean.Omega.Constraint }.isImpossible
                              Bool.true)
                            (instDecidableEqBool
                              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                                  Lean.Omega.Constraint }.isImpossible
                              Bool.true))
                          Bool.true)
                        (@Eq.refl Bool Bool.true)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int)))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int)))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                      (Lean.Omega.combo_sat'
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                          upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                          Lean.Omega.Constraint }
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                          upperBound := @Option.none Int : Lean.Omega.Constraint }
                        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                          (@List.cons Int
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.nil Int)))
                        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                        (@Lean.Omega.Constraint.combine_sat'
                          { lowerBound := @Option.none Int,
                            upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                            Lean.Omega.Constraint }
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound := @Option.none Int : Lean.Omega.Constraint }
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                            (@List.cons Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@List.nil Int)))
                          (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                          (@Lean.Omega.tidy_sat
                            { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                              upperBound := @Option.none Int : Lean.Omega.Constraint }
                            (@List.cons Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)))
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                            (@Lean.Omega.Constraint.addInequality_sat
                              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                              (@List.cons Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)))
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                              (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b a)
                                ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int)) :
                                        Lean.Omega.LinearCombo }
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                Int.instLEInt (@Int.sub_nonneg_of_le b a a_5)
                                (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b a)
                                  (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                                  ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int)) :
                                          Lean.Omega.LinearCombo }
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  (@Lean.Omega.Int.sub_congr b
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    a
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    (@Eq.symm Int
                                      ((Lean.Omega.LinearCombo.coordinate
                                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                      b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.nil Int)))
                                    (@Eq.symm Int
                                      ((Lean.Omega.LinearCombo.coordinate
                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                      a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.cons Int b (@List.nil Int)))))
                                  (@Eq.symm Int
                                    ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                          (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                          {
                                            coeffs :=
                                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int)) :
                                            Lean.Omega.LinearCombo }
                                          {
                                            coeffs :=
                                              @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int) :
                                            Lean.Omega.LinearCombo }).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                      ({
                                            coeffs :=
                                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                      ({
                                            coeffs :=
                                              @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                                    (Lean.Omega.LinearCombo.sub_eval
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int)) :
                                        Lean.Omega.LinearCombo }
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))))))
                          (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                              (@List.cons Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@List.nil Int)))
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                            (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                              Int.instLEInt (@Int.sub_nonneg_of_le a b a_4)
                              (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                                ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                (@Lean.Omega.Int.sub_congr a
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  b
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.cons Int b (@List.nil Int))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.nil Int))))
                                (@Eq.symm Int
                                  ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                                  (Lean.Omega.LinearCombo.sub_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))))))
                        (@Lean.Omega.Constraint.addInequality_sat
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)))
                          (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                          (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                            Int.instLEInt
                            (@Int.sub_nonneg_of_le b
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@Int.add_one_le_of_lt a b h₁))
                            (@Eq.trans Int
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int)) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                              (@Lean.Omega.Int.sub_congr b
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                (@Eq.symm Int
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.nil Int)))
                                (@Eq.trans Int
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  (@Lean.Omega.Int.add_congr a
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      ⋯)
                                    ⋯ ⋯ ⋯ ⋯)
                                  ⋯))
                              ⋯))))))
                ⋯)
            ⋯ ⋯ ⋯ ⋯ ⋯)) (@Lean.Grind.OrderedAdd.mk (Int) (@instHAdd Int
      (@Lean.Grind.Semiring.toAdd Int
        (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (@Std.IsPreorder.mk Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
      (fun (a : Int) =>
        @Decidable.byContradiction (@LE.le Int Int.instLEInt a a) (a.decLe a)
          fun (a_1 : Not (@LE.le Int Int.instLEInt a a)) =>
          (fun (a : Int) (a_2 : Not (@LE.le Int Int.instLEInt a a)) =>
              @Lean.Omega.Constraint.not_sat'_of_isImpossible
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                  Lean.Omega.Constraint }
                (@of_decide_eq_true
                  (@Eq Bool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (instDecidableEqBool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (@id
                    (@Eq Bool
                      (@Decidable.decide
                        (@Eq Bool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true)
                        (instDecidableEqBool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true))
                      Bool.true)
                    (@Eq.refl Bool Bool.true)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                  (@Lean.Omega.Constraint.addInequality_sat
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                    (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                      Int.instLEInt
                      (@Int.sub_nonneg_of_le a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Int.add_one_le_of_lt a a (@Lean.Omega.Int.lt_of_not_le a a a_2)))
                      (@Eq.trans Int
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                        (@Lean.Omega.Int.sub_congr a
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@Eq.symm Int
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                          (@Eq.trans Int
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                            ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            (@Lean.Omega.Int.add_congr a
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                              (@id
                                (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                            (@Eq.symm Int
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                              (Lean.Omega.LinearCombo.add_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) : Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))))
                        (@Eq.symm Int
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ({
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                          (Lean.Omega.LinearCombo.sub_eval
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))))))))
            a a_1)
      fun (a b c : Int) (a_1 : @LE.le Int Int.instLEInt b a) (a_2 : @LE.le Int Int.instLEInt c b) =>
      @Decidable.byContradiction (@LE.le Int Int.instLEInt c a) (c.decLe a)
        fun (a_3 : Not (@LE.le Int Int.instLEInt c a)) =>
        (fun (a b c : Int) (a_4 : @LE.le Int Int.instLEInt b a) (a_5 : @LE.le Int Int.instLEInt c b)
              (a_6 : Not (@LE.le Int Int.instLEInt c a)) =>
            @Lean.Omega.Constraint.not_sat'_of_isImpossible
              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                upperBound :=
                  @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                Lean.Omega.Constraint }
              (@of_decide_eq_true
                (@Eq Bool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (instDecidableEqBool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (@id
                  (@Eq Bool
                    (@Decidable.decide
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true))
                    Bool.true)
                  (@Eq.refl Bool Bool.true)))
              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.nil Int))))
              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
              (@Lean.Omega.Constraint.combine_sat'
                { lowerBound := @Option.none Int,
                  upperBound :=
                    @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                  Lean.Omega.Constraint }
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                  upperBound := @Option.none Int : Lean.Omega.Constraint }
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.nil Int))))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (Lean.Omega.combo_sat'
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound := @Option.none Int : Lean.Omega.Constraint }
                    { lowerBound := @Option.none Int,
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int)))
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int))))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                    (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int)))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        Int.instLEInt (@Int.sub_nonneg_of_le a b a_4)
                        (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          (@Lean.Omega.Int.sub_congr a
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            b
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              a
                              (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int)))))
                          (@Eq.symm Int
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            (Lean.Omega.LinearCombo.sub_eval
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@Lean.Omega.Constraint.addInequality_sat
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                        (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          Int.instLEInt
                          (@Int.sub_nonneg_of_le c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@Int.add_one_le_of_lt a c (@Lean.Omega.Int.lt_of_not_le c a a_6)))
                          (@Eq.trans Int
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Lean.Omega.Int.sub_congr c
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int)))
                              (@Eq.trans Int
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@Lean.Omega.Int.add_congr a
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    a
                                    (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                      (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                                  (@id
                                    (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                    (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                (@Eq.symm Int
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                  (Lean.Omega.LinearCombo.add_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))
                            (@Eq.symm Int
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                              (Lean.Omega.LinearCombo.sub_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))))))
                (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                    ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                          (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }).eval
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                    Int.instLEInt (@Int.sub_nonneg_of_le b c a_5)
                    (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                              Lean.Omega.LinearCombo }
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int))) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                      (@Lean.Omega.Int.sub_congr b
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        c
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int))))
                      (@Eq.symm Int
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                        (Lean.Omega.LinearCombo.sub_eval
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))))
          a b c a_1 a_2 a_3) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   decide) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)
-/

-- Lean.Grind.OrderedRing.mul_nonneg, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h4.inst : Not (@Std.IsPartialOrder Int (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b)) := by
  exact fun hc_c =>
    absurd (hc_c.toIsPreorder.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h4.prem0 : @LT.lt Int Int.instLTInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h4.prem1 : @LT.lt Int Int.instLTInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h4 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        {a b : R},
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
              b →
            @Std.IsPartialOrder R inst_1) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h4.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h4.prem0 HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h4.prem1)

-- Lean.Grind.OrderedRing.mul_nonneg, hypothesis 6: necessary
/- FAILED: 1202:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.260 hc_h a b a_1 a_2 a_3 ≠ ?m.261 hc_h a b a_1 a_2 a_3 | 1227:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.229 hc_h a b a_1 a_2 a_3 ≠ ?m.230 hc_h a b a_1 a_2 a_3 | 1202:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.260 hc_h a b a_1 a_2 a_3 ≠ ?m.261 hc_h a b a_1 a_2 a_3 | 1224:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.233 hc_h a b a_1 a_2 a_3 ≠ ?m.234 hc_h a b a_1 a_2 a_3 | 1210:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.252 hc_h a b a_1 a_2 a_3 ≠ ?m.253 hc_h a b a_1 a_2 a_3 | 1260:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.219 hc_h a b a_1 a_2 a_3 ≠ ?m.220 hc_h a b a_1 a_2 a_3 | 1210:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.252 hc_h a b a_1 a_2 a_3 ≠ ?m.253 hc_h a b a_1 a_2 a_3 | 1257:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.223 hc_h a b a_1 a_2 a_3 ≠ ?m.224 hc_h a b a_1 a_2 a_3
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonneg.h6 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (⟨fun a b => b ≤ a⟩ : LE Int) (Int.instLTInt) (@Std.IsPartialOrder.mk (Int) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.OrderedRing.mk (Int) (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (Int.instLTInt) (@Std.IsPartialOrder.toIsPreorder Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
      (@Std.IsPartialOrder.mk Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
        (@Std.IsPreorder.mk Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
          (fun (a : Int) =>
            @Decidable.byContradiction (@LE.le Int Int.instLEInt a a) (a.decLe a)
              fun (a_1 : Not (@LE.le Int Int.instLEInt a a)) =>
              (fun (a : Int) (a_2 : Not (@LE.le Int Int.instLEInt a a)) =>
                  @Lean.Omega.Constraint.not_sat'_of_isImpossible
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                      upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                      Lean.Omega.Constraint }
                    (@of_decide_eq_true
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                            upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                            upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (@id
                        (@Eq Bool
                          (@Decidable.decide
                            (@Eq Bool
                              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                                  Lean.Omega.Constraint }.isImpossible
                              Bool.true)
                            (instDecidableEqBool
                              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                                  Lean.Omega.Constraint }.isImpossible
                              Bool.true))
                          Bool.true)
                        (@Eq.refl Bool Bool.true)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                      (@Lean.Omega.Constraint.addInequality_sat
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                        (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          Int.instLEInt
                          (@Int.sub_nonneg_of_le a
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@Int.add_one_le_of_lt a a (@Lean.Omega.Int.lt_of_not_le a a a_2)))
                          (@Eq.trans Int
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            (@Lean.Omega.Int.sub_congr a
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                              (@Eq.trans Int
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                (@Lean.Omega.Int.add_congr a
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                    a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                                  (@id
                                    (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                    (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                (@Eq.symm Int
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                  (Lean.Omega.LinearCombo.add_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))))
                            (@Eq.symm Int
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                              (Lean.Omega.LinearCombo.sub_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))))))))
                a a_1)
          fun (a b c : Int) (a_1 : @LE.le Int Int.instLEInt b a) (a_2 : @LE.le Int Int.instLEInt c b) =>
          @Decidable.byContradiction (@LE.le Int Int.instLEInt c a) (c.decLe a)
            fun (a_3 : Not (@LE.le Int Int.instLEInt c a)) =>
            (fun (a b c : Int) (a_4 : @LE.le Int Int.instLEInt b a) (a_5 : @LE.le Int Int.instLEInt c b)
                  (a_6 : Not (@LE.le Int Int.instLEInt c a)) =>
                @Lean.Omega.Constraint.not_sat'_of_isImpossible
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                    upperBound :=
                      @Option.some Int
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                    Lean.Omega.Constraint }
                  (@of_decide_eq_true
                    (@Eq Bool
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                          upperBound :=
                            @Option.some Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                          Lean.Omega.Constraint }.isImpossible
                      Bool.true)
                    (instDecidableEqBool
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                          upperBound :=
                            @Option.some Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                          Lean.Omega.Constraint }.isImpossible
                      Bool.true)
                    (@id
                      (@Eq Bool
                        (@Decidable.decide
                          (@Eq Bool
                            { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                                upperBound :=
                                  @Option.some Int
                                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                                Lean.Omega.Constraint }.isImpossible
                            Bool.true)
                          (instDecidableEqBool
                            { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                                upperBound :=
                                  @Option.some Int
                                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                                Lean.Omega.Constraint }.isImpossible
                            Bool.true))
                        Bool.true)
                      (@Eq.refl Bool Bool.true)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (@Lean.Omega.Constraint.combine_sat'
                    { lowerBound := @Option.none Int,
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound := @Option.none Int : Lean.Omega.Constraint }
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int))))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (Lean.Omega.combo_sat'
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                          upperBound := @Option.none Int : Lean.Omega.Constraint }
                        { lowerBound := @Option.none Int,
                          upperBound :=
                            @Option.some Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                          Lean.Omega.Constraint }
                        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                          (@List.cons Int
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.nil Int)))
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@List.nil Int))))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                        (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                            (@List.cons Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@List.nil Int)))
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                          (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            Int.instLEInt (@Int.sub_nonneg_of_le a b a_4)
                            (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@Lean.Omega.Int.sub_congr a
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                b
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@Eq.symm Int
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  a
                                  (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                    (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                                (@Eq.symm Int
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int)))))
                              (@Eq.symm Int
                                ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                  ({
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  ({
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                (Lean.Omega.LinearCombo.sub_eval
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))
                        (@Lean.Omega.tidy_sat
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                            upperBound := @Option.none Int : Lean.Omega.Constraint }
                          (@List.cons Int
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                          (@Lean.Omega.Constraint.addInequality_sat
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.cons Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                            (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              Int.instLEInt
                              (@Int.sub_nonneg_of_le c
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@Int.add_one_le_of_lt a c (@Lean.Omega.Int.lt_of_not_le c a a_6)))
                              (@Eq.trans Int
                                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int))) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@Lean.Omega.Int.sub_congr c
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int)))
                                  (@Eq.trans Int
                                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                      ((Lean.Omega.LinearCombo.coordinate
                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                    ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                          (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                          {
                                            coeffs :=
                                              @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int) :
                                            Lean.Omega.LinearCombo }
                                          { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    (@Lean.Omega.Int.add_congr a
                                      ((Lean.Omega.LinearCombo.coordinate
                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                      (@Eq.symm Int
                                        ((Lean.Omega.LinearCombo.coordinate
                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                          (Lean.Omega.Coeffs.ofList
                                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                        a
                                        (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                          (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                                      (@id
                                        (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                                Lean.Omega.LinearCombo }.eval
                                            (Lean.Omega.Coeffs.ofList
                                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                        (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                    (@Eq.symm Int
                                      ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                            (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                            {
                                              coeffs :=
                                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int) :
                                              Lean.Omega.LinearCombo }
                                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                              Lean.Omega.LinearCombo }).eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                      (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        ({
                                              coeffs :=
                                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int) :
                                              Lean.Omega.LinearCombo }.eval
                                          (Lean.Omega.Coeffs.ofList
                                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                        ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                              Lean.Omega.LinearCombo }.eval
                                          (Lean.Omega.Coeffs.ofList
                                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                      (Lean.Omega.LinearCombo.add_eval
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))
                                (@Eq.symm Int
                                  ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int))) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int))) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                  (Lean.Omega.LinearCombo.sub_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))))))
                    (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                          (@List.cons Int
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        Int.instLEInt (@Int.sub_nonneg_of_le b c a_5)
                        (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int)) :
                                  Lean.Omega.LinearCombo }
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          (@Lean.Omega.Int.sub_congr b
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            c
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int))))
                          (@Eq.symm Int
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            (Lean.Omega.LinearCombo.sub_eval
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))))
              a b c a_1 a_2 a_3)
        fun (a b : ⋯) (a_1 : ⋯) (a_2 : ⋯) =>
        @Decidable.byContradiction (@Eq Int a b) (a.instDecidableEq b) fun (a_3 : ⋯) =>
          (fun (a b : ⋯) (a_4 : ⋯) (a_5 : ⋯) (a_6 : ⋯) =>
              @Or.elim (@LT.lt Int Int.instLTInt a b) (@LT.lt Int Int.instLTInt b a) False (@Int.lt_or_gt_of_ne a b a_6)
                (fun (h₁ : ⋯) =>
                  @Lean.Omega.Constraint.not_sat'_of_isImpossible
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                      upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                      Lean.Omega.Constraint }
                    (@of_decide_eq_true
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                            upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                            upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (@id
                        (@Eq Bool
                          (@Decidable.decide
                            (@Eq Bool
                              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                                  Lean.Omega.Constraint }.isImpossible
                              Bool.true)
                            (instDecidableEqBool
                              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                                  Lean.Omega.Constraint }.isImpossible
                              Bool.true))
                          Bool.true)
                        (@Eq.refl Bool Bool.true)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int)))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int)))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                      (Lean.Omega.combo_sat'
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                          upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                          Lean.Omega.Constraint }
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                          upperBound := @Option.none Int : Lean.Omega.Constraint }
                        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                          (@List.cons Int
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.nil Int)))
                        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                        (@Lean.Omega.Constraint.combine_sat'
                          { lowerBound := @Option.none Int,
                            upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                            Lean.Omega.Constraint }
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound := @Option.none Int : Lean.Omega.Constraint }
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                            (@List.cons Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@List.nil Int)))
                          (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                          (@Lean.Omega.tidy_sat
                            { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                              upperBound := @Option.none Int : Lean.Omega.Constraint }
                            (@List.cons Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)))
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                            (@Lean.Omega.Constraint.addInequality_sat
                              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                              (@List.cons Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)))
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                              (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b a)
                                ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int)) :
                                        Lean.Omega.LinearCombo }
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                Int.instLEInt (@Int.sub_nonneg_of_le b a a_5)
                                (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b a)
                                  (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                                  ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int)) :
                                          Lean.Omega.LinearCombo }
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  (@Lean.Omega.Int.sub_congr b
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    a
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    (@Eq.symm Int
                                      ((Lean.Omega.LinearCombo.coordinate
                                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                      b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.nil Int)))
                                    (@Eq.symm Int
                                      ((Lean.Omega.LinearCombo.coordinate
                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                      a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.cons Int b (@List.nil Int)))))
                                  (@Eq.symm Int
                                    ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                          (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                          {
                                            coeffs :=
                                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int)) :
                                            Lean.Omega.LinearCombo }
                                          {
                                            coeffs :=
                                              @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int) :
                                            Lean.Omega.LinearCombo }).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                      ({
                                            coeffs :=
                                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                      ({
                                            coeffs :=
                                              @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                                    (Lean.Omega.LinearCombo.sub_eval
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int)) :
                                        Lean.Omega.LinearCombo }
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))))))
                          (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                              (@List.cons Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@List.nil Int)))
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                            (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                              Int.instLEInt (@Int.sub_nonneg_of_le a b a_4)
                              (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                                ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                (@Lean.Omega.Int.sub_congr a
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  b
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.cons Int b (@List.nil Int))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.nil Int))))
                                (@Eq.symm Int
                                  ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                                  (Lean.Omega.LinearCombo.sub_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))))))
                        (@Lean.Omega.Constraint.addInequality_sat
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)))
                          (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                          (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                            Int.instLEInt
                            (@Int.sub_nonneg_of_le b
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@Int.add_one_le_of_lt a b h₁))
                            (@Eq.trans Int
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int)) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                              (@Lean.Omega.Int.sub_congr b
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                (@Eq.symm Int
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.nil Int)))
                                (@Eq.trans Int
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  (@Lean.Omega.Int.add_congr a
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      ⋯)
                                    ⋯ ⋯ ⋯ ⋯)
                                  ⋯))
                              ⋯))))))
                ⋯)
            ⋯ ⋯ ⋯ ⋯ ⋯)) (@Lean.Grind.OrderedAdd.mk (Int) (@instHAdd Int
      (@Lean.Grind.Semiring.toAdd Int
        (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (@Std.IsPreorder.mk Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
      (fun (a : Int) =>
        @Decidable.byContradiction (@LE.le Int Int.instLEInt a a) (a.decLe a)
          fun (a_1 : Not (@LE.le Int Int.instLEInt a a)) =>
          (fun (a : Int) (a_2 : Not (@LE.le Int Int.instLEInt a a)) =>
              @Lean.Omega.Constraint.not_sat'_of_isImpossible
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                  Lean.Omega.Constraint }
                (@of_decide_eq_true
                  (@Eq Bool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (instDecidableEqBool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (@id
                    (@Eq Bool
                      (@Decidable.decide
                        (@Eq Bool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true)
                        (instDecidableEqBool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true))
                      Bool.true)
                    (@Eq.refl Bool Bool.true)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                  (@Lean.Omega.Constraint.addInequality_sat
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                    (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                      Int.instLEInt
                      (@Int.sub_nonneg_of_le a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Int.add_one_le_of_lt a a (@Lean.Omega.Int.lt_of_not_le a a a_2)))
                      (@Eq.trans Int
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                        (@Lean.Omega.Int.sub_congr a
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@Eq.symm Int
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                          (@Eq.trans Int
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                            ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            (@Lean.Omega.Int.add_congr a
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                              (@id
                                (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                            (@Eq.symm Int
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                              (Lean.Omega.LinearCombo.add_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) : Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))))
                        (@Eq.symm Int
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ({
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                          (Lean.Omega.LinearCombo.sub_eval
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))))))))
            a a_1)
      fun (a b c : Int) (a_1 : @LE.le Int Int.instLEInt b a) (a_2 : @LE.le Int Int.instLEInt c b) =>
      @Decidable.byContradiction (@LE.le Int Int.instLEInt c a) (c.decLe a)
        fun (a_3 : Not (@LE.le Int Int.instLEInt c a)) =>
        (fun (a b c : Int) (a_4 : @LE.le Int Int.instLEInt b a) (a_5 : @LE.le Int Int.instLEInt c b)
              (a_6 : Not (@LE.le Int Int.instLEInt c a)) =>
            @Lean.Omega.Constraint.not_sat'_of_isImpossible
              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                upperBound :=
                  @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                Lean.Omega.Constraint }
              (@of_decide_eq_true
                (@Eq Bool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (instDecidableEqBool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (@id
                  (@Eq Bool
                    (@Decidable.decide
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true))
                    Bool.true)
                  (@Eq.refl Bool Bool.true)))
              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.nil Int))))
              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
              (@Lean.Omega.Constraint.combine_sat'
                { lowerBound := @Option.none Int,
                  upperBound :=
                    @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                  Lean.Omega.Constraint }
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                  upperBound := @Option.none Int : Lean.Omega.Constraint }
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.nil Int))))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (Lean.Omega.combo_sat'
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound := @Option.none Int : Lean.Omega.Constraint }
                    { lowerBound := @Option.none Int,
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int)))
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int))))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                    (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int)))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        Int.instLEInt (@Int.sub_nonneg_of_le a b a_4)
                        (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          (@Lean.Omega.Int.sub_congr a
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            b
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              a
                              (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int)))))
                          (@Eq.symm Int
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            (Lean.Omega.LinearCombo.sub_eval
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@Lean.Omega.Constraint.addInequality_sat
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                        (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          Int.instLEInt
                          (@Int.sub_nonneg_of_le c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@Int.add_one_le_of_lt a c (@Lean.Omega.Int.lt_of_not_le c a a_6)))
                          (@Eq.trans Int
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Lean.Omega.Int.sub_congr c
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int)))
                              (@Eq.trans Int
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@Lean.Omega.Int.add_congr a
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    a
                                    (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                      (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                                  (@id
                                    (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                    (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                (@Eq.symm Int
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                  (Lean.Omega.LinearCombo.add_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))
                            (@Eq.symm Int
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                              (Lean.Omega.LinearCombo.sub_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))))))
                (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                    ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                          (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }).eval
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                    Int.instLEInt (@Int.sub_nonneg_of_le b c a_5)
                    (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                              Lean.Omega.LinearCombo }
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int))) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                      (@Lean.Omega.Int.sub_congr b
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        c
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int))))
                      (@Eq.symm Int
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                        (Lean.Omega.LinearCombo.sub_eval
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))))
          a b c a_1 a_2 a_3) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   decide) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (-1) (-1) (by
  decide) (by
  decide)) (by
  decide +kernel)
-/

-- Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h4.inst : Not (@Std.IsPartialOrder Int (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b)) := by
  exact fun hc_c =>
    absurd (hc_c.toIsPreorder.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h4.prem0 : @LT.lt Int Int.instLTInt (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h4.prem1 : @LT.lt Int Int.instLTInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h4 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        {a b : R},
        @LE.le R inst_1 a
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst)))))) →
          @LE.le R inst_1
              (@OfNat.ofNat R (nat_lit 0)
                (@Zero.toOfNat0 R
                  (@Lean.Grind.AddCommMonoid.toZero R
                    (@Lean.Grind.NatModule.toAddCommMonoid R
                      (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
              b →
            @Std.IsPartialOrder R inst_1) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h4.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h4.prem0 HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h4.prem1)

-- Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg, hypothesis 6: necessary
/- FAILED: 1202:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, a ≤ 0 → 0 ≤ b → a * b ≤ 0
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.257 hc_h a b a_1 a_2 a_3 ≠ ?m.258 hc_h a b a_1 a_2 a_3 | 1226:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, a ≤ 0 → 0 ≤ b → a * b ≤ 0
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.229 hc_h a b a_1 a_2 a_3 ≠ ?m.230 hc_h a b a_1 a_2 a_3 | 1202:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, a ≤ 0 → 0 ≤ b → a * b ≤ 0
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.257 hc_h a b a_1 a_2 a_3 ≠ ?m.258 hc_h a b a_1 a_2 a_3 | 1992:2: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (6000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 1976:213: Application type mismatch: The argument
  h6.prem0
has type
  (0 : Nat) ≤ 1
but is expected to have type
  (1 : Int) ≤ 0
in the application
  hc_h h6.prem0 | 1260:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, a ≤ 0 → 0 ≤ b → a * b ≤ 0
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.219 hc_h a b a_1 a_2 a_3 ≠ ?m.220 hc_h a b a_1 a_2 a_3 | 1976:213: Application type mismatch: The argument
  h6.prem0
has type
  (0 : Nat) ≤ 1
but is expected to have type
  (1 : Int) ≤ 0
in the application
  hc_h h6.prem0 | 1257:20: don't know how to synthesize placeholder for argument `a_6`
context:
hc_h :
  ∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
    [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, a ≤ 0 → 0 ≤ b → a * b ≤ 0
a b : Int
a_1 : a ≤ b
a_2 : b ≤ a
a_3 : ¬a = b
⊢ ?m.223 hc_h a b a_1 a_2 a_3 ≠ ?m.224 hc_h a b a_1 a_2 a_3
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_nonpos_of_nonpos_of_nonneg.h6 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Lean.Grind.OrderedRing R] {a b : R}, a ≤ 0 → 0 ≤ b → a * b ≤ 0 := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (⟨fun a b => b ≤ a⟩ : LE Int) (Int.instLTInt) (@Std.IsPartialOrder.mk (Int) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.OrderedRing.mk (Int) (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (Int.instLTInt) (@Std.IsPartialOrder.toIsPreorder Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
      (@Std.IsPartialOrder.mk Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
        (@Std.IsPreorder.mk Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
          (fun (a : Int) =>
            @Decidable.byContradiction (@LE.le Int Int.instLEInt a a) (a.decLe a)
              fun (a_1 : Not (@LE.le Int Int.instLEInt a a)) =>
              (fun (a : Int) (a_2 : Not (@LE.le Int Int.instLEInt a a)) =>
                  @Lean.Omega.Constraint.not_sat'_of_isImpossible
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                      upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                      Lean.Omega.Constraint }
                    (@of_decide_eq_true
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                            upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                            upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (@id
                        (@Eq Bool
                          (@Decidable.decide
                            (@Eq Bool
                              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                                  Lean.Omega.Constraint }.isImpossible
                              Bool.true)
                            (instDecidableEqBool
                              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                                  Lean.Omega.Constraint }.isImpossible
                              Bool.true))
                          Bool.true)
                        (@Eq.refl Bool Bool.true)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                      (@Lean.Omega.Constraint.addInequality_sat
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                        (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          Int.instLEInt
                          (@Int.sub_nonneg_of_le a
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@Int.add_one_le_of_lt a a (@Lean.Omega.Int.lt_of_not_le a a a_2)))
                          (@Eq.trans Int
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            (@Lean.Omega.Int.sub_congr a
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                              (@Eq.trans Int
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                (@Lean.Omega.Int.add_congr a
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                    a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                                  (@id
                                    (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                    (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                (@Eq.symm Int
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                  (Lean.Omega.LinearCombo.add_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))))
                            (@Eq.symm Int
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                              (Lean.Omega.LinearCombo.sub_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))))))))
                a a_1)
          fun (a b c : Int) (a_1 : @LE.le Int Int.instLEInt b a) (a_2 : @LE.le Int Int.instLEInt c b) =>
          @Decidable.byContradiction (@LE.le Int Int.instLEInt c a) (c.decLe a)
            fun (a_3 : Not (@LE.le Int Int.instLEInt c a)) =>
            (fun (a b c : Int) (a_4 : @LE.le Int Int.instLEInt b a) (a_5 : @LE.le Int Int.instLEInt c b)
                  (a_6 : Not (@LE.le Int Int.instLEInt c a)) =>
                @Lean.Omega.Constraint.not_sat'_of_isImpossible
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                    upperBound :=
                      @Option.some Int
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                    Lean.Omega.Constraint }
                  (@of_decide_eq_true
                    (@Eq Bool
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                          upperBound :=
                            @Option.some Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                          Lean.Omega.Constraint }.isImpossible
                      Bool.true)
                    (instDecidableEqBool
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                          upperBound :=
                            @Option.some Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                          Lean.Omega.Constraint }.isImpossible
                      Bool.true)
                    (@id
                      (@Eq Bool
                        (@Decidable.decide
                          (@Eq Bool
                            { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                                upperBound :=
                                  @Option.some Int
                                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                                Lean.Omega.Constraint }.isImpossible
                            Bool.true)
                          (instDecidableEqBool
                            { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                                upperBound :=
                                  @Option.some Int
                                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                                Lean.Omega.Constraint }.isImpossible
                            Bool.true))
                        Bool.true)
                      (@Eq.refl Bool Bool.true)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (@Lean.Omega.Constraint.combine_sat'
                    { lowerBound := @Option.none Int,
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound := @Option.none Int : Lean.Omega.Constraint }
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int))))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (Lean.Omega.combo_sat'
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                          upperBound := @Option.none Int : Lean.Omega.Constraint }
                        { lowerBound := @Option.none Int,
                          upperBound :=
                            @Option.some Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                          Lean.Omega.Constraint }
                        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                          (@List.cons Int
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.nil Int)))
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@List.nil Int))))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                        (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                            (@List.cons Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@List.nil Int)))
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                          (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            Int.instLEInt (@Int.sub_nonneg_of_le a b a_4)
                            (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@Lean.Omega.Int.sub_congr a
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                b
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@Eq.symm Int
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  a
                                  (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                    (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                                (@Eq.symm Int
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int)))))
                              (@Eq.symm Int
                                ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                  ({
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  ({
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                (Lean.Omega.LinearCombo.sub_eval
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))
                        (@Lean.Omega.tidy_sat
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                            upperBound := @Option.none Int : Lean.Omega.Constraint }
                          (@List.cons Int
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                          (@Lean.Omega.Constraint.addInequality_sat
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.cons Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                            (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              Int.instLEInt
                              (@Int.sub_nonneg_of_le c
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@Int.add_one_le_of_lt a c (@Lean.Omega.Int.lt_of_not_le c a a_6)))
                              (@Eq.trans Int
                                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int))) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@Lean.Omega.Int.sub_congr c
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int)))
                                  (@Eq.trans Int
                                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                    (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                      ((Lean.Omega.LinearCombo.coordinate
                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                    ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                          (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                          {
                                            coeffs :=
                                              @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int) :
                                            Lean.Omega.LinearCombo }
                                          { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    (@Lean.Omega.Int.add_congr a
                                      ((Lean.Omega.LinearCombo.coordinate
                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                      (@Eq.symm Int
                                        ((Lean.Omega.LinearCombo.coordinate
                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                          (Lean.Omega.Coeffs.ofList
                                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                        a
                                        (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                          (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                                      (@id
                                        (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                                Lean.Omega.LinearCombo }.eval
                                            (Lean.Omega.Coeffs.ofList
                                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                        (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                    (@Eq.symm Int
                                      ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                            (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                            {
                                              coeffs :=
                                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int) :
                                              Lean.Omega.LinearCombo }
                                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                              Lean.Omega.LinearCombo }).eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                      (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                        ({
                                              coeffs :=
                                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int) :
                                              Lean.Omega.LinearCombo }.eval
                                          (Lean.Omega.Coeffs.ofList
                                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                        ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                              Lean.Omega.LinearCombo }.eval
                                          (Lean.Omega.Coeffs.ofList
                                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                      (Lean.Omega.LinearCombo.add_eval
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))
                                (@Eq.symm Int
                                  ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int))) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int))) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                  (Lean.Omega.LinearCombo.sub_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))))))
                    (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                          (@List.cons Int
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        Int.instLEInt (@Int.sub_nonneg_of_le b c a_5)
                        (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int)) :
                                  Lean.Omega.LinearCombo }
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          (@Lean.Omega.Int.sub_congr b
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            c
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int))))
                          (@Eq.symm Int
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            (Lean.Omega.LinearCombo.sub_eval
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))))
              a b c a_1 a_2 a_3)
        fun (a b : ⋯) (a_1 : ⋯) (a_2 : ⋯) =>
        @Decidable.byContradiction (@Eq Int a b) (a.instDecidableEq b) fun (a_3 : ⋯) =>
          (fun (a b : ⋯) (a_4 : ⋯) (a_5 : ⋯) (a_6 : ⋯) =>
              @Or.elim (@LT.lt Int Int.instLTInt a b) (@LT.lt Int Int.instLTInt b a) False (@Int.lt_or_gt_of_ne a b a_6)
                (fun (h₁ : ⋯) =>
                  @Lean.Omega.Constraint.not_sat'_of_isImpossible
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                      upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                      Lean.Omega.Constraint }
                    (@of_decide_eq_true
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                            upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                            upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (@id
                        (@Eq Bool
                          (@Decidable.decide
                            (@Eq Bool
                              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                                  Lean.Omega.Constraint }.isImpossible
                              Bool.true)
                            (instDecidableEqBool
                              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                                  Lean.Omega.Constraint }.isImpossible
                              Bool.true))
                          Bool.true)
                        (@Eq.refl Bool Bool.true)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int)))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int)))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                      (Lean.Omega.combo_sat'
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                          upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                          Lean.Omega.Constraint }
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                          upperBound := @Option.none Int : Lean.Omega.Constraint }
                        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                          (@List.cons Int
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.nil Int)))
                        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                        (@Lean.Omega.Constraint.combine_sat'
                          { lowerBound := @Option.none Int,
                            upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                            Lean.Omega.Constraint }
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound := @Option.none Int : Lean.Omega.Constraint }
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                            (@List.cons Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@List.nil Int)))
                          (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                          (@Lean.Omega.tidy_sat
                            { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                              upperBound := @Option.none Int : Lean.Omega.Constraint }
                            (@List.cons Int
                              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)))
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                            (@Lean.Omega.Constraint.addInequality_sat
                              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                              (@List.cons Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)))
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                              (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b a)
                                ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int)) :
                                        Lean.Omega.LinearCombo }
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                Int.instLEInt (@Int.sub_nonneg_of_le b a a_5)
                                (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b a)
                                  (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                                  ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int)) :
                                          Lean.Omega.LinearCombo }
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  (@Lean.Omega.Int.sub_congr b
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    a
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    (@Eq.symm Int
                                      ((Lean.Omega.LinearCombo.coordinate
                                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                      b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.nil Int)))
                                    (@Eq.symm Int
                                      ((Lean.Omega.LinearCombo.coordinate
                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                      a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.cons Int b (@List.nil Int)))))
                                  (@Eq.symm Int
                                    ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                          (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                          {
                                            coeffs :=
                                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int)) :
                                            Lean.Omega.LinearCombo }
                                          {
                                            coeffs :=
                                              @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int) :
                                            Lean.Omega.LinearCombo }).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                      ({
                                            coeffs :=
                                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                  (@List.nil Int)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                      ({
                                            coeffs :=
                                              @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                                    (Lean.Omega.LinearCombo.sub_eval
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int)) :
                                        Lean.Omega.LinearCombo }
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))))))
                          (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                              (@List.cons Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@List.nil Int)))
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                            (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                              Int.instLEInt (@Int.sub_nonneg_of_le a b a_4)
                              (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                                (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                                ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                (@Lean.Omega.Int.sub_congr a
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  b
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.cons Int b (@List.nil Int))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.nil Int))))
                                (@Eq.symm Int
                                  ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                              (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                                (@List.nil Int)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                                  (Lean.Omega.LinearCombo.sub_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))))))
                        (@Lean.Omega.Constraint.addInequality_sat
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int
                            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)))
                          (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))
                          (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                            Int.instLEInt
                            (@Int.sub_nonneg_of_le b
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              (@Int.add_one_le_of_lt a b h₁))
                            (@Eq.trans Int
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int)) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                              (@Lean.Omega.Int.sub_congr b
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                (@Eq.symm Int
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.nil Int)))
                                (@Eq.trans Int
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int))))))
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.nil Int)))))
                                  (@Lean.Omega.Int.add_congr a
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      ⋯)
                                    ⋯ ⋯ ⋯ ⋯)
                                  ⋯))
                              ⋯))))))
                ⋯)
            ⋯ ⋯ ⋯ ⋯ ⋯)) (@Lean.Grind.OrderedAdd.mk (Int) (@instHAdd Int
      (@Lean.Grind.Semiring.toAdd Int
        (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (@Std.IsPreorder.mk Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
      (fun (a : Int) =>
        @Decidable.byContradiction (@LE.le Int Int.instLEInt a a) (a.decLe a)
          fun (a_1 : Not (@LE.le Int Int.instLEInt a a)) =>
          (fun (a : Int) (a_2 : Not (@LE.le Int Int.instLEInt a a)) =>
              @Lean.Omega.Constraint.not_sat'_of_isImpossible
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                  Lean.Omega.Constraint }
                (@of_decide_eq_true
                  (@Eq Bool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (instDecidableEqBool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (@id
                    (@Eq Bool
                      (@Decidable.decide
                        (@Eq Bool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true)
                        (instDecidableEqBool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true))
                      Bool.true)
                    (@Eq.refl Bool Bool.true)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                  (@Lean.Omega.Constraint.addInequality_sat
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                    (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                      Int.instLEInt
                      (@Int.sub_nonneg_of_le a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Int.add_one_le_of_lt a a (@Lean.Omega.Int.lt_of_not_le a a a_2)))
                      (@Eq.trans Int
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                        (@Lean.Omega.Int.sub_congr a
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@Eq.symm Int
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                          (@Eq.trans Int
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                            ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            (@Lean.Omega.Int.add_congr a
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                              (@id
                                (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                            (@Eq.symm Int
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                              (Lean.Omega.LinearCombo.add_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) : Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))))
                        (@Eq.symm Int
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ({
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                          (Lean.Omega.LinearCombo.sub_eval
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))))))))
            a a_1)
      fun (a b c : Int) (a_1 : @LE.le Int Int.instLEInt b a) (a_2 : @LE.le Int Int.instLEInt c b) =>
      @Decidable.byContradiction (@LE.le Int Int.instLEInt c a) (c.decLe a)
        fun (a_3 : Not (@LE.le Int Int.instLEInt c a)) =>
        (fun (a b c : Int) (a_4 : @LE.le Int Int.instLEInt b a) (a_5 : @LE.le Int Int.instLEInt c b)
              (a_6 : Not (@LE.le Int Int.instLEInt c a)) =>
            @Lean.Omega.Constraint.not_sat'_of_isImpossible
              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                upperBound :=
                  @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                Lean.Omega.Constraint }
              (@of_decide_eq_true
                (@Eq Bool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (instDecidableEqBool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (@id
                  (@Eq Bool
                    (@Decidable.decide
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true))
                    Bool.true)
                  (@Eq.refl Bool Bool.true)))
              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.nil Int))))
              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
              (@Lean.Omega.Constraint.combine_sat'
                { lowerBound := @Option.none Int,
                  upperBound :=
                    @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                  Lean.Omega.Constraint }
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                  upperBound := @Option.none Int : Lean.Omega.Constraint }
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.nil Int))))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (Lean.Omega.combo_sat'
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound := @Option.none Int : Lean.Omega.Constraint }
                    { lowerBound := @Option.none Int,
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int)))
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int))))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                    (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int)))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        Int.instLEInt (@Int.sub_nonneg_of_le a b a_4)
                        (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          (@Lean.Omega.Int.sub_congr a
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            b
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              a
                              (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int)))))
                          (@Eq.symm Int
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            (Lean.Omega.LinearCombo.sub_eval
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@Lean.Omega.Constraint.addInequality_sat
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                        (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          Int.instLEInt
                          (@Int.sub_nonneg_of_le c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@Int.add_one_le_of_lt a c (@Lean.Omega.Int.lt_of_not_le c a a_6)))
                          (@Eq.trans Int
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Lean.Omega.Int.sub_congr c
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int)))
                              (@Eq.trans Int
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@Lean.Omega.Int.add_congr a
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    a
                                    (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                      (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                                  (@id
                                    (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                    (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                (@Eq.symm Int
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                  (Lean.Omega.LinearCombo.add_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))
                            (@Eq.symm Int
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                              (Lean.Omega.LinearCombo.sub_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))))))
                (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                    ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                          (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }).eval
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                    Int.instLEInt (@Int.sub_nonneg_of_le b c a_5)
                    (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                              Lean.Omega.LinearCombo }
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int))) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                      (@Lean.Omega.Int.sub_congr b
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        c
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int))))
                      (@Eq.symm Int
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                        (Lean.Omega.LinearCombo.sub_eval
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))))
          a b c a_1 a_2 a_3) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   decide) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (1) (-1) (by
  decide) (by
  decide)) (by
  decide +kernel)
-/

-- Lean.Grind.Field.IsOrdered.lt_mul_inv_iff_mul_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.lt_mul_inv_iff_mul_lt.h5 : ¬∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R] (a b : R)
        {c : R}, 0 < c → Std.IsLinearOrder R := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) (⟨fun a b => a < b⟩ : LE Rat) (Rat.instLT) (@Std.LawfulOrderLT.mk (Rat) (Rat.instLT) (@LE.mk Rat fun (a b : Rat) => @LT.lt Rat Rat.instLT a b) (by (try dsimp only);   grind)) (0) (0) (1) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPartialOrder.toIsPreorder.le_refl (0 : Rat))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedAdd.add_lt_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h2 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Lean.Grind.AddCommMonoid M] [inst_2 : LT M] [inst_3 : Std.LawfulOrderLT M]
        {a b : M}, a < b → ∀ (c : M), Std.IsPreorder M := fun hc_h => absurd (@hc_h (Int : Type) (⟨fun a b => a < b⟩ : LE Int) (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (0) (1) (by
  decide) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff.h2 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Lean.Grind.IntModule M] [inst_2 : LT M] [inst_3 : Std.LawfulOrderLT M] (k : Int)
        {a b : M}, a < b → Std.IsPreorder M := fun hc_h => absurd (@hc_h (Int : Type) (⟨fun a b => a < b⟩ : LE Int) (Lean.Grind.Ring.toIntModule) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (0) (0) (1) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff.h6.inst : Not
      (Iff
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
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff.h6.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff.h6 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : @Std.IsPreorder M inst] [inst_2 : Lean.Grind.IntModule M]
        [inst :
          @Lean.Grind.OrderedAdd M
            (@instHAdd M
              (@Lean.Grind.AddCommMonoid.toAdd M
                (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2))))
            inst inst_1]
        [inst : LT M] (k : Int) {a b : M},
        @LT.lt M inst a b →
          Iff
            (@LT.lt M inst (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k a)
              (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k b))
            (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff.h6.inst (@hc_h (Int) (Int.instLEInt) _ (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@LT.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt a b) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_lt_zsmul_iff.h6.prem0)

-- Lean.Grind.CommRing.le_true_of_kronLin, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h3.inst : ¬False = True := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h3.prem0 : (Lean.Grind.CommRing.Expr.num 0).linOk_k (Lean.Grind.CommRing.Expr.num 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h3.prem1 : Lean.Grind.CommRing.Expr.kronOk_k 0 (Lean.Grind.CommRing.Expr.num 0) (Lean.Grind.CommRing.Expr.num 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h3.prem2 : Lean.Grind.CommRing.Expr.kronLinEval_k 0 (Lean.Grind.CommRing.Expr.num 0) =
      Lean.Grind.CommRing.Expr.kronLinEval_k 0 (Lean.Grind.CommRing.Expr.num 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h3 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] (ctx : Lean.Grind.CommRing.Context α) (K : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        a.linOk_k b = Bool.true →
          Lean.Grind.CommRing.Expr.kronOk_k K a b = Bool.true →
            Lean.Grind.CommRing.Expr.kronLinEval_k K a = Lean.Grind.CommRing.Expr.kronLinEval_k K b →
              (Lean.Grind.CommRing.Expr.denote ctx a ≤ Lean.Grind.CommRing.Expr.denote ctx b) = True := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h3.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) ({ le := fun (x x_1 : Int) => False : LE Int }) (Lean.RArray.leaf 1) (0) (Lean.Grind.CommRing.Expr.num 0) (Lean.Grind.CommRing.Expr.num 0) HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h3.prem0 HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h3.prem1 HypCheckProof.Lean.Grind.CommRing.le_true_of_kronLin.h3.prem2)

-- Lean.Grind.Linarith.le_of_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Linarith.le_of_eq.h3 : ¬∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] (ctx : Lean.Grind.Linarith.Context α)
        (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        Lean.Grind.Linarith.norm_cert lhs rhs p = Bool.true →
          Lean.Grind.Linarith.Expr.denote_k ctx lhs = Lean.Grind.Linarith.Expr.denote_k ctx rhs → Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.Ring.toIntModule) (⟨fun _ _ => False⟩ : LE Int) (.leaf 1 : Lean.RArray Int) (.zero : Lean.Grind.Linarith.Expr) (.zero : Lean.Grind.Linarith.Expr) (.nil : Lean.Grind.Linarith.Poly) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.Linarith.le_norm, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_norm.h3.inst : Not (@Std.IsPreorder Int (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b)) := by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_norm.h3.prem0 : @Eq Bool
      (Lean.Grind.Linarith.norm_cert Lean.Grind.Linarith.Expr.zero
        (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_norm.h3.prem1 : @LT.lt Int Int.instLTInt
      (@Lean.Grind.Linarith.Expr.denote_k Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Expr.zero)
      (@Lean.Grind.Linarith.Expr.denote_k Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.le_norm.h3 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] (ctx : Lean.Grind.Linarith.Context α)
        (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.norm_cert lhs rhs p) Bool.true →
          @LE.le α inst_1 (@Lean.Grind.Linarith.Expr.denote_k α inst ctx lhs)
              (@Lean.Grind.Linarith.Expr.denote_k α inst ctx rhs) →
            @Std.IsPreorder α inst_1) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.le_norm.h3.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.le_norm.h3.prem0 HypCheckProof.Lean.Grind.Linarith.le_norm.h3.prem1)

-- Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_neg_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_neg_left.h5 : ¬∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R] {a b : R}
        {c : R}, c < 0 → Std.IsLinearOrder R := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) (⟨fun a b => a < b⟩ : LE Rat) (Rat.instLT) (@Std.LawfulOrderLT.mk (Rat) (Rat.instLT) (@LE.mk Rat fun (a b : Rat) => @LT.lt Rat Rat.instLT a b) (by (try dsimp only);   grind)) (0) (0) (-1) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPartialOrder.toIsPreorder.le_refl (0 : Rat))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.Field.IsOrdered.mul_inv_le_iff_mul_le_of_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.mul_inv_le_iff_mul_le_of_neg.h5 : ¬∀ {R : Type} [inst : Lean.Grind.Field R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R] (a c : R)
        {b : R}, b < 0 → Std.IsLinearOrder R := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) (⟨fun a b => a < b⟩ : LE Rat) (Rat.instLT) (@Std.LawfulOrderLT.mk (Rat) (Rat.instLT) (@LE.mk Rat fun (a b : Rat) => @LT.lt Rat Rat.instLT a b) (by (try dsimp only);   grind)) (0) (0) (-1) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPartialOrder.toIsPreorder.le_refl (0 : Rat))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.Field.NormNum.sub_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.sub_eq.h2 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] (a b : α) (v₁ v₂ v : Rat),
        (v == v₁ - v₂) = Bool.true →
          a = Lean.Grind.Field.NormNum.ofRat v₁ →
            b = Lean.Grind.Field.NormNum.ofRat v₂ → a - b = Lean.Grind.Field.NormNum.ofRat v := fun hc_h => absurd (@hc_h (Fin 2 : Type) ({ (inferInstance : Lean.Grind.CommRing (Fin 2)) with inv := id, div := (· * ·), zpow := ⟨fun a n => a ^ n.natAbs⟩, div_eq_mul_inv := (by decide), zero_ne_one := (by decide), inv_zero := (by decide), mul_inv_cancel := (by decide), zpow_zero := fun a => Lean.Grind.Semiring.pow_zero a, zpow_succ := fun a n => Lean.Grind.Semiring.pow_succ a n, zpow_neg := (by intro a n; show a ^ (-n).natAbs = a ^ n.natAbs; rw [Int.natAbs_neg]) } : Lean.Grind.Field (Fin 2)) _ _ (1) (1 / 2) _ (beq_self_eq_true _) rfl rfl) (by
  decide +kernel)

-- Lean.Grind.CommRing.le_norm_expr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_expr.h4 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst : LE α] [inst_1 : LT α] (ctx : Lean.Grind.CommRing.Context α)
        (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr),
        Lean.Grind.CommRing.norm_cnstr_cert lhs rhs lhs' rhs' = Bool.true → Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt) (⟨fun _ _ => False⟩ : LE Int) (Int.instLTInt) (.leaf 1 : Lean.RArray Int) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (.num 0 : Lean.Grind.CommRing.Expr) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedRing.natCast_lt_natCast_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.natCast_lt_natCast_of_lt.h5 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst : LE R] [inst_1 : LT R] [inst_2 : Std.LawfulOrderLT R] (a b : Nat),
        a < b → Std.IsPreorder R := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (0) (1) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedRing.natCast_lt_natCast_of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.natCast_lt_natCast_of_lt.h6 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1] (a b : Nat),
        @LT.lt Nat instLTNat a b →
          @LT.lt R inst_2 (@Nat.cast R (@Lean.Grind.Semiring.natCast R (@Lean.Grind.Ring.toSemiring R inst)) a)
            (@Nat.cast R (@Lean.Grind.Semiring.natCast R (@Lean.Grind.Ring.toSemiring R inst)) b)) := fun hc_h => absurd (@hc_h (Fin 2 : Type) (@Lean.Grind.CommRing.toRing (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Lean.Grind.Fin.instCommRingFinOfNeZeroNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) (@instLEFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@instLTFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) _ _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.OrderedAdd.zsmul_pos_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_pos_iff.h2 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Lean.Grind.IntModule M] [inst_2 : LT M] [inst_3 : Std.LawfulOrderLT M] (k : Int)
        {x : M}, 0 < x → Std.IsPreorder M := fun hc_h => absurd (@hc_h (Int : Type) (⟨fun a b => a < b⟩ : LE Int) (Lean.Grind.Ring.toIntModule) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (0) (1) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedAdd.zsmul_pos_iff, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_pos_iff.h6.inst : Not
      (Iff
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
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_pos_iff.h6.prem0 : @LE.le Int Int.instLEInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_pos_iff.h6 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : @Std.IsPreorder M inst] [inst_2 : Lean.Grind.IntModule M]
        [inst :
          @Lean.Grind.OrderedAdd M
            (@instHAdd M
              (@Lean.Grind.AddCommMonoid.toAdd M
                (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2))))
            inst inst_1]
        [inst : LT M] (k : Int) {x : M},
        @LT.lt M inst
            (@OfNat.ofNat M (nat_lit 0)
              (@Zero.toOfNat0 M
                (@Lean.Grind.AddCommMonoid.toZero M
                  (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2)))))
            x →
          Iff
            (@LT.lt M inst
              (@OfNat.ofNat M (nat_lit 0)
                (@Zero.toOfNat0 M
                  (@Lean.Grind.AddCommMonoid.toZero M
                    (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_2)))))
              (@HSMul.hSMul Int M M (@instHSMul Int M (@Lean.Grind.IntModule.zsmul M inst_2)) k x))
            (@LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_pos_iff.h6.inst (@hc_h (Int) (Int.instLEInt) _ (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) _ (@LT.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt a b) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_pos_iff.h6.prem0)

-- Lean.Grind.OrderedAdd.zsmul_le_zsmul, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h2.inst : Not (@Std.IsPreorder Int (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b)) := by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h2.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h2.prem1 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h2 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : Lean.Grind.IntModule M] {a b : M} {k : Int},
        @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k →
          @LE.le M inst a b → @Std.IsPreorder M inst) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h2.inst (@hc_h (Int) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h2.prem0 HypCheckProof.Lean.Grind.OrderedAdd.zsmul_le_zsmul.h2.prem1)

-- Lean.Grind.OrderedRing.mul_pos, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h4.inst : Not (@Std.IsPreorder Int (@LE.mk Int fun (x x_1 : Int) => False)) := by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h4.prem0 : @LE.le Int Int.instLEInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h4.prem1 : @LE.le Int Int.instLEInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h4 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] {a b : R},
        @LT.lt R inst_2
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
            a →
          @LT.lt R inst_2
              (@OfNat.ofNat R (nat_lit 0)
                (@Zero.toOfNat0 R
                  (@Lean.Grind.AddCommMonoid.toZero R
                    (@Lean.Grind.NatModule.toAddCommMonoid R
                      (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
              b →
            @Std.IsPreorder R inst_1) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h4.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@LE.mk Int fun (x x_1 : Int) => False) (@LT.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt a b) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h4.prem0 HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h4.prem1)

-- Lean.Grind.OrderedRing.le_of_intCast_le_intCast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.le_of_intCast_le_intCast.h4 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.IsPreorder R inst_1]
        [inst_4 : @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2 inst_3] (a b : Int),
        @LE.le R inst_1 (@Int.cast R (@Lean.Grind.Ring.intCast R inst) a)
            (@Int.cast R (@Lean.Grind.Ring.intCast R inst) b) →
          @LE.le Int Int.instLEInt a b) := fun hc_h => absurd (@hc_h (Int : Type) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (⟨fun _ _ => True⟩ : LE Int) (Int.instLTInt) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (x x_1 : Int) => True) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.OrderedRing.mk (Int) (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (x x_1 : Int) => True) (Int.instLTInt) (@Std.IsPreorder.mk Int (@LE.mk Int fun (x x_1 : Int) => True) (fun (a : Int) => True.intro)
      fun (a b c : Int) (a_1 a_2 : True) => a_2) (@Lean.Grind.OrderedAdd.mk (Int) (@instHAdd Int
      (@Lean.Grind.Semiring.toAdd Int
        (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))) (@LE.mk Int fun (x x_1 : Int) => True) (@Std.IsPreorder.mk Int (@LE.mk Int fun (x x_1 : Int) => True) (fun (a : Int) => True.intro)
      fun (a b c : Int) (a_1 a_2 : True) => a_2) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   decide) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Lean.Grind.OrderedRing.le_of_intCast_le_intCast, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.le_of_intCast_le_intCast.h5.inst : Not (@Std.IsPreorder Int (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b)) := by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.le_of_intCast_le_intCast.h5.prem0 : @LT.lt Int Int.instLTInt
      (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.le_of_intCast_le_intCast.h5 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        (a b : Int),
        @LE.le R inst_1 (@Int.cast R (@Lean.Grind.Ring.intCast R inst) a)
            (@Int.cast R (@Lean.Grind.Ring.intCast R inst) b) →
          @Std.IsPreorder R inst_1) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.le_of_intCast_le_intCast.h5.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedRing.le_of_intCast_le_intCast.h5.prem0)

-- Lean.Grind.OrderedRing.lt_of_natCast_lt_natCast, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.lt_of_natCast_lt_natCast.h5 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        (a b : Nat),
        @LT.lt R inst_2 (@Nat.cast R (@Lean.Grind.Semiring.natCast R (@Lean.Grind.Ring.toSemiring R inst)) a)
            (@Nat.cast R (@Lean.Grind.Semiring.natCast R (@Lean.Grind.Ring.toSemiring R inst)) b) →
          @Std.IsPreorder R inst_1) := fun hc_h => absurd (@hc_h (Int : Type) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedRing.lt_of_natCast_lt_natCast, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.lt_of_natCast_lt_natCast.h6 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1] (a b : Nat),
        @LT.lt R inst_2 (@Nat.cast R (@Lean.Grind.Semiring.natCast R (@Lean.Grind.Ring.toSemiring R inst)) a)
            (@Nat.cast R (@Lean.Grind.Semiring.natCast R (@Lean.Grind.Ring.toSemiring R inst)) b) →
          @LT.lt Nat instLTNat a b) := fun hc_h => absurd (@hc_h (Fin 2 : Type) (@Lean.Grind.CommRing.toRing (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Lean.Grind.Fin.instCommRingFinOfNeZeroNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) (@instLEFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@instLTFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) _ _ (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.Order.le_eq_true_k, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_k.h3 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.IsPreorder α inst] [inst_3 : Lean.Grind.Ring α]
        [inst_4 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_3) inst inst_1 inst_2] {a : α} {k : Int},
        @Eq Bool (Int.ble' (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k) Bool.true →
          @Eq Prop
            (@LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_3))) a
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_3) k)))
            True) := fun hc_h => absurd (@hc_h (Int : Type) (⟨fun a b => b ≤ a⟩ : LE Int) (Int.instLTInt) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.Grind.OrderedRing.mk (Int) (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (Int.instLTInt) (@Std.IsPreorder.mk Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
      (fun (a : Int) =>
        @Decidable.byContradiction (@LE.le Int Int.instLEInt a a) (a.decLe a)
          fun (a_1 : Not (@LE.le Int Int.instLEInt a a)) =>
          (fun (a : Int) (a_2 : Not (@LE.le Int Int.instLEInt a a)) =>
              @Lean.Omega.Constraint.not_sat'_of_isImpossible
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                  Lean.Omega.Constraint }
                (@of_decide_eq_true
                  (@Eq Bool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (instDecidableEqBool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (@id
                    (@Eq Bool
                      (@Decidable.decide
                        (@Eq Bool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true)
                        (instDecidableEqBool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true))
                      Bool.true)
                    (@Eq.refl Bool Bool.true)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                  (@Lean.Omega.Constraint.addInequality_sat
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                    (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                      Int.instLEInt
                      (@Int.sub_nonneg_of_le a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Int.add_one_le_of_lt a a (@Lean.Omega.Int.lt_of_not_le a a a_2)))
                      (@Eq.trans Int
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                        (@Lean.Omega.Int.sub_congr a
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@Eq.symm Int
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                          (@Eq.trans Int
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                            ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            (@Lean.Omega.Int.add_congr a
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                              (@id
                                (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                            (@Eq.symm Int
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                              (Lean.Omega.LinearCombo.add_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) : Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))))
                        (@Eq.symm Int
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ({
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                          (Lean.Omega.LinearCombo.sub_eval
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))))))))
            a a_1)
      fun (a b c : Int) (a_1 : @LE.le Int Int.instLEInt b a) (a_2 : @LE.le Int Int.instLEInt c b) =>
      @Decidable.byContradiction (@LE.le Int Int.instLEInt c a) (c.decLe a)
        fun (a_3 : Not (@LE.le Int Int.instLEInt c a)) =>
        (fun (a b c : Int) (a_4 : @LE.le Int Int.instLEInt b a) (a_5 : @LE.le Int Int.instLEInt c b)
              (a_6 : Not (@LE.le Int Int.instLEInt c a)) =>
            @Lean.Omega.Constraint.not_sat'_of_isImpossible
              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                upperBound :=
                  @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                Lean.Omega.Constraint }
              (@of_decide_eq_true
                (@Eq Bool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (instDecidableEqBool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (@id
                  (@Eq Bool
                    (@Decidable.decide
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true))
                    Bool.true)
                  (@Eq.refl Bool Bool.true)))
              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.nil Int))))
              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
              (@Lean.Omega.Constraint.combine_sat'
                { lowerBound := @Option.none Int,
                  upperBound :=
                    @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                  Lean.Omega.Constraint }
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                  upperBound := @Option.none Int : Lean.Omega.Constraint }
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.nil Int))))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (Lean.Omega.combo_sat'
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound := @Option.none Int : Lean.Omega.Constraint }
                    { lowerBound := @Option.none Int,
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int)))
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int))))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                    (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int)))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        Int.instLEInt (@Int.sub_nonneg_of_le a b a_4)
                        (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          (@Lean.Omega.Int.sub_congr a
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            b
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              a
                              (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int)))))
                          (@Eq.symm Int
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            (Lean.Omega.LinearCombo.sub_eval
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@Lean.Omega.Constraint.addInequality_sat
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                        (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          Int.instLEInt
                          (@Int.sub_nonneg_of_le c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@Int.add_one_le_of_lt a c (@Lean.Omega.Int.lt_of_not_le c a a_6)))
                          (@Eq.trans Int
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Lean.Omega.Int.sub_congr c
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int)))
                              (@Eq.trans Int
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@Lean.Omega.Int.add_congr a
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    a
                                    (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                      (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                                  (@id
                                    (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                    (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                (@Eq.symm Int
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                  (Lean.Omega.LinearCombo.add_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))
                            (@Eq.symm Int
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                              (Lean.Omega.LinearCombo.sub_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))))))
                (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                    ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                          (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }).eval
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                    Int.instLEInt (@Int.sub_nonneg_of_le b c a_5)
                    (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                              Lean.Omega.LinearCombo }
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int))) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                      (@Lean.Omega.Int.sub_congr b
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        c
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int))))
                      (@Eq.symm Int
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                        (Lean.Omega.LinearCombo.sub_eval
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))))
          a b c a_1 a_2 a_3) (@Lean.Grind.OrderedAdd.mk (Int) (@instHAdd Int
      (@Lean.Grind.Semiring.toAdd Int
        (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (@Std.IsPreorder.mk Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
      (fun (a : Int) =>
        @Decidable.byContradiction (@LE.le Int Int.instLEInt a a) (a.decLe a)
          fun (a_1 : Not (@LE.le Int Int.instLEInt a a)) =>
          (fun (a : Int) (a_2 : Not (@LE.le Int Int.instLEInt a a)) =>
              @Lean.Omega.Constraint.not_sat'_of_isImpossible
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                  Lean.Omega.Constraint }
                (@of_decide_eq_true
                  (@Eq Bool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (instDecidableEqBool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (@id
                    (@Eq Bool
                      (@Decidable.decide
                        (@Eq Bool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true)
                        (instDecidableEqBool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true))
                      Bool.true)
                    (@Eq.refl Bool Bool.true)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                  (@Lean.Omega.Constraint.addInequality_sat
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                    (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                      Int.instLEInt
                      (@Int.sub_nonneg_of_le a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Int.add_one_le_of_lt a a (@Lean.Omega.Int.lt_of_not_le a a a_2)))
                      (@Eq.trans Int
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                        (@Lean.Omega.Int.sub_congr a
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@Eq.symm Int
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                          (@Eq.trans Int
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                            ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            (@Lean.Omega.Int.add_congr a
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                              (@id
                                (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                            (@Eq.symm Int
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                              (Lean.Omega.LinearCombo.add_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) : Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))))
                        (@Eq.symm Int
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ({
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                          (Lean.Omega.LinearCombo.sub_eval
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))))))))
            a a_1)
      fun (a b c : Int) (a_1 : @LE.le Int Int.instLEInt b a) (a_2 : @LE.le Int Int.instLEInt c b) =>
      @Decidable.byContradiction (@LE.le Int Int.instLEInt c a) (c.decLe a)
        fun (a_3 : Not (@LE.le Int Int.instLEInt c a)) =>
        (fun (a b c : Int) (a_4 : @LE.le Int Int.instLEInt b a) (a_5 : @LE.le Int Int.instLEInt c b)
              (a_6 : Not (@LE.le Int Int.instLEInt c a)) =>
            @Lean.Omega.Constraint.not_sat'_of_isImpossible
              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                upperBound :=
                  @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                Lean.Omega.Constraint }
              (@of_decide_eq_true
                (@Eq Bool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (instDecidableEqBool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (@id
                  (@Eq Bool
                    (@Decidable.decide
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true))
                    Bool.true)
                  (@Eq.refl Bool Bool.true)))
              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.nil Int))))
              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
              (@Lean.Omega.Constraint.combine_sat'
                { lowerBound := @Option.none Int,
                  upperBound :=
                    @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                  Lean.Omega.Constraint }
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                  upperBound := @Option.none Int : Lean.Omega.Constraint }
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.nil Int))))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (Lean.Omega.combo_sat'
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound := @Option.none Int : Lean.Omega.Constraint }
                    { lowerBound := @Option.none Int,
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int)))
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int))))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                    (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int)))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        Int.instLEInt (@Int.sub_nonneg_of_le a b a_4)
                        (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          (@Lean.Omega.Int.sub_congr a
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            b
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              a
                              (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int)))))
                          (@Eq.symm Int
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            (Lean.Omega.LinearCombo.sub_eval
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@Lean.Omega.Constraint.addInequality_sat
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                        (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          Int.instLEInt
                          (@Int.sub_nonneg_of_le c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@Int.add_one_le_of_lt a c (@Lean.Omega.Int.lt_of_not_le c a a_6)))
                          (@Eq.trans Int
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Lean.Omega.Int.sub_congr c
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int)))
                              (@Eq.trans Int
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@Lean.Omega.Int.add_congr a
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    a
                                    (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                      (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                                  (@id
                                    (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                    (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                (@Eq.symm Int
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                  (Lean.Omega.LinearCombo.add_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))
                            (@Eq.symm Int
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                              (Lean.Omega.LinearCombo.sub_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))))))
                (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                    ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                          (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }).eval
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                    Int.instLEInt (@Int.sub_nonneg_of_le b c a_5)
                    (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                              Lean.Omega.LinearCombo }
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int))) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                      (@Lean.Omega.Int.sub_congr b
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        c
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int))))
                      (@Eq.symm Int
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                        (Lean.Omega.LinearCombo.sub_eval
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))))
          a b c a_1 a_2 a_3) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   decide) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.Order.le_eq_true_k, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_k.h4 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α] [inst_3 : Lean.Grind.Ring α] {a : α}
        {k : Int}, Int.ble' 0 k = Bool.true → Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (Lean.Grind.instCommRingInt.toRing) (0) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.Order.le_eq_true_k, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_true_k.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α] {a : α} {k : Int},
        @Eq Bool (Int.ble' (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k) Bool.true →
          @Eq Prop
            (@LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k)))
            True) := fun hc_h => absurd (@hc_h (Fin 2 : Type) (@instLEFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@instLTFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) _ _ (@Lean.Grind.CommRing.toRing (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Lean.Grind.Fin.instCommRingFinOfNeZeroNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
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
          (@Eq.refl Bool Bool.true)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.OrderedRing.pos_intCast_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.pos_intCast_of_pos.h5 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst : LE R] [inst_1 : LT R] [inst_2 : Std.LawfulOrderLT R] (a : Int),
        0 < a → Std.IsPreorder R := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (1) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedRing.pos_intCast_of_pos, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.pos_intCast_of_pos.h6.inst : Not False := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.pos_intCast_of_pos.h6.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.pos_intCast_of_pos.h6 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1] (a : Int),
        @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) a →
          @LT.lt R inst_2
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
            (@Int.cast R (@Lean.Grind.Ring.intCast R inst) a)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.pos_intCast_of_pos.h6.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@LE.mk Int fun (x x_1 : Int) => True) (@LT.mk Int fun (x x_1 : Int) => False) (@Std.LawfulOrderLT.mk (Int) (@LT.mk Int fun (x x_1 : Int) => False) (@LE.mk Int fun (x x_1 : Int) => True) (by (try dsimp only);   (intros; simp_all; done))) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (x x_1 : Int) => True) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; omega))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedRing.pos_intCast_of_pos.h6.prem0)

-- Lean.Grind.CommRing.le_true_of_denote_eq, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h3.inst : Not (@Eq Prop False True) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h3.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h3.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h3 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] (ctx : Lean.Grind.CommRing.Context α)
        (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p) →
            @Eq Prop
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h3.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@LE.mk Int fun (x x_1 : Int) => False) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h3.prem0 HypCheckProof.Lean.Grind.CommRing.le_true_of_denote_eq.h3.prem1)

-- Lean.Grind.OrderedAdd.add_lt_left_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left_iff.h2 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Lean.Grind.AddCommMonoid M] [inst_2 : LT M] [inst_3 : Std.LawfulOrderLT M]
        {a b : M} (c : M), Std.IsPreorder M := fun hc_h => absurd (@hc_h (Int : Type) (⟨fun a b => a < b⟩ : LE Int) (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedAdd.zsmul_nonpos, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h2.inst : Not (@Std.IsPreorder Int (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b)) := by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h2.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h2.prem1 : @LT.lt Int Int.instLTInt (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h2 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : Lean.Grind.IntModule M] {k : Int} {a : M},
        @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) k →
          @LE.le M inst a
              (@OfNat.ofNat M (nat_lit 0)
                (@Zero.toOfNat0 M
                  (@Lean.Grind.AddCommMonoid.toZero M
                    (@Lean.Grind.NatModule.toAddCommMonoid M (@Lean.Grind.IntModule.toNatModule M inst_1))))) →
            @Std.IsPreorder M inst) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h2.inst (@hc_h (Int) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h2.prem0 HypCheckProof.Lean.Grind.OrderedAdd.zsmul_nonpos.h2.prem1)

-- Lean.Grind.OrderedRing.pos_natCast_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.pos_natCast_of_pos.h5 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst : LE R] [inst_1 : LT R] [inst_2 : Std.LawfulOrderLT R] (a : Nat),
        0 < a → Std.IsPreorder R := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (1) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedRing.pos_natCast_of_pos, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.pos_natCast_of_pos.h6 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1] (a : Nat),
        @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a →
          @LT.lt R inst_2
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
            (@Nat.cast R (@Lean.Grind.Semiring.natCast R (@Lean.Grind.Ring.toSemiring R inst)) a)) := fun hc_h => absurd (@hc_h (Fin 2 : Type) (@Lean.Grind.CommRing.toRing (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Lean.Grind.Fin.instCommRingFinOfNeZeroNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) (@instLEFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@instLTFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) _ _ (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.OrderedRing.mul_pos_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos_iff.h5 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst : LE R] [inst_1 : LT R] [inst_2 : Std.LawfulOrderLT R] {a b : R},
        Std.IsLinearOrder R := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPartialOrder.toIsPreorder.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedAdd.nsmul_nonneg, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_nonneg.h2.inst : Not (@Std.IsPreorder Int (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b)) := by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_nonneg.h2.prem0 : @LT.lt Int Int.instLTInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_nonneg.h2 : Not
      (∀ {M : Type} [inst : LE M] [inst_1 : Lean.Grind.NatModule M] {k : Nat} {a : M},
        @LE.le M inst
            (@OfNat.ofNat M (nat_lit 0)
              (@Zero.toOfNat0 M (@Lean.Grind.AddCommMonoid.toZero M (@Lean.Grind.NatModule.toAddCommMonoid M inst_1))))
            a →
          @Std.IsPreorder M inst) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.nsmul_nonneg.h2.inst (@hc_h (Int) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (@Lean.Grind.Semiring.toNatModule Int
      (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedAdd.nsmul_nonneg.h2.prem0)

-- Lean.Grind.Linarith.lt_unsat, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_unsat.h4.inst : Not False := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_unsat.h4.prem0 : @LE.le Int Int.instLEInt
      (@Lean.Grind.Linarith.Poly.denote Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Poly.nil)
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.IntModule.toNatModule Int
                (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.lt_unsat.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.Linarith.Context α),
        @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote α inst ctx Lean.Grind.Linarith.Poly.nil)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
          False) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.lt_unsat.h4.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (@LT.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt a b) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.Linarith.lt_unsat.h4.prem0)

-- Lean.Grind.OrderedRing.natCast_nonneg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.natCast_nonneg.h4 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.IsPreorder R inst_1]
        [inst_4 : @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2 inst_3] {a : Nat},
        @LE.le R inst_1
          (@OfNat.ofNat R (nat_lit 0)
            (@Zero.toOfNat0 R
              (@Lean.Grind.AddCommMonoid.toZero R
                (@Lean.Grind.NatModule.toAddCommMonoid R
                  (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
          (@Nat.cast R (@Lean.Grind.Semiring.natCast R (@Lean.Grind.Ring.toSemiring R inst)) a)) := fun hc_h => absurd (@hc_h (Int : Type) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (⟨fun a b => b ≤ a⟩ : LE Int) (Int.instLTInt) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (@Lean.Grind.OrderedRing.mk (Int) (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (Int.instLTInt) (@Std.IsPreorder.mk Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
      (fun (a : Int) =>
        @Decidable.byContradiction (@LE.le Int Int.instLEInt a a) (a.decLe a)
          fun (a_1 : Not (@LE.le Int Int.instLEInt a a)) =>
          (fun (a : Int) (a_2 : Not (@LE.le Int Int.instLEInt a a)) =>
              @Lean.Omega.Constraint.not_sat'_of_isImpossible
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                  Lean.Omega.Constraint }
                (@of_decide_eq_true
                  (@Eq Bool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (instDecidableEqBool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (@id
                    (@Eq Bool
                      (@Decidable.decide
                        (@Eq Bool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true)
                        (instDecidableEqBool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true))
                      Bool.true)
                    (@Eq.refl Bool Bool.true)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                  (@Lean.Omega.Constraint.addInequality_sat
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                    (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                      Int.instLEInt
                      (@Int.sub_nonneg_of_le a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Int.add_one_le_of_lt a a (@Lean.Omega.Int.lt_of_not_le a a a_2)))
                      (@Eq.trans Int
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                        (@Lean.Omega.Int.sub_congr a
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@Eq.symm Int
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                          (@Eq.trans Int
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                            ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            (@Lean.Omega.Int.add_congr a
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                              (@id
                                (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                            (@Eq.symm Int
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                              (Lean.Omega.LinearCombo.add_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) : Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))))
                        (@Eq.symm Int
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ({
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                          (Lean.Omega.LinearCombo.sub_eval
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))))))))
            a a_1)
      fun (a b c : Int) (a_1 : @LE.le Int Int.instLEInt b a) (a_2 : @LE.le Int Int.instLEInt c b) =>
      @Decidable.byContradiction (@LE.le Int Int.instLEInt c a) (c.decLe a)
        fun (a_3 : Not (@LE.le Int Int.instLEInt c a)) =>
        (fun (a b c : Int) (a_4 : @LE.le Int Int.instLEInt b a) (a_5 : @LE.le Int Int.instLEInt c b)
              (a_6 : Not (@LE.le Int Int.instLEInt c a)) =>
            @Lean.Omega.Constraint.not_sat'_of_isImpossible
              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                upperBound :=
                  @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                Lean.Omega.Constraint }
              (@of_decide_eq_true
                (@Eq Bool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (instDecidableEqBool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (@id
                  (@Eq Bool
                    (@Decidable.decide
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true))
                    Bool.true)
                  (@Eq.refl Bool Bool.true)))
              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.nil Int))))
              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
              (@Lean.Omega.Constraint.combine_sat'
                { lowerBound := @Option.none Int,
                  upperBound :=
                    @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                  Lean.Omega.Constraint }
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                  upperBound := @Option.none Int : Lean.Omega.Constraint }
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.nil Int))))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (Lean.Omega.combo_sat'
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound := @Option.none Int : Lean.Omega.Constraint }
                    { lowerBound := @Option.none Int,
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int)))
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int))))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                    (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int)))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        Int.instLEInt (@Int.sub_nonneg_of_le a b a_4)
                        (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          (@Lean.Omega.Int.sub_congr a
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            b
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              a
                              (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int)))))
                          (@Eq.symm Int
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            (Lean.Omega.LinearCombo.sub_eval
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@Lean.Omega.Constraint.addInequality_sat
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                        (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          Int.instLEInt
                          (@Int.sub_nonneg_of_le c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@Int.add_one_le_of_lt a c (@Lean.Omega.Int.lt_of_not_le c a a_6)))
                          (@Eq.trans Int
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Lean.Omega.Int.sub_congr c
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int)))
                              (@Eq.trans Int
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@Lean.Omega.Int.add_congr a
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    a
                                    (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                      (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                                  (@id
                                    (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                    (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                (@Eq.symm Int
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                  (Lean.Omega.LinearCombo.add_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))
                            (@Eq.symm Int
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                              (Lean.Omega.LinearCombo.sub_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))))))
                (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                    ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                          (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }).eval
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                    Int.instLEInt (@Int.sub_nonneg_of_le b c a_5)
                    (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                              Lean.Omega.LinearCombo }
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int))) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                      (@Lean.Omega.Int.sub_congr b
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        c
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int))))
                      (@Eq.symm Int
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                        (Lean.Omega.LinearCombo.sub_eval
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))))
          a b c a_1 a_2 a_3) (@Lean.Grind.OrderedAdd.mk (Int) (@instHAdd Int
      (@Lean.Grind.Semiring.toAdd Int
        (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (@Std.IsPreorder.mk Int (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a)
      (fun (a : Int) =>
        @Decidable.byContradiction (@LE.le Int Int.instLEInt a a) (a.decLe a)
          fun (a_1 : Not (@LE.le Int Int.instLEInt a a)) =>
          (fun (a : Int) (a_2 : Not (@LE.le Int Int.instLEInt a a)) =>
              @Lean.Omega.Constraint.not_sat'_of_isImpossible
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                  upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                  Lean.Omega.Constraint }
                (@of_decide_eq_true
                  (@Eq Bool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (instDecidableEqBool
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                        Lean.Omega.Constraint }.isImpossible
                    Bool.true)
                  (@id
                    (@Eq Bool
                      (@Decidable.decide
                        (@Eq Bool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true)
                        (instDecidableEqBool
                          { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                              upperBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) :
                              Lean.Omega.Constraint }.isImpossible
                          Bool.true))
                      Bool.true)
                    (@Eq.refl Bool Bool.true)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                  (@Lean.Omega.Constraint.addInequality_sat
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@List.nil Int))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))
                    (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                      Int.instLEInt
                      (@Int.sub_nonneg_of_le a
                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Int.add_one_le_of_lt a a (@Lean.Omega.Int.lt_of_not_le a a a_2)))
                      (@Eq.trans Int
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                        (@Lean.Omega.Int.sub_congr a
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@Eq.symm Int
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                          (@Eq.trans Int
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                            ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            (@Lean.Omega.Int.add_congr a
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                              ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                a (@Lean.Omega.LinearCombo.coordinate_eval_0 a (@List.nil Int)))
                              (@id
                                (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                                (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                            (@Eq.symm Int
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                              (Lean.Omega.LinearCombo.add_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) : Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))))
                        (@Eq.symm Int
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ({
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))
                            ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }.eval
                              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int)))))
                          (Lean.Omega.LinearCombo.sub_eval
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                              Lean.Omega.LinearCombo }
                            (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.nil Int))))))))))
            a a_1)
      fun (a b c : Int) (a_1 : @LE.le Int Int.instLEInt b a) (a_2 : @LE.le Int Int.instLEInt c b) =>
      @Decidable.byContradiction (@LE.le Int Int.instLEInt c a) (c.decLe a)
        fun (a_3 : Not (@LE.le Int Int.instLEInt c a)) =>
        (fun (a b c : Int) (a_4 : @LE.le Int Int.instLEInt b a) (a_5 : @LE.le Int Int.instLEInt c b)
              (a_6 : Not (@LE.le Int Int.instLEInt c a)) =>
            @Lean.Omega.Constraint.not_sat'_of_isImpossible
              { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                upperBound :=
                  @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                Lean.Omega.Constraint }
              (@of_decide_eq_true
                (@Eq Bool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (instDecidableEqBool
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }.isImpossible
                  Bool.true)
                (@id
                  (@Eq Bool
                    (@Decidable.decide
                      (@Eq Bool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true)
                      (instDecidableEqBool
                        { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                            upperBound :=
                              @Option.some Int
                                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                            Lean.Omega.Constraint }.isImpossible
                        Bool.true))
                    Bool.true)
                  (@Eq.refl Bool Bool.true)))
              (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                  (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.nil Int))))
              (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
              (@Lean.Omega.Constraint.combine_sat'
                { lowerBound := @Option.none Int,
                  upperBound :=
                    @Option.some Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                  Lean.Omega.Constraint }
                { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                  upperBound := @Option.none Int : Lean.Omega.Constraint }
                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.nil Int))))
                (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                (@Lean.Omega.tidy_sat
                  { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                    upperBound := @Option.none Int : Lean.Omega.Constraint }
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (Lean.Omega.combo_sat'
                    { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))),
                      upperBound := @Option.none Int : Lean.Omega.Constraint }
                    { lowerBound := @Option.none Int,
                      upperBound :=
                        @Option.some Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) :
                      Lean.Omega.Constraint }
                    (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int)))
                    (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int))))
                    (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                    (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.nil Int)))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        Int.instLEInt (@Int.sub_nonneg_of_le a b a_4)
                        (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) a b)
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int)) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          (@Lean.Omega.Int.sub_congr a
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            b
                            ((Lean.Omega.LinearCombo.coordinate
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              a
                              (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                            (@Eq.symm Int
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int)))))
                          (@Eq.symm Int
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ({
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int)) :
                                    Lean.Omega.LinearCombo }.eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            (Lean.Omega.LinearCombo.sub_eval
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))
                    (@Lean.Omega.tidy_sat
                      { lowerBound := @Option.some Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))),
                        upperBound := @Option.none Int : Lean.Omega.Constraint }
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                      (@Lean.Omega.Constraint.addInequality_sat
                        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.cons Int
                          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int))))
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                        (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                          ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          Int.instLEInt
                          (@Int.sub_nonneg_of_le c
                            (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                              (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                            (@Int.add_one_le_of_lt a c (@Lean.Omega.Int.lt_of_not_le c a a_6)))
                          (@Eq.trans Int
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) c
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                            ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                  (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                  {
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int))) :
                                    Lean.Omega.LinearCombo }
                                  { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                    coeffs :=
                                      @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int) :
                                    Lean.Omega.LinearCombo }).eval
                              (Lean.Omega.Coeffs.ofList
                                (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                            (@Lean.Omega.Int.sub_congr c
                              ((Lean.Omega.LinearCombo.coordinate
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                              ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@Eq.symm Int
                                ((Lean.Omega.LinearCombo.coordinate
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int)))
                              (@Eq.trans Int
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) a
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                      (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                      {
                                        coeffs :=
                                          @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                            (@List.nil Int) :
                                        Lean.Omega.LinearCombo }
                                      { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }).eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                (@Lean.Omega.Int.add_congr a
                                  ((Lean.Omega.LinearCombo.coordinate
                                        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                  ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                        Lean.Omega.LinearCombo }.eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@Eq.symm Int
                                    ((Lean.Omega.LinearCombo.coordinate
                                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    a
                                    (@Lean.Omega.LinearCombo.coordinate_eval_0 a
                                      (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                                  (@id
                                    (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                            Lean.Omega.LinearCombo }.eval
                                        (Lean.Omega.Coeffs.ofList
                                          (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                    (@Eq.refl Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
                                (@Eq.symm Int
                                  ((@HAdd.hAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                        (@instHAdd Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instAdd)
                                        {
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }
                                        { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }).eval
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
                                    ({
                                          coeffs :=
                                            @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                    ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                          Lean.Omega.LinearCombo }.eval
                                      (Lean.Omega.Coeffs.ofList
                                        (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                                  (Lean.Omega.LinearCombo.add_eval
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)) :
                                      Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList
                                      (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))
                            (@Eq.symm Int
                              ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                                    (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                                    {
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }
                                    { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }).eval
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                              (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                ({
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                          (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                            (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                              (@List.nil Int))) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                                ({ const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                      coeffs :=
                                        @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int) :
                                      Lean.Omega.LinearCombo }.eval
                                  (Lean.Omega.Coeffs.ofList
                                    (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                              (Lean.Omega.LinearCombo.sub_eval
                                {
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                        (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                          (@List.nil Int))) :
                                  Lean.Omega.LinearCombo }
                                { const := @OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)),
                                  coeffs :=
                                    @List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int) :
                                  Lean.Omega.LinearCombo }
                                (Lean.Omega.Coeffs.ofList
                                  (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))))))))
                (@Lean.Omega.Constraint.addInequality_sat (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                      (@List.cons Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@List.nil Int))))
                  (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))
                  (@le_of_le_of_eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                    ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                          (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }).eval
                      (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                    Int.instLEInt (@Int.sub_nonneg_of_le b c a_5)
                    (@Eq.trans Int (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) b c)
                      (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                      ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                            (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                              Lean.Omega.LinearCombo }
                            {
                              coeffs :=
                                @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int))) :
                              Lean.Omega.LinearCombo }).eval
                        (Lean.Omega.Coeffs.ofList (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                      (@Lean.Omega.Int.sub_congr b
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        c
                        ((Lean.Omega.LinearCombo.coordinate (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          b (@Lean.Omega.LinearCombo.coordinate_eval_1 a b (@List.cons Int c (@List.nil Int))))
                        (@Eq.symm Int
                          ((Lean.Omega.LinearCombo.coordinate
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          c (@Lean.Omega.LinearCombo.coordinate_eval_2 a b c (@List.nil Int))))
                      (@Eq.symm Int
                        ((@HSub.hSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo Lean.Omega.LinearCombo
                              (@instHSub Lean.Omega.LinearCombo Lean.Omega.LinearCombo.instSub)
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }
                              {
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }).eval
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                      (@List.nil Int)) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))
                          ({
                                coeffs :=
                                  @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                    (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                      (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                        (@List.nil Int))) :
                                Lean.Omega.LinearCombo }.eval
                            (Lean.Omega.Coeffs.ofList
                              (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int)))))))
                        (Lean.Omega.LinearCombo.sub_eval
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@List.nil Int)) :
                            Lean.Omega.LinearCombo }
                          {
                            coeffs :=
                              @List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                (@List.cons Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                                  (@List.cons Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                                    (@List.nil Int))) :
                            Lean.Omega.LinearCombo }
                          (Lean.Omega.Coeffs.ofList
                            (@List.cons Int a (@List.cons Int b (@List.cons Int c (@List.nil Int))))))))))))
          a b c a_1 a_2 a_3) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   decide) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Lean.Grind.OrderedRing.natCast_nonneg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.natCast_nonneg.h5 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst : LE R] [inst_1 : LT R] [inst_2 : Std.LawfulOrderLT R] {a : Nat},
        Std.IsPreorder R := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega))) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedRing.natCast_nonneg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.natCast_nonneg.h6 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1] {a : Nat},
        @LE.le R inst_1
          (@OfNat.ofNat R (nat_lit 0)
            (@Zero.toOfNat0 R
              (@Lean.Grind.AddCommMonoid.toZero R
                (@Lean.Grind.NatModule.toAddCommMonoid R
                  (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
          (@Nat.cast R (@Lean.Grind.Semiring.natCast R (@Lean.Grind.Ring.toSemiring R inst)) a)) := fun hc_h => absurd (@hc_h (Int : Type) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (⟨fun a b => b ≤ a⟩ : LE Int) (⟨fun a b => b < a⟩ : LT Int) (@Std.LawfulOrderLT.mk (Int) (@LT.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt b a) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (by (try dsimp only);   (intros; omega))) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Lean.Grind.Field.IsOrdered.inv_nonpos_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.inv_nonpos_iff.h5 : ¬∀ {R : Type} [inst : Lean.Grind.Field R] [inst : LE R] [inst_1 : LT R] [inst_2 : Std.LawfulOrderLT R] {a : R},
        Std.IsLinearOrder R := fun hc_h => absurd (@hc_h (Rat : Type) (Lean.Grind.instFieldRat) (⟨fun a b => a < b⟩ : LE Rat) (Rat.instLT) (@Std.LawfulOrderLT.mk (Rat) (Rat.instLT) (@LE.mk Rat fun (a b : Rat) => @LT.lt Rat Rat.instLT a b) (by (try dsimp only);   grind)) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPartialOrder.toIsPreorder.le_refl (0 : Rat))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.IntModule.OfNatModule.mk_le_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.IntModule.OfNatModule.mk_le_mk.h3 : ¬∀ {α : Type} [inst : Lean.Grind.NatModule α] [inst : LE α] {a₁ a₂ b₁ b₂ : α}, Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.Semiring.toNatModule) (⟨fun _ _ => False⟩ : LE Int) (0) (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.IntModule.OfNatModule.mk_le_mk, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.IntModule.OfNatModule.mk_le_mk.h4 : ¬∀ {α : Type} [inst : Lean.Grind.NatModule α] [inst_1 : LE α] [inst_2 : Std.IsPreorder α] {a₁ a₂ b₁ b₂ : α},
        Lean.Grind.OrderedAdd α := fun hc_h => absurd (@hc_h (Nat) (Lean.Grind.Semiring.toNatModule) (⟨fun a b => a % 2 ≤ b % 2⟩ : LE Nat) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (0) (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.add_le_left_iff (a := (0 : Nat)) (b := (1 : Nat)) (1 : Nat))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedRing.neg_one_lt_zero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.neg_one_lt_zero.h5 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst : LE R] [inst_1 : LT R] [inst_2 : Std.LawfulOrderLT R], Std.IsPreorder R := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega)))) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedRing.not_one_lt_zero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.not_one_lt_zero.h5 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst : LE R] [inst_1 : LT R] [inst_2 : Std.LawfulOrderLT R], Std.IsPreorder R := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toRing) (⟨fun a b => a < b⟩ : LE Int) (Int.instLTInt) (@Std.LawfulOrderLT.mk (Int) (Int.instLTInt) (@LE.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt a b) (by (try dsimp only);   (intros; omega)))) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.OrderedRing.not_one_lt_zero, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.not_one_lt_zero.h6 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1],
        Not
          (@LT.lt R inst_2
            (@OfNat.ofNat R (nat_lit 1) (@Lean.Grind.Semiring.ofNat R (@Lean.Grind.Ring.toSemiring R inst) (nat_lit 1)))
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst)))))))) := fun hc_h => absurd (@hc_h (Int : Type) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (⟨fun a b => b ≤ a⟩ : LE Int) (⟨fun a b => b < a⟩ : LT Int) (@Std.LawfulOrderLT.mk (Int) (@LT.mk Int fun (a b : Int) => @LT.lt Int Int.instLTInt b a) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (by (try dsimp only);   (intros; omega))) (@Std.IsPreorder.mk (Int) (@LE.mk Int fun (a b : Int) => @LE.le Int Int.instLEInt b a) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega)))) (by
  decide +kernel)

-- Lean.Grind.OrderedAdd.add_le_right_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_right_iff.h2 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Lean.Grind.AddCommMonoid M] {a b : M} (c : M), Std.IsPreorder M := fun hc_h => absurd (@hc_h (Int : Type) (⟨fun _ _ => False⟩ : LE Int) (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.ExistsAddOfLT.exists_add_of_le, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.ExistsAddOfLT.exists_add_of_le.h4.inst : ¬∃ (c : Nat), 0 ≠ c ∧ 0 = 1 + c := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.ExistsAddOfLT.exists_add_of_le.h4.prem0 : 1 ≠ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.ExistsAddOfLT.exists_add_of_le.h4 : ¬∀ {α : Type} {inst : LT α} {inst_1 : Zero α} {inst_2 : Add α} {a b : α}, a < b → ∃ (c : α), 0 < c ∧ b = a + c := fun hc_h => HypCheckProof.Lean.Grind.ExistsAddOfLT.exists_add_of_le.h4.inst (@hc_h (Nat) ({ lt := fun (a b : Nat) => a ≠ b : LT Nat }) (Zero.ofOfNat0) (instAddNat) (1) (0) HypCheckProof.Lean.Grind.ExistsAddOfLT.exists_add_of_le.h4.prem0)

-- Lean.Grind.IntModule.OfNatModule.toQ_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.IntModule.OfNatModule.toQ_le.h3 : ¬∀ {α : Type} [inst : Lean.Grind.NatModule α] [inst : LE α] {a b : α}, Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.Semiring.toNatModule) (⟨fun _ _ => False⟩ : LE Int) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.IntModule.OfNatModule.toQ_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.IntModule.OfNatModule.toQ_le.h4 : ¬∀ {α : Type} [inst : Lean.Grind.NatModule α] [inst_1 : LE α] [inst_2 : Std.IsPreorder α] {a b : α},
        Lean.Grind.OrderedAdd α := fun hc_h => absurd (@hc_h (Nat) (Lean.Grind.Semiring.toNatModule) (⟨fun a b => a % 2 ≤ b % 2⟩ : LE Nat) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.add_le_left_iff (a := (0 : Nat)) (b := (1 : Nat)) (1 : Nat))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.IsCharP.natCast_eq_zero_iff_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.IsCharP.natCast_eq_zero_iff_of_lt.h3 : Not
      (∀ {α : Type} (p : Nat) [inst : Lean.Grind.Semiring α] {x : Nat},
        @LT.lt Nat instLTNat x p →
          Iff
            (@Eq α (@Nat.cast α (@Lean.Grind.Semiring.natCast α inst) x)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.Semiring.toNatModule α inst))))))
            (@Eq Nat x (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := fun hc_h => absurd (@hc_h (Fin 2 : Type) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Lean.Grind.CommSemiring.toSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Lean.Grind.CommRing.toCommSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Lean.Grind.Fin.instCommRingFinOfNeZeroNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.OrderedRing.zero_lt_one, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedRing.zero_lt_one.h5 : Not
      (∀ {R : Type} {inst : Lean.Grind.Semiring R} {inst_1 : LE R} {inst_2 : LT R} {inst_3 : @Std.IsPreorder R inst_1},
        @LT.lt R inst_2
          (@OfNat.ofNat R (nat_lit 0)
            (@Zero.toOfNat0 R
              (@Lean.Grind.AddCommMonoid.toZero R
                (@Lean.Grind.NatModule.toAddCommMonoid R (@Lean.Grind.Semiring.toNatModule R inst)))))
          (@OfNat.ofNat R (nat_lit 1) (@Lean.Grind.Semiring.ofNat R inst (nat_lit 1)))) := fun hc_h => absurd (@hc_h (Nat) (@Lean.Grind.CommSemiring.toSemiring Nat Lean.Grind.instCommSemiringNat) (instLENat) (⟨fun a b => b < a⟩ : LT Nat) ((@Std.IsPreorder.mk (Nat) (instLENat) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))))) (by
  decide +kernel)

-- Lean.Grind.CommRing.inv_int_eqC, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.inv_int_eqC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Field α] (b : Int),
        @Eq Bool
            (@bne Int (@instBEqOfDecidableEq Int Int.instDecidableEq)
              (@HMod.hMod Int Int Int (@instHMod Int Int.instMod) b (@Nat.cast Int instNatCastInt c))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
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
                (nat_lit 1)))) := fun hc_h => absurd (@hc_h (Fin 2 : Type) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ({ (inferInstance : Lean.Grind.CommRing (Fin 2)) with inv := id, div := (· * ·), zpow := ⟨fun a n => a ^ n.natAbs⟩, div_eq_mul_inv := (by decide), zero_ne_one := (by decide), inv_zero := (by decide), mul_inv_cancel := (by decide), zpow_zero := fun a => Lean.Grind.Semiring.pow_zero a, zpow_succ := fun a n => Lean.Grind.Semiring.pow_succ a n, zpow_neg := (by intro a n; show a ^ (-n).natAbs = a ^ n.natAbs; rw [Int.natAbs_neg]) } : Lean.Grind.Field (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.OrderedAdd.neg_nonneg_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.neg_nonneg_iff.h2 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Lean.Grind.AddCommGroup M] {a : M}, Std.IsPreorder M := fun hc_h => absurd (@hc_h (Int : Type) (⟨fun _ _ => False⟩ : LE Int) (Lean.Grind.Ring.toAddCommGroup) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.Field.natCast_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Field.natCast_ne_zero.h2 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] {n : Nat},
        @Ne Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @Ne α
            (@Nat.cast α
              (@Lean.Grind.Semiring.natCast α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
              n)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α
                        (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))))))) := fun hc_h => absurd (@hc_h (Fin 2 : Type) ({ (inferInstance : Lean.Grind.CommRing (Fin 2)) with inv := id, div := (· * ·), zpow := ⟨fun a n => a ^ n.natAbs⟩, div_eq_mul_inv := (by decide), zero_ne_one := (by decide), inv_zero := (by decide), mul_inv_cancel := (by decide), zpow_zero := fun a => Lean.Grind.Semiring.pow_zero a, zpow_succ := fun a n => Lean.Grind.Semiring.pow_succ a n, zpow_neg := (by intro a n; show a ^ (-n).natAbs = a ^ n.natAbs; rw [Int.natAbs_neg]) } : Lean.Grind.Field (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.Ring.OfSemiring.instOrderedAddQ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Ring.OfSemiring.instOrderedAddQ.h3 : ¬∀ {α : Type} [inst : Lean.Grind.Semiring α] [inst : LE α], Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring.toSemiring) (⟨fun _ _ => False⟩ : LE Int)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.Ring.OfSemiring.instOrderedAddQ, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Ring.OfSemiring.instOrderedAddQ.h4 : ¬∀ {α : Type} [inst : Lean.Grind.Semiring α] [inst_1 : LE α] [inst_2 : Std.IsPreorder α], Lean.Grind.OrderedAdd α := fun hc_h => absurd (@hc_h (Nat) (Lean.Grind.instCommSemiringNat.toSemiring) (⟨fun a b => a % 2 ≤ b % 2⟩ : LE Nat) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega)))) (by
  exact fun hc_c =>
    absurd (hc_c.add_le_left_iff (a := (0 : Nat)) (b := (1 : Nat)) (1 : Nat))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.Ring.OfSemiring.instIsPreorderQ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Ring.OfSemiring.instIsPreorderQ.h3 : ¬∀ {α : Type} [inst : Lean.Grind.Semiring α] [inst : LE α], Std.IsPreorder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.instCommRingInt.toCommSemiring.toSemiring) (⟨fun _ _ => False⟩ : LE Int)) (by
  exact fun hc_c =>
    absurd (hc_c.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.Ring.OfSemiring.instIsPreorderQ, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Ring.OfSemiring.instIsPreorderQ.h4 : ¬∀ {α : Type} [inst : Lean.Grind.Semiring α] [inst_1 : LE α] [inst_2 : Std.IsPreorder α], Lean.Grind.OrderedAdd α := fun hc_h => absurd (@hc_h (Nat) (Lean.Grind.instCommSemiringNat.toSemiring) (⟨fun a b => a % 2 ≤ b % 2⟩ : LE Nat) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega)))) (by
  exact fun hc_c =>
    absurd (hc_c.add_le_left_iff (a := (0 : Nat)) (b := (1 : Nat)) (1 : Nat))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.CommRing.inv_int_eq', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.inv_int_eq'.h2 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (b : Int),
        @Eq Bool
            (@bne Int (@instBEqOfDecidableEq Int Int.instDecidableEq) b
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
          @Eq α
            (@HMul.hMul α α α
              (@instHMul α
                (@Lean.Grind.Semiring.toMul α
                  (@Lean.Grind.CommSemiring.toSemiring α
                    (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
              (@IntCast.intCast α
                (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))) b)
              (@Inv.inv α (@Lean.Grind.Field.toInv α inst)
                (@Lean.Grind.CommRing.denoteInt α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) b)))
            (@OfNat.ofNat α (nat_lit 1)
              (@Lean.Grind.Semiring.ofNat α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
                (nat_lit 1)))) := fun hc_h => absurd (@hc_h (Fin 2 : Type) ({ (inferInstance : Lean.Grind.CommRing (Fin 2)) with inv := id, div := (· * ·), zpow := ⟨fun a n => a ^ n.natAbs⟩, div_eq_mul_inv := (by decide), zero_ne_one := (by decide), inv_zero := (by decide), mul_inv_cancel := (by decide), zpow_zero := fun a => Lean.Grind.Semiring.pow_zero a, zpow_succ := fun a n => Lean.Grind.Semiring.pow_succ a n, zpow_neg := (by intro a n; show a ^ (-n).natAbs = a ^ n.natAbs; rw [Int.natAbs_neg]) } : Lean.Grind.Field (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.CommRing.inv_int_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.CommRing.inv_int_eq.h2 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (b : Int),
        @Eq Bool
            (@bne Int (@instBEqOfDecidableEq Int Int.instDecidableEq) b
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
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
                (nat_lit 1)))) := fun hc_h => absurd (@hc_h (Fin 2 : Type) ({ (inferInstance : Lean.Grind.CommRing (Fin 2)) with inv := id, div := (· * ·), zpow := ⟨fun a n => a ^ n.natAbs⟩, div_eq_mul_inv := (by decide), zero_ne_one := (by decide), inv_zero := (by decide), mul_inv_cancel := (by decide), zpow_zero := fun a => Lean.Grind.Semiring.pow_zero a, zpow_succ := fun a n => Lean.Grind.Semiring.pow_succ a n, zpow_neg := (by intro a n; show a ^ (-n).natAbs = a ^ n.natAbs; rw [Int.natAbs_neg]) } : Lean.Grind.Field (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Lean.Grind.IntModule.OfNatModule.instIsPartialOrderQ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.IntModule.OfNatModule.instIsPartialOrderQ.h3 : ¬∀ {α : Type} [inst : Lean.Grind.NatModule α] [inst : LE α], Std.IsPartialOrder α := fun hc_h => absurd (@hc_h (Int : Type) (Lean.Grind.Semiring.toNatModule) (⟨fun _ _ => False⟩ : LE Int)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPreorder.le_refl (0 : Int))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.IntModule.OfNatModule.instIsPartialOrderQ, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.IntModule.OfNatModule.instIsPartialOrderQ.h4 : ¬∀ {α : Type} [inst : Lean.Grind.NatModule α] [inst_1 : LE α] [inst_2 : Std.IsPartialOrder α], Lean.Grind.OrderedAdd α := fun hc_h => absurd (@hc_h (Fin 2 : Type) (Lean.Grind.Semiring.toNatModule) (instLEFin) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.add_le_left_iff (a := ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2) : Fin 2)) (b :=
        ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2) : Fin 2))
        ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2) : Fin 2))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Lean.Grind.Field.NormNum.ofRat_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.ofRat_mul.h2 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (a b : Rat),
        @Eq α (@Lean.Grind.Field.NormNum.ofRat α inst (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) a b))
          (@HMul.hMul α α α
            (@instHMul α
              (@Lean.Grind.Semiring.toMul α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
            (@Lean.Grind.Field.NormNum.ofRat α inst a) (@Lean.Grind.Field.NormNum.ofRat α inst b))) := fun hc_h => absurd (@hc_h (Fin 2 : Type) ({ (inferInstance : Lean.Grind.CommRing (Fin 2)) with inv := id, div := (· * ·), zpow := ⟨fun a n => a ^ n.natAbs⟩, div_eq_mul_inv := (by decide), zero_ne_one := (by decide), inv_zero := (by decide), mul_inv_cancel := (by decide), zpow_zero := fun a => Lean.Grind.Semiring.pow_zero a, zpow_succ := fun a n => Lean.Grind.Semiring.pow_succ a n, zpow_neg := (by intro a n; show a ^ (-n).natAbs = a ^ n.natAbs; rw [Int.natAbs_neg]) } : Lean.Grind.Field (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
      (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))) (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))) (by
  decide +kernel)

-- Lean.Grind.Field.NormNum.ofRat_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.ofRat_add.h2 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] (a b : Rat),
        @Eq α (@Lean.Grind.Field.NormNum.ofRat α inst (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) a b))
          (@HAdd.hAdd α α α
            (@instHAdd α
              (@Lean.Grind.Semiring.toAdd α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))
            (@Lean.Grind.Field.NormNum.ofRat α inst a) (@Lean.Grind.Field.NormNum.ofRat α inst b))) := fun hc_h => absurd (@hc_h (Fin 2 : Type) ({ (inferInstance : Lean.Grind.CommRing (Fin 2)) with inv := id, div := (· * ·), zpow := ⟨fun a n => a ^ n.natAbs⟩, div_eq_mul_inv := (by decide), zero_ne_one := (by decide), inv_zero := (by decide), mul_inv_cancel := (by decide), zpow_zero := fun a => Lean.Grind.Semiring.pow_zero a, zpow_succ := fun a n => Lean.Grind.Semiring.pow_succ a n, zpow_neg := (by intro a n; show a ^ (-n).natAbs = a ^ n.natAbs; rw [Int.natAbs_neg]) } : Lean.Grind.Field (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
      (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))))) (by
  decide +kernel)

