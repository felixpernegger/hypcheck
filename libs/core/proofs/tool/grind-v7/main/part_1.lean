import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.Order.le_trans_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h6.inst : Not
      (@LE.le UInt8 instLEUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HAdd.hAdd UInt8 UInt8 UInt8
          (@instHAdd UInt8
            (@Lean.Grind.Semiring.toAdd UInt8
              (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
          (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h6.prem0 : @LE.le UInt8 instLEUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h6.prem1 : @LE.le UInt8 instLEUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h6.prem2 : @Eq Bool
      (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α] {a b c : α} {k₁ k₂ : Int} (k : Int),
        @LE.le α inst a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @LE.le α inst b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)) →
            @Eq Bool
                (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k
                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁))
                Bool.true →
              @LE.le α inst a
                (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                  (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_trans_k.h6.inst (@hc_h (UInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_trans_k.h6.prem0 HypCheckProof.Lean.Grind.Order.le_trans_k.h6.prem1 HypCheckProof.Lean.Grind.Order.le_trans_k.h6.prem2)

-- Lean.Grind.Order.le_trans_k, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h13.inst : Not
      (@LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h13.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h13.prem1 : @Eq Bool
      (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h13 : Not
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
            @LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_trans_k.h13.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_trans_k.h13.prem0 HypCheckProof.Lean.Grind.Order.le_trans_k.h13.prem1)

-- Lean.Grind.Order.le_trans_k, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h14.inst : Not
      (@LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h14.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h14.prem1 : @Eq Bool
      (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h14 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b c : α}
        {k₁ k₂ : Int} (k : Int),
        @LE.le α inst a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @Eq Bool
              (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k
                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁))
              Bool.true →
            @LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_trans_k.h14.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_trans_k.h14.prem0 HypCheckProof.Lean.Grind.Order.le_trans_k.h14.prem1)

-- Lean.Grind.Order.le_trans_k, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h15.inst : Not
      (@LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h15.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h15.prem1 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_trans_k.h15 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b c : α}
        {k₁ k₂ : Int} (k : Int),
        @LE.le α inst a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @LE.le α inst b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)) →
            @LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_trans_k.h15.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.Order.le_trans_k.h15.prem0 HypCheckProof.Lean.Grind.Order.le_trans_k.h15.prem1)

-- Lean.Grind.Order.le_lt_trans_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h6.inst : Not
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
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h6.prem0 : @LE.le UInt8 instLEUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h6.prem1 : @LT.lt UInt8 instLTUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h6.prem2 : @Eq Bool
      (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α] {a b c : α} {k₁ k₂ : Int} (k : Int),
        @LE.le α inst a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @LT.lt α inst_1 b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)) →
            @Eq Bool
                (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k
                  (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁))
                Bool.true →
              @LT.lt α inst_1 a
                (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                  (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h6.inst (@hc_h (UInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h6.prem0 HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h6.prem1 HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h6.prem2)

-- Lean.Grind.Order.le_lt_trans_k, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h13.inst : Not
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
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h13.prem0 : @LT.lt Int Int.instLTInt (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h13.prem1 : @Eq Bool
      (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h13 : Not
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
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h13.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h13.prem0 HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h13.prem1)

-- Lean.Grind.Order.le_lt_trans_k, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h14.inst : Not
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
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h14.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h14.prem1 : @Eq Bool
      (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h14 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b c : α}
        {k₁ k₂ : Int} (k : Int),
        @LE.le α inst a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @Eq Bool
              (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq) k
                (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) k₂ k₁))
              Bool.true →
            @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h14.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h14.prem0 HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h14.prem1)

-- Lean.Grind.Order.le_lt_trans_k, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h15.inst : Not
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
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h15.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h15.prem1 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h15 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b c : α}
        {k₁ k₂ : Int} (k : Int),
        @LE.le α inst a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @LT.lt α inst_1 b
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)) →
            @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) c
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k))) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h15.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h15.prem0 HypCheckProof.Lean.Grind.Order.le_lt_trans_k.h15.prem1)

-- Lean.Grind.CommRing.sub_eq_of_toExprC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h3.inst : Not
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
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h3.prem0 : @Eq Lean.Grind.CommRing.Poly
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
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (a b a' b' : Lean.Grind.CommRing.Expr) (p pa pb : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal (a.sub b) c) →
          @Eq Lean.Grind.CommRing.Expr a' pa.toExpr_k →
            @Eq Lean.Grind.CommRing.Expr b' pb.toExpr_k →
              @Eq Lean.Grind.CommRing.Poly p
                  (pa.combineC_k c
                    (Lean.Grind.CommRing.Poly.mulConstC_k
                      (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) pb c)) →
                @Eq α
                  (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                    (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                    (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
                  (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                    (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a')
                    (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl rfl HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h3.prem0)

-- Lean.Grind.CommRing.sub_eq_of_toExprC, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h13.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h13 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (a b a' b' : Lean.Grind.CommRing.Expr)
        (p pa pb : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Expr a' pa.toExpr_k →
          @Eq Lean.Grind.CommRing.Expr b' pb.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (pa.combineC_k c
                  (Lean.Grind.CommRing.Poly.mulConstC_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) pb c)) →
              @Eq α
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h13.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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

-- Lean.Grind.CommRing.sub_eq_of_toExprC, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h14.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h14.prem0 : @Eq Lean.Grind.CommRing.Poly
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
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h14 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (a b a' b' : Lean.Grind.CommRing.Expr)
        (p pa pb : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal (a.sub b) c) →
          @Eq Lean.Grind.CommRing.Expr b' pb.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (pa.combineC_k c
                  (Lean.Grind.CommRing.Poly.mulConstC_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) pb c)) →
              @Eq α
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h14.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h14.prem0)

-- Lean.Grind.CommRing.sub_eq_of_toExprC, hypothesis 15: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h15.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h15.prem0 : @Eq Lean.Grind.CommRing.Poly
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
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h15 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (a b a' b' : Lean.Grind.CommRing.Expr)
        (p pa pb : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal (a.sub b) c) →
          @Eq Lean.Grind.CommRing.Expr a' pa.toExpr_k →
            @Eq Lean.Grind.CommRing.Poly p
                (pa.combineC_k c
                  (Lean.Grind.CommRing.Poly.mulConstC_k
                    (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) pb c)) →
              @Eq α
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h15.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl rfl HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h15.prem0)

-- Lean.Grind.CommRing.sub_eq_of_toExprC, hypothesis 16: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h16.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h16 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (a b a' b' : Lean.Grind.CommRing.Expr)
        (p pa pb : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal (a.sub b) c) →
          @Eq Lean.Grind.CommRing.Expr a' pa.toExpr_k →
            @Eq Lean.Grind.CommRing.Expr b' pb.toExpr_k →
              @Eq α
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
                (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a')
                  (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.sub_eq_of_toExprC.h16.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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

-- Lean.Grind.CommRing.lt_norm_poly0, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly0.h6.inst : Not
      (@Eq Prop
        (@LT.lt UInt8 instLTUInt8
          (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
            (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
            (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var
                (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).neg))
        (@LT.lt UInt8 instLTUInt8
          (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
            (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)
            (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly0.h6.prem0 : @Eq Lean.Grind.CommRing.Expr
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
            (Lean.Grind.CommRing.Expr.var
                (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).neg)).toExpr_k := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly0.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (lhs.sub rhs)) →
          @Eq Lean.Grind.CommRing.Expr lhs' p.toExpr_k →
            @Eq Prop
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
              (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
                  (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm_poly0.h6.inst (@hc_h (UInt8) (Lean.Grind.instCommRingUInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).neg) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).neg)) rfl HypCheckProof.Lean.Grind.CommRing.lt_norm_poly0.h6.prem0)

-- Lean.Grind.CommRing.lt_norm_poly0, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly0.h13.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k)
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly0.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Expr lhs' p.toExpr_k →
          @Eq Prop
            (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
                (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm_poly0.h13.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) rfl)

-- Lean.Grind.CommRing.lt_norm_poly0, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly0.h14.inst : Not
      (@Eq Prop
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        (@LT.lt Int Int.instLTInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.lt_norm_poly0.h14 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs lhs' : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyX_k bal (lhs.sub rhs)) →
          @Eq Prop
            (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            (@LT.lt α inst_2 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs')
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
                (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.lt_norm_poly0.h14.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyX_k Bool.false
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) rfl)

-- Lean.Grind.Linarith.le_lt_combine, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h11.prem0 : @LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h11.prem1 : @LT.lt Int Int.instLTInt
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
theorem HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 inst_4]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
        @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
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
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h11.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h11.prem0 HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h11.prem1)

-- Lean.Grind.Linarith.le_lt_combine, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h12.prem0 : @Eq Bool
      (Lean.Grind.Linarith.le_lt_combine_cert
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)
        Lean.Grind.Linarith.Poly.nil)
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h12.prem1 : @LT.lt Int Int.instLTInt
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
theorem HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 inst_4]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.le_lt_combine_cert p₁ p₂ p₃) Bool.true →
          @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₃)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h12.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h12.prem0 HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h12.prem1)

-- Lean.Grind.Linarith.le_lt_combine, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h13.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h13.prem0 : @Eq Bool
      (Lean.Grind.Linarith.le_lt_combine_cert Lean.Grind.Linarith.Poly.nil Lean.Grind.Linarith.Poly.nil
        Lean.Grind.Linarith.Poly.nil)
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h13.prem1 : @LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedAdd α
            (@instHAdd α
              (@Lean.Grind.AddCommMonoid.toAdd α
                (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))
            inst_1 inst_4]
        (ctx : Lean.Grind.Linarith.Context α) (p₁ p₂ p₃ : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.le_lt_combine_cert p₁ p₂ p₃) Bool.true →
          @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst))))) →
            @LT.lt α inst_2 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p₃)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h13.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h13.prem0 HypCheckProof.Lean.Grind.Linarith.le_lt_combine.h13.prem1)

-- Lean.Grind.CommRing.Stepwise.simpC, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h12.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h12.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h12 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k₁ : Int) (p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int)
        (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h12.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@List.nil Nat) HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h12.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h12.prem1)

-- Lean.Grind.CommRing.Stepwise.simpC, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h13.inst : Not
      (@Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h13.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h13 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k₁ : Int) (p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int)
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
            @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h13.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h13.prem0)

-- Lean.Grind.CommRing.Stepwise.simpC, hypothesis 14: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h14.inst : Not
      (@Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h14.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h14 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (k₁ : Int) (p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int)
        (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHintC c hs (Lean.Grind.CommRing.Poly.mulConstC_k k₁ p₁ c)
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h14.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.simpC.h14.prem0)

-- Lean.Grind.CommRing.eq_true_of_kronQLin, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h11.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h11.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h11.prem2 : @Eq Bool
      (Lean.Grind.CommRing.Expr.linQOk_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h11.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQLinEq_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h11 : Not
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
                  @Eq Prop
                    (@Eq α
                      (@Lean.Grind.CommRing.Expr.denote α
                        (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx a)
                      (@Lean.Grind.CommRing.Expr.denote α
                        (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx b))
                    True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h11.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h11.prem0 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h11.prem1 (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h11.prem2 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h11.prem3)

-- Lean.Grind.CommRing.eq_true_of_kronQLin, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h12.prem0 : @Lean.Grind.CommRing.InvVars.ok Rat Lean.Grind.instFieldRat
      (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) := by
  rfl
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h12.prem1 : @Eq Bool (Lean.Grind.CommRing.InvVars.nonzero_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))) Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h12.prem2 : @Eq Bool
      (Lean.Grind.CommRing.Expr.linQOk_k (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h12.prem3 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronQOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@List.nil (Prod Lean.Grind.CommRing.Var Nat))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h12 : Not
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
                  @Eq Prop
                    (@Eq α
                      (@Lean.Grind.CommRing.Expr.denote α
                        (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx a)
                      (@Lean.Grind.CommRing.Expr.denote α
                        (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) ctx b))
                    True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h12.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.RArray.leaf Rat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.nil (Prod Lean.Grind.CommRing.Var Nat)) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h12.prem0 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h12.prem1 (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h12.prem2 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronQLin.h12.prem3)

-- Lean.Grind.CommRing.le_true_of_kronS, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronS.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronS.h11.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronS.h11.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronS.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        [inst_2 : LE α] [inst_3 : @Std.IsPreorder α inst_2] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronEval_k K B a) (Lean.Grind.CommRing.Expr.kronEval_k K B b) →
            @Eq Prop
              (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_kronS.h11.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_true_of_kronS.h11.prem0 HypCheckProof.Lean.Grind.CommRing.le_true_of_kronS.h11.prem1)

-- Lean.Grind.CommRing.le_true_of_kronS, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronS.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronS.h12.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronS.h12.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_kronS.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        [inst_2 : LE α] [inst_3 : @Std.IsPreorder α inst_2] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Prop
              (@LE.le α inst_2 (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_kronS.h12.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.le_true_of_kronS.h12.prem0 HypCheckProof.Lean.Grind.CommRing.le_true_of_kronS.h12.prem1)

-- Lean.Grind.Order.lt_eq_true_of_lt_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h6.inst : Not
      (@Eq Prop
        (@LT.lt UInt8 instLTUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
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
theorem HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h6.prem0 : @Eq Bool
      ((@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).ble'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h6.prem1 : @LT.lt UInt8 instLTUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst : @Std.IsPreorder α inst] [inst : Lean.Grind.Ring α] {a b : α} {k₁ k₂ : Int},
        @Eq Bool (k₁.ble' k₂) Bool.true →
          @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst) k₁)) →
            @Eq Prop
              (@LT.lt α inst_1 a
                (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst))) b
                  (@Int.cast α (@Lean.Grind.Ring.intCast α inst) k₂)))
              True) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h6.inst (@hc_h (UInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h6.prem0 HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h6.prem1)

-- Lean.Grind.Order.lt_eq_true_of_lt_k, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h11.inst : Not
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
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h11.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h11 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b : α}
        {k₁ k₂ : Int},
        @LT.lt α inst_1 a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₁)) →
          @Eq Prop
            (@LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
            True) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h11.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h11.prem0)

-- Lean.Grind.Order.lt_eq_true_of_lt_k, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h12.inst : Not
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
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h12.prem0 : @Eq Bool
      (Int.ble' (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h12 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a b : α}
        {k₁ k₂ : Int},
        @Eq Bool (k₁.ble' k₂) Bool.true →
          @Eq Prop
            (@LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) b
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k₂)))
            True) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h12.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.lt_eq_true_of_lt_k.h12.prem0)

-- Lean.Grind.Linarith.not_lt_norm, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h6.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h6.prem0 : @Eq Bool
      (Lean.Grind.Linarith.norm_cert Lean.Grind.Linarith.Expr.zero
        (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h6.prem1 : Not
      (@LT.lt UInt8 instLTUInt8
        (@Lean.Grind.Linarith.Expr.denote_k UInt8
          (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
          (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Lean.Grind.Linarith.Expr.denote_k UInt8
          (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1))))
          Lean.Grind.Linarith.Expr.zero)) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsLinearOrder α inst_1]
        (ctx : Lean.Grind.Linarith.Context α) (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.norm_cert rhs lhs p) Bool.true →
          Not
              (@LT.lt α inst_2 (@Lean.Grind.Linarith.Expr.denote_k α inst ctx lhs)
                (@Lean.Grind.Linarith.Expr.denote_k α inst ctx rhs)) →
            @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h6.inst (@hc_h (UInt8) (@Lean.Grind.Ring.toIntModule UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8)) (instLEUInt8) (instLTUInt8) _ _ (@Lean.RArray.leaf UInt8 (@OfNat.ofNat UInt8 (nat_lit 1) (@UInt8.instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Poly.add (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h6.prem0 HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h6.prem1)

-- Lean.Grind.Linarith.not_lt_norm, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h11.prem0 : Not
      (@LT.lt Int Int.instLTInt
        (@Lean.Grind.Linarith.Expr.denote_k Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Expr.zero)
        (@Lean.Grind.Linarith.Expr.denote_k Int
          (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Expr.zero)) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h11 : Not
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
            (@LT.lt α inst_2 (@Lean.Grind.Linarith.Expr.denote_k α inst ctx lhs)
              (@Lean.Grind.Linarith.Expr.denote_k α inst ctx rhs)) →
          @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h11.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h11.prem0)

-- Lean.Grind.Linarith.not_lt_norm, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h12.prem0 : @Eq Bool
      (Lean.Grind.Linarith.norm_cert
        (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        Lean.Grind.Linarith.Expr.zero
        (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h12 : Not
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
          @LE.le α inst_1 (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h12.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.not_lt_norm.h12.prem0)

-- Lean.Grind.CommRing.Stepwise.simp1C, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h11.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h11.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h11 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon)
        (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h11.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@List.nil Nat) HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h11.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h11.prem1)

-- Lean.Grind.CommRing.Stepwise.simp1C, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h12.inst : Not
      (@Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h12.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h12 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon)
        (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHintC c hs p₁ (Lean.Grind.CommRing.Poly.mulMonC_k k₂ m₂ p₂ c)) →
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h12.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h12.prem0)

-- Lean.Grind.CommRing.Stepwise.simp1C, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h13.inst : Not
      (@Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h13.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h13 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon)
        (p₂ p : Lean.Grind.CommRing.Poly) (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHintC c hs p₁ (Lean.Grind.CommRing.Poly.mulMonC_k k₂ m₂ p₂ c)) →
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h13.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.simp1C.h13.prem0)

-- Lean.Grind.CommRing.le_true_of_toPPX_eq, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eq.h11.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.branch Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.branch Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eq.h11.prem0 : @Eq Lean.Grind.CommRing.PPoly
      (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Bool.false
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Bool.false
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eq.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.PPoly),
        @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a) →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b) →
            @Eq Prop
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eq.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) _ (@Lean.RArray.branch Int (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Bool.false
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1))))) rfl HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eq.h11.prem0)

-- Lean.Grind.CommRing.le_true_of_toPPX_eq, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eq.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eq.h12.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eq.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.PPoly),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₂ b) →
            @Eq Prop
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eq.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eq.h12.prem0 rfl)

-- Lean.Grind.CommRing.le_true_of_toPPX_eq, hypothesis 13: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eq.h13.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eq.h13.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eq.h13 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : @Std.IsPreorder α inst_1]
        (ctx : Lean.Grind.CommRing.Context α) (B : Nat) (bal₁ bal₂ : Bool) (a b : Lean.Grind.CommRing.Expr)
        (p : Lean.Grind.CommRing.PPoly),
        @Eq Bool (Lean.Grind.CommRing.Expr.degOk_k B a b) Bool.true →
          @Eq Lean.Grind.CommRing.PPoly p (Lean.Grind.CommRing.Expr.toPPX_k B bal₁ a) →
            @Eq Prop
              (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eq.h13.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Bool.false) (Bool.false) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPPX_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Bool.false
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.le_true_of_toPPX_eq.h13.prem0 rfl)

-- Lean.Grind.CommRing.le_false_of_poly, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_false_of_poly.h12.inst : Not
      (@Eq Prop
        (@LE.le Int Int.instLEInt
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        False) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.le_false_of_poly.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α]
        [inst_3 : @Std.LawfulOrderLT α inst_2 inst_1] [inst_4 : @Std.IsPreorder α inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_4]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (lhs rhs : Lean.Grind.CommRing.Expr) (n : Nat),
        @Eq Prop
          (@LE.le α inst_1 (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
          False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_false_of_poly.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))

-- Lean.Grind.IntModule.OfNatModule.of_not_le, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.IntModule.OfNatModule.of_not_le.h11.inst : ¬¬Lean.Grind.IntModule.OfNatModule.toQ 0 ≤ Lean.Grind.IntModule.OfNatModule.toQ 0 := by
  simp
theorem HypCheckProof.Lean.Grind.IntModule.OfNatModule.of_not_le.h11 : ¬∀ {α : Type} [inst : Lean.Grind.NatModule α] [inst_1 : LE α] [inst_2 : Std.IsPreorder α]
        [inst_3 : Lean.Grind.OrderedAdd α] {a b : α} {a' b' : Lean.Grind.IntModule.OfNatModule.Q α},
        Lean.Grind.IntModule.OfNatModule.toQ a = a' → Lean.Grind.IntModule.OfNatModule.toQ b = b' → ¬a' ≤ b' := fun hc_h => HypCheckProof.Lean.Grind.IntModule.OfNatModule.of_not_le.h11.inst (@hc_h (Nat) (Lean.Grind.Semiring.toNatModule) (instLENat) _ _ (0) (0) (Lean.Grind.IntModule.OfNatModule.toQ 0) (Lean.Grind.IntModule.OfNatModule.toQ 0) rfl rfl)

-- Lean.Grind.OrderedRing.mul_lt_mul_of_neg_right, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_right.h10.inst : ¬0 * -1 < 0 * -1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_right.h10.prem0 : -1 < 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_right.h10 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Lean.Grind.OrderedRing R] [inst_5 : Std.LawfulOrderLT R] {a b c : R}, c < 0 → b * c < a * c := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_right.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt.toRing) (Int.instLEInt) (Int.instLTInt) _ _ _ (0) (0) (-1) HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_right.h10.prem0)

-- Lean.Grind.OrderedRing.mul_lt_mul_of_neg_right, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_right.h11.inst : Not
      (@LT.lt Int Int.instLTInt
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_right.h11.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_right.h11 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.IsPartialOrder R inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2
            (@Std.IsPartialOrder.toIsPreorder R inst_1 inst_3)]
        [inst_5 : @Std.LawfulOrderLT R inst_2 inst_1] {a b c : R},
        @LT.lt R inst_2 a b →
          @LT.lt R inst_2
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) b c)
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) a c)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_right.h11.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.OrderedRing.mul_lt_mul_of_neg_right.h11.prem0)

-- Lean.Grind.AC.diseq_simp_rhs_middle, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_middle.h10.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_middle.h10.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_middle.h10.prem1 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_middle.h10.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) ≠
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_middle.h10 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op}
        (lhs₁ rhs₁ head tail lhs₂ rhs₂ rhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ ≠ Lean.Grind.AC.Seq.denote ctx rhs₂ →
            Lean.Grind.AC.Seq.denote ctx lhs₂ ≠ Lean.Grind.AC.Seq.denote ctx rhs₂' := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_middle.h10.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_middle.h10.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_middle.h10.prem1 HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_middle.h10.prem2)

-- Lean.Grind.CommRing.Expr.denote_mul_of_terms, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h9.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h9.prem1 : @Eq Lean.Grind.CommRing.Poly (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.sumB_k Lean.Grind.CommRing.Poly.combine_k
        ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).mulTerms_k
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb : Lean.Grind.CommRing.Poly) (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pb) →
          @Eq (List Lean.Grind.CommRing.Poly) ts (pa.mulTerms_k pb) →
            @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Poly.sumB_k Lean.Grind.CommRing.Poly.combine_k ts) →
              @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.mul b))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).mulTerms_k
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h9.prem0 rfl HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h9.prem1)

-- Lean.Grind.CommRing.Expr.denote_mul_of_terms, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h10.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h10.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h10.prem1 : @Eq Lean.Grind.CommRing.Poly (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.sumB_k Lean.Grind.CommRing.Poly.combine_k
        ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mulTerms_k
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb : Lean.Grind.CommRing.Poly) (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq (List Lean.Grind.CommRing.Poly) ts (pa.mulTerms_k pb) →
            @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Poly.sumB_k Lean.Grind.CommRing.Poly.combine_k ts) →
              @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.mul b))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).mulTerms_k
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h10.prem0 rfl HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h10.prem1)

-- Lean.Grind.CommRing.Expr.denote_mul_of_terms, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h11.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).mul
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.sumB_k Lean.Grind.CommRing.Poly.combine_k
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h11.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h11.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb : Lean.Grind.CommRing.Poly) (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pb) →
            @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Poly.sumB_k Lean.Grind.CommRing.Poly.combine_k ts) →
              @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.mul b))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@List.cons Lean.Grind.CommRing.Poly
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@List.nil Lean.Grind.CommRing.Poly)) (Lean.Grind.CommRing.Poly.sumB_k Lean.Grind.CommRing.Poly.combine_k
      (@List.cons Lean.Grind.CommRing.Poly
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@List.nil Lean.Grind.CommRing.Poly))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h11.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h11.prem1 rfl)

-- Lean.Grind.CommRing.Expr.denote_mul_of_terms, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h12.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h12.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h12.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb : Lean.Grind.CommRing.Poly) (ts : List Lean.Grind.CommRing.Poly) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pb) →
            @Eq (List Lean.Grind.CommRing.Poly) ts (pa.mulTerms_k pb) →
              @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.mul b))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).mulTerms_k
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h12.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.denote_mul_of_terms.h12.prem1 rfl)

-- Lean.Grind.AC.eq_simp_rhs_prefix, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h9.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h9.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h9.prem1 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h9.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h9 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op}
        (lhs₁ rhs₁ tail lhs₂ rhs₂ rhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₂ →
            Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₂' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h9.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h9.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h9.prem1 HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h9.prem2)

-- Lean.Grind.AC.eq_simp_rhs_prefix, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h11.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) =
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h11.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h11.prem1 : Lean.Grind.AC.simp_prefix_cert (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0)
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h11.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h11 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op}
        (lhs₁ rhs₁ tail lhs₂ rhs₂ rhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.simp_prefix_cert lhs₁ rhs₁ tail rhs₂ rhs₂' = Bool.true →
          Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
            Lean.Grind.AC.Seq.denote ctx lhs₂ = Lean.Grind.AC.Seq.denote ctx rhs₂' := fun hc_h => HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h11.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h11.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h11.prem1 HypCheckProof.Lean.Grind.AC.eq_simp_rhs_prefix.h11.prem2)

-- Lean.Grind.CommRing.le_mul, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_mul.h10.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_mul.h10.prem0 : @LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.CommRing.le_mul.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
        (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly) (k : Int) (p : Lean.Grind.CommRing.Poly),
        @LE.le α inst_1 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
          @LE.le α inst_1 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_mul.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.le_mul.h10.prem0)

-- Lean.Grind.CommRing.le_mul, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_mul.h11.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_mul.h11.prem0 : @Eq Bool
      (Lean.Grind.CommRing.mul_ineq_cert
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
theorem HypCheckProof.Lean.Grind.CommRing.le_mul.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] [inst_2 : LT α] [inst_3 : @Std.IsPreorder α inst_1]
        [inst_4 :
          @Lean.Grind.OrderedRing α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            inst_1 inst_2 inst_3]
        (ctx : Lean.Grind.CommRing.Context α) (p₁ : Lean.Grind.CommRing.Poly) (k : Int) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.mul_ineq_cert p₁ k p) Bool.true →
          @LE.le α inst_1 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_mul.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.le_mul.h11.prem0)

-- Lean.Grind.AC.diseq_simp_rhs_prefix, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_prefix.h9.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_prefix.h9.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_prefix.h9.prem1 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) =
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_prefix.h9.prem2 : Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.var 0) ≠
      Lean.Grind.AC.Seq.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_prefix.h9 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op}
        (lhs₁ rhs₁ tail lhs₂ rhs₂ rhs₂' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx lhs₁ = Lean.Grind.AC.Seq.denote ctx rhs₁ →
          Lean.Grind.AC.Seq.denote ctx lhs₂ ≠ Lean.Grind.AC.Seq.denote ctx rhs₂ →
            Lean.Grind.AC.Seq.denote ctx lhs₂ ≠ Lean.Grind.AC.Seq.denote ctx rhs₂' := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_prefix.h9.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_prefix.h9.prem0 (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)) (Lean.Grind.AC.Seq.var 0) HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_prefix.h9.prem1 HypCheckProof.Lean.Grind.AC.diseq_simp_rhs_prefix.h9.prem2)

-- Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_add_toExpr, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_add_toExpr.h8.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_add_toExpr.h8.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).nonneg_k.and
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).nonneg_k)
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_add_toExpr.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α)
        (a b : Lean.Grind.CommRing.Expr) (p q r : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Expr b (q.toExpr_k.add r.toExpr_k) →
          @Eq Lean.Grind.CommRing.Poly p (q.combine_k r) →
            @Eq Bool (q.nonneg_k.and r.nonneg_k) Bool.true →
              @Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_add_toExpr.h8.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).toExpr_k.add
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
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) rfl rfl HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_denoteS_eq_add_toExpr.h8.prem0)

-- Lean.Grind.Order.lt_unsat_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_unsat_k.h6.inst : Not False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_unsat_k.h6.prem0 : @Eq Bool
      ((@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).ble'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_unsat_k.h6.prem1 : @LT.lt UInt8 instLTUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@HAdd.hAdd UInt8 UInt8 UInt8
        (@instHAdd UInt8
          (@Lean.Grind.Semiring.toAdd UInt8
            (@Lean.Grind.Ring.toSemiring UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))))
        (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Int.cast UInt8 (@Lean.Grind.Ring.intCast UInt8 (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8))
          (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_unsat_k.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst : @Std.IsPreorder α inst] [inst : Lean.Grind.Ring α] {a : α} {k : Int},
        @Eq Bool (k.ble' (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) Bool.true →
          @LT.lt α inst_1 a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst))) a
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst) k)) →
            False) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_unsat_k.h6.inst (@hc_h (UInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.Order.lt_unsat_k.h6.prem0 HypCheckProof.Lean.Grind.Order.lt_unsat_k.h6.prem1)

-- Lean.Grind.Order.lt_unsat_k, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_unsat_k.h9.inst : Not False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_unsat_k.h9.prem0 : @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_unsat_k.h9 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a : α} {k : Int},
        @LT.lt α inst_1 a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k)) →
          False) := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_unsat_k.h9.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.Order.lt_unsat_k.h9.prem0)

-- Lean.Grind.Order.lt_unsat_k, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_unsat_k.h10.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_unsat_k.h10.prem0 : Int.ble' 0 0 = Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_unsat_k.h10 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α] [inst_3 : Std.IsPreorder α]
        [inst_4 : Lean.Grind.Ring α] [inst : Lean.Grind.OrderedRing α] {a : α} {k : Int}, k.ble' 0 = Bool.true → False := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_unsat_k.h10.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (Lean.Grind.instCommRingInt.toRing) _ (0) (0) HypCheckProof.Lean.Grind.Order.lt_unsat_k.h10.prem0)

-- Lean.Grind.OrderedRing.mul_pos_of_neg_of_neg, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos_of_neg_of_neg.h9.inst : ¬0 < 0 * -1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos_of_neg_of_neg.h9.prem0 : -1 < 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos_of_neg_of_neg.h9 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Lean.Grind.OrderedRing R] [inst_5 : Std.LawfulOrderLT R] {a b : R}, b < 0 → 0 < a * b := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_pos_of_neg_of_neg.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt.toRing) (Int.instLEInt) (Int.instLTInt) _ _ _ (0) (-1) HypCheckProof.Lean.Grind.OrderedRing.mul_pos_of_neg_of_neg.h9.prem0)

-- Lean.Grind.OrderedRing.mul_pos_of_neg_of_neg, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos_of_neg_of_neg.h10.inst : ¬0 < -1 * 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos_of_neg_of_neg.h10.prem0 : -1 < 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos_of_neg_of_neg.h10 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Lean.Grind.OrderedRing R] [inst_5 : Std.LawfulOrderLT R] {a b : R}, a < 0 → 0 < a * b := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_pos_of_neg_of_neg.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt.toRing) (Int.instLEInt) (Int.instLTInt) _ _ _ (-1) (0) HypCheckProof.Lean.Grind.OrderedRing.mul_pos_of_neg_of_neg.h10.prem0)

-- Lean.Grind.OrderedRing.mul_neg_of_neg_of_pos, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_neg_of_pos.h9.inst : Not
      (@LT.lt Int Int.instLTInt
        (@HMul.hMul Int Int Int
          (@instHMul Int
            (@Lean.Grind.Semiring.toMul Int
              (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_neg_of_pos.h9.prem0 : @LT.lt Int Int.instLTInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_neg_of_pos.h9 : Not
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
            b →
          @LT.lt R inst_2
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) a b)
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_neg_of_pos.h9.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_neg_of_pos.h9.prem0)

-- Lean.Grind.OrderedRing.mul_neg_of_neg_of_pos, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_neg_of_pos.h10.inst : ¬-1 * 0 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_neg_of_pos.h10.prem0 : -1 < 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_neg_of_pos.h10 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPartialOrder R]
        [inst_4 : Lean.Grind.OrderedRing R] [inst_5 : Std.LawfulOrderLT R] {a b : R}, a < 0 → a * b < 0 := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_neg_of_pos.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt.toRing) (Int.instLEInt) (Int.instLTInt) _ _ _ (-1) (0) HypCheckProof.Lean.Grind.OrderedRing.mul_neg_of_neg_of_pos.h10.prem0)

-- Lean.Grind.CommRing.Stepwise.simp, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h10.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h10.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h10.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k₁ : Int)
        (p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly)
        (hs : List Nat),
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@List.nil Nat) HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h10.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h10.prem1)

-- Lean.Grind.CommRing.Stepwise.simp, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h11.inst : Not
      (@Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h11.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k₁ : Int)
        (p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly)
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
            @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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
        Lean.Grind.CommRing.Mon.unit (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h11.prem0)

-- Lean.Grind.CommRing.Stepwise.simp, hypothesis 12: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h12.inst : Not
      (@Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h12.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h12 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (k₁ : Int)
        (p₁ : Lean.Grind.CommRing.Poly) (k₂ : Int) (m₂ : Lean.Grind.CommRing.Mon) (p₂ p : Lean.Grind.CommRing.Poly)
        (hs : List Nat),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mergeHint hs (Lean.Grind.CommRing.Poly.mulConst_k k₁ p₁)
              (Lean.Grind.CommRing.Poly.mulMon_k k₂ m₂ p₂)) →
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
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h12.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (Lean.Grind.CommRing.Mon.unit) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) (@List.nil Nat) rfl HypCheckProof.Lean.Grind.CommRing.Stepwise.simp.h12.prem0)

-- Lean.Grind.Field.NormNum.div_eq, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.div_eq.h8.inst : Not
      (@Eq Rat
        (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat (@Lean.Grind.Field.toDiv Rat Lean.Grind.instFieldRat))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.div_eq.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (a b : α) (v₁ v₂ v : Rat),
        @Eq α a (@Lean.Grind.Field.NormNum.ofRat α inst v₁) →
          @Eq α b (@Lean.Grind.Field.NormNum.ofRat α inst v₂) →
            @Eq α (@HDiv.hDiv α α α (@instHDiv α (@Lean.Grind.Field.toDiv α inst)) a b)
              (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.div_eq.h8.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) rfl rfl)

-- Lean.Grind.Field.NormNum.div_eq, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.div_eq.h9.inst : Not
      (@Eq Rat
        (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat (@Lean.Grind.Field.toDiv Rat Lean.Grind.instFieldRat))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.div_eq.h9.prem0 : @Eq Bool
      (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat)
        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
      Bool.true := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.div_eq.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (a b : α) (v₁ v₂ v : Rat),
        @Eq Bool
            (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat) v
              (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) v₁ v₂))
            Bool.true →
          @Eq α b (@Lean.Grind.Field.NormNum.ofRat α inst v₂) →
            @Eq α (@HDiv.hDiv α α α (@instHDiv α (@Lean.Grind.Field.toDiv α inst)) a b)
              (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.div_eq.h9.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Field.NormNum.div_eq.h9.prem0 rfl)

-- Lean.Grind.Field.NormNum.div_eq, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.div_eq.h10.inst : Not
      (@Eq Rat
        (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat (@Lean.Grind.Field.toDiv Rat Lean.Grind.instFieldRat))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.div_eq.h10.prem0 : @Eq Bool
      (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat)
        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))
      Bool.true := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.div_eq.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (a b : α) (v₁ v₂ v : Rat),
        @Eq Bool
            (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat) v
              (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) v₁ v₂))
            Bool.true →
          @Eq α a (@Lean.Grind.Field.NormNum.ofRat α inst v₁) →
            @Eq α (@HDiv.hDiv α α α (@instHDiv α (@Lean.Grind.Field.toDiv α inst)) a b)
              (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.div_eq.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Field.NormNum.div_eq.h10.prem0 rfl)

-- Lean.Grind.Field.IsOrdered.le_mul_inv_iff_le_mul_of_neg, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.le_mul_inv_iff_le_mul_of_neg.h10.inst : Not
      (Iff
        (@LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
            (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
              (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))))
        (@LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.le_mul_inv_iff_le_mul_of_neg.h10 : Not
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
          (@LE.le R inst_1 a
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              b (@Inv.inv R (@Lean.Grind.Field.toInv R inst) c)))
          (@LE.le R inst_1 b
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              a c))) := fun hc_h => HypCheckProof.Lean.Grind.Field.IsOrdered.le_mul_inv_iff_le_mul_of_neg.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.Field.IsOrdered.le_mul_inv_iff_mul_le, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.le_mul_inv_iff_mul_le.h10.inst : Not
      (Iff
        (@LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
              (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))))
        (@LE.le Rat Rat.instLE
          (@HMul.hMul Rat Rat Rat
            (@instHMul Rat
              (@Lean.Grind.Semiring.toMul Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))
            (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.IsOrdered.le_mul_inv_iff_mul_le.h10 : Not
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
          (@LE.le R inst_1 a
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              b (@Inv.inv R (@Lean.Grind.Field.toInv R inst) c)))
          (@LE.le R inst_1
            (@HMul.hMul R R R
              (@instHMul R
                (@Lean.Grind.Semiring.toMul R
                  (@Lean.Grind.CommSemiring.toSemiring R
                    (@Lean.Grind.CommRing.toCommSemiring R (@Lean.Grind.Field.toCommRing R inst)))))
              a c)
            b)) := fun hc_h => HypCheckProof.Lean.Grind.Field.IsOrdered.le_mul_inv_iff_mul_le.h10.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (Rat.instLE) (Rat.instLT) _ _ _ (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))

-- Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff, hypothesis 4: necessary
/- FAILED: 8:236: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 } | 43:123: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff.h4.inst : ¬(2 • 0 % 2 < 2 • 1 % 2 ↔ 0 < 2) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff.h4.prem0 : 0 % 2 < 1 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.NatModule M] [inst_3 : LT M]
        [inst : Std.LawfulOrderLT M] (k : Nat) {a b : M}, a < b → (k • a < k • b ↔ 0 < k) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule) ({ lt := fun (a b : Nat) => a % 2 < b % 2 : LT Nat }) (@Std.LawfulOrderLT.mk _ _ _ (by (try dsimp only);   (intros; omega))) (2) (0) (1) HypCheckProof.Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff.h4.prem0)
-/

-- Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff.h6.inst : ¬(0 • 0 ≤ 0 • 0 ↔ 0 < 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff.h6.prem0 : 0 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff.h6 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.NatModule M]
        [inst : Lean.Grind.OrderedAdd M] [inst : LT M] (k : Nat) {a b : M}, a < b → (k • a < k • b ↔ 0 < k) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff.h6.inst (@hc_h (Nat) (instLENat) _ (Lean.Grind.Semiring.toNatModule) _ ({ lt := fun (a b : Nat) => a ≤ b : LT Nat }) (0) (0) (0) HypCheckProof.Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff.h6.prem0)

-- Lean.Grind.CommRing.Expr.denote_eq_of_kron_poly, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_eq_of_kron_poly.h11.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
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
          (@HMul.hMul Int Int Int
            (@instHMul Int
              (@Lean.Grind.Semiring.toMul Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
            (@Nat.cast Int
              (@Lean.Grind.Semiring.natCast Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Lean.Grind.CommRing.PPoly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
              (@Lean.Grind.CommRing.Var.denote Int
                (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_eq_of_kron_poly.h11.prem0 : And
      (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (And
        (@LT.lt Nat instLTNat (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).degB_k
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@LT.lt Nat instLTNat
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).maxDeg_k
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_eq_of_kron_poly.h11.prem1 : @LT.lt Nat instLTNat
      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).majorant_k
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).norm1_k)
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).norm1_k)))
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_eq_of_kron_poly.h11 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B c : Nat)
        (e : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly) (E : Lean.Grind.CommRing.PPoly),
        And (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) B)
            (And (@LT.lt Nat instLTNat e.degB_k B) (@LT.lt Nat instLTNat p.maxDeg_k B)) →
          @LT.lt Nat instLTNat
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) e.majorant_k p.norm1_k)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) c E.norm1_k)))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) K) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx e)
              (@HAdd.hAdd α α α
                (@instHAdd α
                  (@Lean.Grind.Semiring.toAdd α
                    (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
                (@HMul.hMul α α α
                  (@instHMul α
                    (@Lean.Grind.Semiring.toMul α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))
                  (@Nat.cast α
                    (@Lean.Grind.Semiring.natCast α
                      (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))
                    c)
                  (@Lean.Grind.CommRing.PPoly.denote α (@Lean.Grind.CommRing.toRing α inst)
                    (@Lean.Grind.CommRing.Var.denote α ctx) B E)))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_eq_of_kron_poly.h11.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_eq_of_kron_poly.h11.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.denote_eq_of_kron_poly.h11.prem1)

-- Lean.Grind.CommRing.eq_true_of_kronLinS, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLinS.h8.inst : Not
      (@Eq Prop
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLinS.h8.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).linSOk_k
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLinS.h8.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLinS.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K a) (Lean.Grind.CommRing.Expr.kronLinEval_k K b) →
            @Eq Prop
              (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLinS.h8.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLinS.h8.prem0 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLinS.h8.prem1)

-- Lean.Grind.CommRing.eq_true_of_kronLinS, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLinS.h9.inst : Not
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
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLinS.h9.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linSOk_k
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLinS.h9.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLinS.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α]
        [inst_1 : @Lean.Grind.AddRightCancel α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.CommSemiring.toSemiring α inst))]
        (ctx : Lean.Grind.CommRing.Context α) (K : Nat) (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linSOk_k b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Prop
              (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLinS.h9.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.Grind.AddRightCancel.mk _ _ (by (try dsimp only);   (intros; omega))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLinS.h9.prem0 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronLinS.h9.prem1)

-- Lean.Grind.OrderedRing.mul_pos, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h5.inst : ¬0 < UInt8.ofNat 4 * UInt8.ofNat 64 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h5.prem0 : 0 < UInt8.ofNat 4 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h5.prem1 : 0 < UInt8.ofNat 64 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h5 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.IsPreorder R] {a b : R},
        0 < a → 0 < b → 0 < a * b := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h5.inst (@hc_h (UInt8) (Lean.Grind.instCommRingUInt8.toRing) (instLEUInt8) (instLTUInt8) _ (UInt8.ofNat 4) (UInt8.ofNat 64) HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h5.prem0 HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h5.prem1)

-- Lean.Grind.OrderedRing.mul_pos, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h8.inst : Not
      (@LT.lt Int Int.instLTInt
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
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h8.prem0 : @LT.lt Int Int.instLTInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h8 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.IsPreorder R inst_1]
        [inst_4 : @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2 inst_3] {a b : R},
        @LT.lt R inst_2
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
            b →
          @LT.lt R inst_2
            (@OfNat.ofNat R (nat_lit 0)
              (@Zero.toOfNat0 R
                (@Lean.Grind.AddCommMonoid.toZero R
                  (@Lean.Grind.NatModule.toAddCommMonoid R
                    (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) a b)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h8.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h8.prem0)

-- Lean.Grind.OrderedRing.mul_pos, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h9.inst : Not
      (@LT.lt Int Int.instLTInt
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
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h9.prem0 : @LT.lt Int Int.instLTInt
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
      (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h9 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.IsPreorder R inst_1]
        [inst_4 : @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2 inst_3] {a b : R},
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
            (@HMul.hMul R R R (@instHMul R (@Lean.Grind.Semiring.toMul R (@Lean.Grind.Ring.toSemiring R inst))) a b)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h9.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.OrderedRing.mul_pos.h9.prem0)

-- Lean.Grind.AC.diseq_norm_ai, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_norm_ai.h3.inst : ¬Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 0) ≠
        Lean.Grind.AC.Seq.denote
          { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.var 1) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_norm_ai.h3.prem0 : Std.Associative
      { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   grind))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_norm_ai.h3.prem1 : Lean.Grind.AC.eq_norm_ai_cert (Lean.Grind.AC.Expr.var 0) ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1))
        (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 1) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.diseq_norm_ai.h3.prem2 : Lean.Grind.AC.Expr.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        (Lean.Grind.AC.Expr.var 0) ≠
      Lean.Grind.AC.Expr.denote
        { vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }
        ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)) := by
  decide
theorem HypCheckProof.Lean.Grind.AC.diseq_norm_ai.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {x : Std.Associative ctx.op} (lhs rhs : Lean.Grind.AC.Expr)
        (lhs' rhs' : Lean.Grind.AC.Seq),
        Lean.Grind.AC.eq_norm_ai_cert lhs rhs lhs' rhs' = Bool.true →
          Lean.Grind.AC.Expr.denote ctx lhs ≠ Lean.Grind.AC.Expr.denote ctx rhs →
            Lean.Grind.AC.Seq.denote ctx lhs' ≠ Lean.Grind.AC.Seq.denote ctx rhs' := fun hc_h => HypCheckProof.Lean.Grind.AC.diseq_norm_ai.h3.inst (@hc_h (Nat) ({ vars := Lean.RArray.leaf { down := 1 : PLift Nat }, op := fun (a b : Nat) => a + b : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.diseq_norm_ai.h3.prem0 (Lean.Grind.AC.Expr.var 0) ((Lean.Grind.AC.Expr.var 0).op (Lean.Grind.AC.Expr.var 1)) (Lean.Grind.AC.Seq.var 0) (Lean.Grind.AC.Seq.var 1) HypCheckProof.Lean.Grind.AC.diseq_norm_ai.h3.prem1 HypCheckProof.Lean.Grind.AC.diseq_norm_ai.h3.prem2)

-- Lean.Grind.Order.le_eq_false_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_k.h6.inst : Not
      (@Eq Prop
        (@LE.le UInt8 instLEUInt8 (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
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
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_k.h6.prem0 : @Eq Bool
      ((@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).blt'
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_k.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α] {a : α} {k : Int},
        @Eq Bool (k.blt' (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) Bool.true →
          @Eq Prop
            (@LE.le α inst a
              (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
                (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k)))
            False) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_false_k.h6.inst (@hc_h (UInt8) (instLEUInt8) (instLTUInt8) _ _ (@Lean.Grind.CommRing.toRing UInt8 Lean.Grind.instCommRingUInt8) (UInt8.ofNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.Order.le_eq_false_k.h6.prem0)

-- Lean.Grind.Order.le_eq_false_k, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_k.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.Order.le_eq_false_k.h9 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : @Std.LawfulOrderLT α inst_1 inst]
        [inst_3 : @Std.IsPreorder α inst] [inst_4 : Lean.Grind.Ring α]
        [inst_5 : @Lean.Grind.OrderedRing α (@Lean.Grind.Ring.toSemiring α inst_4) inst inst_1 inst_3] {a : α} {k : Int},
        @Eq Prop
          (@LE.le α inst a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_4))) a
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_4) k)))
          False) := fun hc_h => HypCheckProof.Lean.Grind.Order.le_eq_false_k.h9.inst (@hc_h (Int) (Int.instLEInt) (Int.instLTInt) _ _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Lean.Grind.Order.lt_le_trans, hypothesis 3: necessary
/- FAILED: 10:309: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 } | 22:135: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans.h3.inst : ¬0 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans.h3.prem0 : 0 < 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans.h3.prem1 : 2 % 2 ≤ 0 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_le_trans.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.IsPreorder α] {a b c : α}, a < b → b ≤ c → a < c := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_le_trans.h3.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (instLTNat) (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (0) (2) (0) HypCheckProof.Lean.Grind.Order.lt_le_trans.h3.prem0 HypCheckProof.Lean.Grind.Order.lt_le_trans.h3.prem1)
-/

-- Lean.Grind.CommRing.Expr.denote_add_of, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h8.inst : Not
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
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).combine_k
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h8.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pb) →
          @Eq Lean.Grind.CommRing.Poly p (pa.combine_k pb) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.add b))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).combine_k
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h8.prem0 rfl)

-- Lean.Grind.CommRing.Expr.denote_add_of, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h9.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).add
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combine_k
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h9.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq Lean.Grind.CommRing.Poly p (pa.combine_k pb) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.add b))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combine_k
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h9.prem0 rfl)

-- Lean.Grind.CommRing.Expr.denote_add_of, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h10.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h10.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h10.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pb) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.add b))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h10.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.denote_add_of.h10.prem1)

-- Lean.Grind.CommRing.Expr.denote_sub_of, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h8.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).combine_k
            (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h8.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pb) →
          @Eq Lean.Grind.CommRing.Poly p
              (pa.combine_k
                (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  pb)) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.sub b))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).combine_k
      (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h8.prem0 rfl)

-- Lean.Grind.CommRing.Expr.denote_sub_of, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h9.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combine_k
            (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h9.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq Lean.Grind.CommRing.Poly p
              (pa.combine_k
                (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  pb)) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.sub b))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combine_k
      (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h9.prem0 rfl)

-- Lean.Grind.CommRing.Expr.denote_sub_of, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h10.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).sub
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h10.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h10.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a b : Lean.Grind.CommRing.Expr)
        (pa pb p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pb) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.sub b))
              (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h10.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.denote_sub_of.h10.prem1)

-- Lean.Grind.CommRing.Expr.eq_of_toPolyC_eq_toExpr, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_eq_toExpr.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_eq_toExpr.h3.prem0 : @Eq Lean.Grind.CommRing.Expr (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).toExpr_k := by
  rfl
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_eq_toExpr.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (a b : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal a c) →
          @Eq Lean.Grind.CommRing.Expr b p.toExpr_k →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_eq_toExpr.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) rfl HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_eq_toExpr.h3.prem0)

-- Lean.Grind.CommRing.Expr.eq_of_toPolyC_eq_toExpr, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_eq_toExpr.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_eq_toExpr.h9 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (a b : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Expr b p.toExpr_k →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_eq_toExpr.h9.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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

-- Lean.Grind.CommRing.Expr.eq_of_toPolyC_eq_toExpr, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_eq_toExpr.h10.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_eq_toExpr.h10 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)) c]
        (ctx : Lean.Grind.CommRing.Context α) (bal : Bool) (a b : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p (Lean.Grind.CommRing.Expr.toPolyXC_k bal a c) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_toPolyC_eq_toExpr.h10.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.toPolyXC_k Bool.false
      (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) rfl)

-- Lean.Grind.CommRing.Stepwise.coreK, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreK.h8.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreK.h8.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            ((Lean.Grind.CommRing.Expr.var
                  (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).sub
              (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))).beq'
        (Lean.Grind.CommRing.Poly.kron_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreK.h8.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreK.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool ((Lean.Grind.CommRing.Expr.kronEval_k K B (lhs.sub rhs)).beq' (Lean.Grind.CommRing.Poly.kron_k K B p))
            Bool.true →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs) →
            @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.coreK.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.Stepwise.coreK.h8.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.coreK.h8.prem1)

-- Lean.Grind.CommRing.Stepwise.coreK, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreK.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreK.h9.prem0 : @Eq Bool
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
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreK.h9.prem1 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.coreK.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (lhs rhs : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq Bool
            (Lean.Grind.CommRing.Stepwise.impOk_k K B (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (lhs.sub rhs) p (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
            Bool.true →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs) →
            @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.coreK.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Stepwise.coreK.h9.prem0 HypCheckProof.Lean.Grind.CommRing.Stepwise.coreK.h9.prem1)

-- Lean.Grind.CommRing.le_cancel_var, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h8.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h8.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h8.prem1 : @LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] (ctx : Lean.Grind.CommRing.Context α) (c : Int)
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
          @LE.le α inst_1 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
            @LE.le α inst_1 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h8.prem0 HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h8.prem1)

-- Lean.Grind.CommRing.le_cancel_var, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h9.inst : Not
      (@LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h9.prem0 : @Eq Bool
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
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h9.prem1 : @LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] (ctx : Lean.Grind.CommRing.Context α) (c : Int)
        (x : Lean.Grind.CommRing.Var) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.cancel_var_cert c x p₁ p₂) Bool.true →
          @LE.le α inst_1 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
            @LE.le α inst_1 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h9.prem0 HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h9.prem1)

-- Lean.Grind.CommRing.le_cancel_var, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h10.inst : Not
      (@LE.le Int Int.instLEInt
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
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h10.prem0 : @Eq Bool
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
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h10.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h10 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] [inst_1 : LE α] (ctx : Lean.Grind.CommRing.Context α) (c : Int)
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
            @LE.le α inst_1 (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h10.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (Int.instLEInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h10.prem0 HypCheckProof.Lean.Grind.CommRing.le_cancel_var.h10.prem1)

-- Lean.Grind.OrderedRing.pos_intCast_of_pos, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.pos_intCast_of_pos.h8.inst : Not
      (@LT.lt Int Int.instLTInt
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.pos_intCast_of_pos.h8 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsPreorder R inst_1]
        [inst_5 : @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2 inst_4] (a : Int),
        @LT.lt R inst_2
          (@OfNat.ofNat R (nat_lit 0)
            (@Zero.toOfNat0 R
              (@Lean.Grind.AddCommMonoid.toZero R
                (@Lean.Grind.NatModule.toAddCommMonoid R
                  (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
          (@Int.cast R (@Lean.Grind.Ring.intCast R inst) a)) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.pos_intCast_of_pos.h8.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Lean.Grind.OrderedRing.sq_pos, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.sq_pos.h6.inst : ¬0 < UInt8.ofNat 16 ^ 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.sq_pos.h6.prem0 : UInt8.ofNat 16 ≠ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.sq_pos.h6 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R]
        [inst_4 : Std.IsLinearOrder R] {a : R}, a ≠ 0 → 0 < a ^ 2 := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.sq_pos.h6.inst (@hc_h (UInt8) (Lean.Grind.instCommRingUInt8.toRing) (instLEUInt8) (instLTUInt8) _ _ (UInt8.ofNat 16) HypCheckProof.Lean.Grind.OrderedRing.sq_pos.h6.prem0)

-- Lean.Grind.OrderedRing.sq_pos, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.sq_pos.h8.inst : Not
      (@LT.lt Int Int.instLTInt
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))
        (@HPow.hPow Int Nat Int
          (@Lean.Grind.Semiring.npow Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.sq_pos.h8 : Not
      (∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : @Std.LawfulOrderLT R inst_2 inst_1]
        [inst_4 : @Std.IsLinearOrder R inst_1]
        [inst_5 :
          @Lean.Grind.OrderedRing R (@Lean.Grind.Ring.toSemiring R inst) inst_1 inst_2
            (@Std.IsLinearPreorder.toIsPreorder R inst_1 (@Std.IsLinearOrder.toIsLinearPreorder R inst_1 inst_4))]
        {a : R},
        @LT.lt R inst_2
          (@OfNat.ofNat R (nat_lit 0)
            (@Zero.toOfNat0 R
              (@Lean.Grind.AddCommMonoid.toZero R
                (@Lean.Grind.NatModule.toAddCommMonoid R
                  (@Lean.Grind.Semiring.toNatModule R (@Lean.Grind.Ring.toSemiring R inst))))))
          (@HPow.hPow R Nat R (@Lean.Grind.Semiring.npow R (@Lean.Grind.Ring.toSemiring R inst)) a
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.sq_pos.h8.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (Int.instLEInt) (Int.instLTInt) _ _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Lean.Grind.OrderedAdd.add_lt_right_iff, hypothesis 4: necessary
/- FAILED: 5:222: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 } | 39:123: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right_iff.h4.inst : ¬(0 % 2 < 1 % 2 ↔ (1 + 0) % 2 < (1 + 1) % 2) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M] [inst_3 : LT M]
        [inst : Std.LawfulOrderLT M] {a b : M} (c : M), a < b ↔ c + a < c + b := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right_iff.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) ({ lt := fun (a b : Nat) => a % 2 < b % 2 : LT Nat }) (@Std.LawfulOrderLT.mk _ _ _ (by (try dsimp only);   (intros; omega))) (0) (1) (1))
-/

-- Lean.Grind.OrderedAdd.add_lt_right_iff, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right_iff.h6.inst : ¬(0 % 2 < 1 % 2 ↔ (1 + 0) % 2 < (1 + 1) % 2) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right_iff.h6 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M]
        [inst : Lean.Grind.OrderedAdd M] [inst : LT M] {a b : M} (c : M), a < b ↔ c + a < c + b := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right_iff.h6.inst (@hc_h (Nat) (instLENat) _ (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) _ ({ lt := fun (a b : Nat) => a % 2 < b % 2 : LT Nat }) (0) (1) (1))

-- Lean.Grind.CommRing.diseq_cancel_var, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h7.inst : Not
      (@Ne Int
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
theorem HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h7.prem0 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h7.prem1 : @Ne Int
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
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h7 : Not
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
          @Ne α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
            @Ne α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h7.prem0 HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h7.prem1)

-- Lean.Grind.CommRing.diseq_cancel_var, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h8.inst : Not
      (@Ne Int
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
theorem HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h8.prem0 : @Eq Bool
      (Lean.Grind.CommRing.cancel_var_cert
        (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h8.prem1 : @Ne Int
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (Lean.Grind.CommRing.Mon.mult
            { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
              k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
            Lean.Grind.CommRing.Mon.unit)
          (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      (@OfNat.ofNat Int (nat_lit 0)
        (@Zero.toOfNat0 Int
          (@Lean.Grind.AddCommMonoid.toZero Int
            (@Lean.Grind.NatModule.toAddCommMonoid Int
              (@Lean.Grind.Semiring.toNatModule Int
                (@Lean.Grind.CommSemiring.toSemiring Int
                  (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (c : Int)
        (x : Lean.Grind.CommRing.Var) (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq Bool (Lean.Grind.CommRing.cancel_var_cert c x p₁ p₂) Bool.true →
          @Ne α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₁)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))))))) →
            @Ne α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h8.prem0 HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h8.prem1)

-- Lean.Grind.CommRing.diseq_cancel_var, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h9.inst : Not
      (@Ne Int
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
theorem HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h9.prem0 : @Eq Bool
      (Lean.Grind.CommRing.cancel_var_cert (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h9.prem1 : @Eq Int
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
theorem HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h9 : Not
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
            @Ne α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p₂)
              (@OfNat.ofNat α (nat_lit 0)
                (@Zero.toOfNat0 α
                  (@Lean.Grind.AddCommMonoid.toZero α
                    (@Lean.Grind.NatModule.toAddCommMonoid α
                      (@Lean.Grind.Semiring.toNatModule α
                        (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h9.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h9.prem0 HypCheckProof.Lean.Grind.CommRing.diseq_cancel_var.h9.prem1)

-- Int.Internal.Linear.eq_dvd_subst, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_dvd_subst.h7.inst : ¬0 ∣
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_dvd_subst.h7.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_dvd_subst.h7.prem1 : 0 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_dvd_subst.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ : Int.Internal.Linear.Poly) (d₂ : Int)
        (p₂ : Int.Internal.Linear.Poly) (d₃ : Int) (p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ = 0 →
          d₂ ∣ Int.Internal.Linear.Poly.denote' ctx p₂ → d₃ ∣ Int.Internal.Linear.Poly.denote' ctx p₃ := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_dvd_subst.h7.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (0) (Int.Internal.Linear.Poly.num 0) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_dvd_subst.h7.prem0 HypCheckProof.Int.Internal.Linear.eq_dvd_subst.h7.prem1)

-- Lean.Grind.CommRing.Expr.eq_of_kronSN, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronSN.h8.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronSN.h8.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronSN.h8.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronSN.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronEval_k K B a) (Lean.Grind.CommRing.Expr.kronEval_k K B b) →
            @Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronSN.h8.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronSN.h8.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronSN.h8.prem1)

-- Lean.Grind.CommRing.Expr.eq_of_kronSN, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronSN.h9.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronSN.h9.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronSN.h9.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronSN.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronSN.h9.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronSN.h9.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronSN.h9.prem1)

-- Int.Internal.Linear.eq_le_subst_nonneg_rfl, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.combine_mul_k
            ((Int.Internal.Linear.Poly.add 1 0
                  (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0))).coeff_k
              1)
            ((Int.Internal.Linear.Poly.num (-1)).coeff_k 1).neg_k (Int.Internal.Linear.Poly.num (-1))
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0)))) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h5.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0))) =
      0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h5.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num (-1)) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        p₃ = Int.Internal.Linear.Poly.combine_mul_k (p₁.coeff_k x) (p₂.coeff_k x).neg_k p₂ p₁ →
          Int.Internal.Linear.Poly.denote' ctx p₁ = 0 →
            Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h5.inst (@hc_h (Lean.RArray.leaf 1) (1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0))) (Int.Internal.Linear.Poly.num (-1)) (Int.Internal.Linear.Poly.combine_mul_k
      ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0))).coeff_k 1)
      ((Int.Internal.Linear.Poly.num (-1)).coeff_k 1).neg_k (Int.Internal.Linear.Poly.num (-1))
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.add (-1) 1 (Int.Internal.Linear.Poly.num 0)))) rfl HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h5.prem0 HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h5.prem1)

-- Int.Internal.Linear.eq_le_subst_nonneg_rfl, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h6.prem0 : Int.ble' 0 ((Int.Internal.Linear.Poly.num 0).coeff_k 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h6.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h6.prem2 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.ble' 0 (p₁.coeff_k x) = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₁ = 0 →
            Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h6.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h6.prem0 HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h6.prem1 HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h6.prem2)

-- Int.Internal.Linear.eq_le_subst_nonneg_rfl, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h7.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0)
          (Int.Internal.Linear.Poly.combine_mul_k ((Int.Internal.Linear.Poly.num (-1)).coeff_k 0)
            ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0).neg_k
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num (-1))) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h7.prem0 : Int.ble' 0 ((Int.Internal.Linear.Poly.num (-1)).coeff_k 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h7.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.ble' 0 (p₁.coeff_k x) = Bool.true →
          p₃ = Int.Internal.Linear.Poly.combine_mul_k (p₁.coeff_k x) (p₂.coeff_k x).neg_k p₂ p₁ →
            Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h7.inst (@hc_h (Lean.RArray.leaf 0) (0) (Int.Internal.Linear.Poly.num (-1)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.combine_mul_k ((Int.Internal.Linear.Poly.num (-1)).coeff_k 0)
      ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0).neg_k
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num (-1))) HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h7.prem0 rfl HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h7.prem1)

-- Int.Internal.Linear.eq_le_subst_nonneg_rfl, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h8.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0)
          (Int.Internal.Linear.Poly.combine_mul_k
            ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0)
            ((Int.Internal.Linear.Poly.num 1).coeff_k 0).neg_k (Int.Internal.Linear.Poly.num 1)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h8.prem0 : Int.ble' 0 ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0) = Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h8.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h8 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.ble' 0 (p₁.coeff_k x) = Bool.true →
          p₃ = Int.Internal.Linear.Poly.combine_mul_k (p₁.coeff_k x) (p₂.coeff_k x).neg_k p₂ p₁ →
            Int.Internal.Linear.Poly.denote' ctx p₁ = 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h8.inst (@hc_h (Lean.RArray.leaf 0) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.combine_mul_k ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).coeff_k 0)
      ((Int.Internal.Linear.Poly.num 1).coeff_k 0).neg_k (Int.Internal.Linear.Poly.num 1)
      (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))) HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h8.prem0 rfl HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg_rfl.h8.prem1)

-- Lean.Grind.CommRing.eq_true_of_kronSN, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronSN.h8.inst : Not
      (@Eq Prop
        (@Eq Int
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.CommRing.Expr.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
        True) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronSN.h8.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronSN.h8.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronSN.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronEval_k K B a) (Lean.Grind.CommRing.Expr.kronEval_k K B b) →
            @Eq Prop
              (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronSN.h8.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronSN.h8.prem0 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronSN.h8.prem1)

-- Lean.Grind.CommRing.eq_true_of_kronSN, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronSN.h9.inst : Not
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
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronSN.h9.prem0 : @Eq Bool
      (Lean.Grind.CommRing.Expr.degSOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronSN.h9.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronSN.h9 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommSemiring α] (ctx : Lean.Grind.CommRing.Context α) (K B : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (Lean.Grind.CommRing.Expr.degSOk_k B a b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq Prop
              (@Eq α (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx a)
                (@Lean.Grind.CommRing.Expr.denoteS α (@Lean.Grind.CommSemiring.toSemiring α inst) ctx b))
              True) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronSN.h9.inst (@hc_h (Int) (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronSN.h9.prem0 HypCheckProof.Lean.Grind.CommRing.eq_true_of_kronSN.h9.prem1)

-- Lean.Grind.Field.NormNum.npow_eq, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.npow_eq.h7.inst : Not
      (@Eq Rat
        (@HPow.hPow Rat Nat Rat
          (@Lean.Grind.Semiring.npow Rat
            (@Lean.Grind.CommSemiring.toSemiring Rat
              (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
          (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.Field.NormNum.npow_eq.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (a : α) (n : Nat) (v₁ v : Rat),
        @Eq α a (@Lean.Grind.Field.NormNum.ofRat α inst v₁) →
          @Eq α
            (@HPow.hPow α Nat α
              (@Lean.Grind.Semiring.npow α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
              a n)
            (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.npow_eq.h7.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) rfl)

-- Lean.Grind.Field.NormNum.npow_eq, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.npow_eq.h8.inst : Not
      (@Eq Rat
        (@HPow.hPow Rat Nat Rat
          (@Lean.Grind.Semiring.npow Rat
            (@Lean.Grind.CommSemiring.toSemiring Rat
              (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
          (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Lean.Grind.Field.NormNum.ofRat Rat Lean.Grind.instFieldRat
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.NormNum.npow_eq.h8.prem0 : @Eq Bool
      (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat)
        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (@HPow.hPow Rat Nat Rat (@instHPow Rat Nat Rat.instPowNat)
          (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Field.NormNum.npow_eq.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (a : α) (n : Nat) (v₁ v : Rat),
        @Eq Bool
            (@BEq.beq Rat (@instBEqOfDecidableEq Rat instDecidableEqRat) v
              (@HPow.hPow Rat Nat Rat (@instHPow Rat Nat Rat.instPowNat) v₁ n))
            Bool.true →
          @Eq α
            (@HPow.hPow α Nat α
              (@Lean.Grind.Semiring.npow α
                (@Lean.Grind.CommSemiring.toSemiring α
                  (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))
              a n)
            (@Lean.Grind.Field.NormNum.ofRat α inst v)) := fun hc_h => HypCheckProof.Lean.Grind.Field.NormNum.npow_eq.h8.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Field.NormNum.npow_eq.h8.prem0)

-- Int.Internal.Linear.eq_def'_norm, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def'_norm.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def'_norm.h6.prem0 : Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0 =
      Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def'_norm.h6.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) =
      Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Int.Internal.Linear.eq_def'_norm.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (e : Int.Internal.Linear.Expr)
        (ePoly ePoly' p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Var.denote ctx x = Int.Internal.Linear.Expr.denote_k ctx e →
          Int.Internal.Linear.Poly.denote' ctx ePoly = Int.Internal.Linear.Poly.denote' ctx ePoly' →
            Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_def'_norm.h6.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Expr.var 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_def'_norm.h6.prem0 HypCheckProof.Int.Internal.Linear.eq_def'_norm.h6.prem1)

-- Int.Internal.Linear.eq_def'_norm, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def'_norm.h7.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add (-1) 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def'_norm.h7.prem0 : Int.Internal.Linear.eq_def'_norm_cert 0 (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.num 0)
        (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add (-1) 0 (Int.Internal.Linear.Poly.num 0)) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def'_norm.h7.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) =
      Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Int.Internal.Linear.eq_def'_norm.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (e : Int.Internal.Linear.Expr)
        (ePoly ePoly' p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.eq_def'_norm_cert x e ePoly ePoly' p = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx ePoly = Int.Internal.Linear.Poly.denote' ctx ePoly' →
            Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_def'_norm.h7.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add (-1) 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_def'_norm.h7.prem0 HypCheckProof.Int.Internal.Linear.eq_def'_norm.h7.prem1)

-- Lean.Grind.CommRing.eq_false_of_sub, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_false_of_sub.h7.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_false_of_sub.h7.prem0 : @Eq Bool (Int.beqZero_k (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Bool.false := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_false_of_sub.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (k : Int),
        @Eq Bool k.beqZero_k Bool.false →
          @Eq Prop
            (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_false_of_sub.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.CommRing.eq_false_of_sub.h7.prem0)

-- Lean.Grind.CommRing.eq_false_of_sub, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.eq_false_of_sub.h8.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.eq_false_of_sub.h8.prem0 : @Eq Int
      (@HSub.hSub Int Int Int
        (@instHSub Int (@Lean.Grind.Ring.toSub Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
      (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.eq_false_of_sub.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α]
        [inst_1 :
          @Lean.Grind.IsCharP α (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        (ctx : Lean.Grind.CommRing.Context α) (lhs rhs : Lean.Grind.CommRing.Expr) (k : Int),
        @Eq α
            (@HSub.hSub α α α (@instHSub α (@Lean.Grind.Ring.toSub α (@Lean.Grind.CommRing.toRing α inst)))
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α inst)) k) →
          @Eq Prop
            (@Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx lhs)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx rhs))
            False) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.eq_false_of_sub.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) _ (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.CommRing.eq_false_of_sub.h8.prem0)

-- Lean.Grind.CommRing.Expr.toLinQ_spec, hypothesis 6: necessary
/- FAILED: 2:106: failed to synthesize instance of type class
  Lean.Grind.Ring Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 2:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.toLinQ_spec.h6.inst : ¬(Lean.Grind.CommRing.PPoly.denoteG (Lean.Grind.CommRing.PPoly.linVal fun (a : Nat) => 0)
            (Lean.Grind.CommRing.Expr.toLinQ [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).fst =
          ↑(Lean.Grind.CommRing.Expr.toLinQ [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).snd *
            Lean.Grind.CommRing.Expr.denoteF (fun (a : Nat) => 0) (Lean.Grind.CommRing.Expr.var 0) ∧
        (Lean.Grind.CommRing.Expr.toLinQ [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).snd ≠ 0 ∧
          Lean.Grind.CommRing.PPoly.kron (2 ^ 0)
                (Lean.Grind.CommRing.Expr.toLinQ [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).fst =
              (Lean.Grind.CommRing.Expr.kronQLin_k 0 [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).fst ∧
            (Lean.Grind.CommRing.Expr.toLinQ [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).snd =
                (Lean.Grind.CommRing.Expr.kronQLin_k 0 [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).snd ∧
              (Lean.Grind.CommRing.Expr.toLinQ [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).fst.norm1 ≤
                  (Lean.Grind.CommRing.Expr.majQ_k [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).fst ∧
                (Lean.Grind.CommRing.Expr.toLinQ [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).snd =
                  (Lean.Grind.CommRing.Expr.majQ_k [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).snd) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.toLinQ_spec.h6.prem0 : Lean.Grind.CommRing.Expr.degQL_k [(0, 0)] (Lean.Grind.CommRing.Expr.var 0) ≤ 1 := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.toLinQ_spec.h6 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (f : Nat → α) (K : Nat)
        (invs : Lean.Grind.CommRing.InvVars) (e : Lean.Grind.CommRing.Expr),
        Lean.Grind.CommRing.Expr.degQL_k invs e ≤ 1 →
          Lean.Grind.CommRing.PPoly.denoteG (Lean.Grind.CommRing.PPoly.linVal f)
                (Lean.Grind.CommRing.Expr.toLinQ invs e).fst =
              ↑(Lean.Grind.CommRing.Expr.toLinQ invs e).snd * Lean.Grind.CommRing.Expr.denoteF f e ∧
            (Lean.Grind.CommRing.Expr.toLinQ invs e).snd ≠ 0 ∧
              Lean.Grind.CommRing.PPoly.kron (2 ^ K) (Lean.Grind.CommRing.Expr.toLinQ invs e).fst =
                  (Lean.Grind.CommRing.Expr.kronQLin_k K invs e).fst ∧
                (Lean.Grind.CommRing.Expr.toLinQ invs e).snd = (Lean.Grind.CommRing.Expr.kronQLin_k K invs e).snd ∧
                  (Lean.Grind.CommRing.Expr.toLinQ invs e).fst.norm1 ≤ (Lean.Grind.CommRing.Expr.majQ_k invs e).fst ∧
                    (Lean.Grind.CommRing.Expr.toLinQ invs e).snd = (Lean.Grind.CommRing.Expr.majQ_k invs e).snd := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.toLinQ_spec.h6.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (fun (a : Nat) => 0) (0) ([(0, 0)]) (Lean.Grind.CommRing.Expr.var 0) HypCheckProof.Lean.Grind.CommRing.Expr.toLinQ_spec.h6.prem0)
-/

-- Lean.Grind.OrderedAdd.add_le_left, hypothesis 4: necessary
/- FAILED: 8:180: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 } | 40:123: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLENat
inferred
  { le := fun a b => a % 2 ≤ b % 2 }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_left.h4.inst : ¬(0 + 1) % 2 ≤ (1 + 1) % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_left.h4.prem0 : 0 % 2 ≤ 1 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_left.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M] {a b : M},
        a ≤ b → ∀ (c : M), a + c ≤ b + c := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_le_left.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk _ _ (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) (0) (1) HypCheckProof.Lean.Grind.OrderedAdd.add_le_left.h4.prem0 (1))
-/

-- Lean.Grind.CommRing.Expr.eq_of_kronLin, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLin.h7.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLin.h7.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).linOk_k
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLin.h7.prem1 : @Eq Int
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (Lean.Grind.CommRing.Expr.kronLinEval_k (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLin.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linOk_k b) Bool.true →
          @Eq Int (Lean.Grind.CommRing.Expr.kronLinEval_k K a) (Lean.Grind.CommRing.Expr.kronLinEval_k K b) →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLin.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLin.h7.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLin.h7.prem1)

-- Lean.Grind.CommRing.Expr.eq_of_kronLin, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLin.h8.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLin.h8.prem0 : @Eq Bool
      ((Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).linOk_k
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLin.h8.prem1 : @Eq Bool
      (Lean.Grind.CommRing.Expr.kronOk_k (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLin.h8 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (K : Nat)
        (a b : Lean.Grind.CommRing.Expr),
        @Eq Bool (a.linOk_k b) Bool.true →
          @Eq Bool (Lean.Grind.CommRing.Expr.kronOk_k K a b) Bool.true →
            @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
              (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx b)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLin.h8.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLin.h8.prem0 HypCheckProof.Lean.Grind.CommRing.Expr.eq_of_kronLin.h8.prem1)

-- Lean.Grind.OrderedRing.mul_pos_iff, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos_iff.h6.inst : ¬(0 < UInt8.ofNat 4 * UInt8.ofNat 64 ↔ 0 < UInt8.ofNat 4 ∧ 0 < UInt8.ofNat 64 ∨ UInt8.ofNat 4 < 0 ∧ UInt8.ofNat 64 < 0) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedRing.mul_pos_iff.h6 : ¬∀ {R : Type} [inst : Lean.Grind.Ring R] [inst_1 : LE R] [inst_2 : LT R] [inst_3 : Std.LawfulOrderLT R]
        [inst_4 : Std.IsLinearOrder R] {a b : R}, 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := fun hc_h => HypCheckProof.Lean.Grind.OrderedRing.mul_pos_iff.h6.inst (@hc_h (UInt8) (Lean.Grind.instCommRingUInt8.toRing) (instLEUInt8) (instLTUInt8) _ _ (UInt8.ofNat 4) (UInt8.ofNat 64))

-- Lean.Grind.Preorder.not_gt_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Preorder.not_gt_of_lt.h3.inst : Not
      (Not
        (@GT.gt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Preorder.not_gt_of_lt.h3.prem0 : @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.Preorder.not_gt_of_lt.h3 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst : @Std.IsPreorder α inst] {a b : α},
        @LT.lt α inst_1 a b → Not (@GT.gt α inst_1 a b)) := fun hc_h => HypCheckProof.Lean.Grind.Preorder.not_gt_of_lt.h3.inst (@hc_h (Nat) (instLENat) (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Lean.Grind.Preorder.not_gt_of_lt.h3.prem0)

-- Lean.Grind.Linarith.lt_unsat, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.lt_unsat.h7.inst : ¬False := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.lt_unsat.h7 : ¬∀ {α : Type} [inst : Lean.Grind.IntModule α] [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α]
        [inst : Std.IsPreorder α] (ctx : Lean.Grind.Linarith.Context α), False := fun hc_h => HypCheckProof.Lean.Grind.Linarith.lt_unsat.h7.inst (@hc_h (Int) (Lean.Grind.Ring.toIntModule) (Int.instLEInt) (Int.instLTInt) _ _ (Lean.RArray.leaf 1))

-- Lean.Grind.Order.eq_of_le_of_le_0, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.eq_of_le_of_le_0.h6.inst : Not
      (@Eq Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.eq_of_le_of_le_0.h6.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.eq_of_le_of_le_0.h6 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : @Std.IsPartialOrder α inst] [inst_2 : Lean.Grind.Ring α] {a b : α},
        @LE.le α inst b
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_2))) a
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_2) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) →
          @Eq α a b) := fun hc_h => HypCheckProof.Lean.Grind.Order.eq_of_le_of_le_0.h6.inst (@hc_h (Int) (Int.instLEInt) _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) HypCheckProof.Lean.Grind.Order.eq_of_le_of_le_0.h6.prem0)

-- Lean.Grind.Order.eq_of_le_of_le_0, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.eq_of_le_of_le_0.h7.inst : Not
      (@Eq Int (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.eq_of_le_of_le_0.h7.prem0 : @LE.le Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
      (@HAdd.hAdd Int Int Int
        (@instHAdd Int
          (@Lean.Grind.Semiring.toAdd Int
            (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))))
        (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (@Int.cast Int (@Lean.Grind.Ring.intCast Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Order.eq_of_le_of_le_0.h7 : Not
      (∀ {α : Type} [inst : LE α] [inst_1 : @Std.IsPartialOrder α inst] [inst_2 : Lean.Grind.Ring α] {a b : α},
        @LE.le α inst a
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst_2))) b
              (@Int.cast α (@Lean.Grind.Ring.intCast α inst_2) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) →
          @Eq α a b) := fun hc_h => HypCheckProof.Lean.Grind.Order.eq_of_le_of_le_0.h7.inst (@hc_h (Int) (Int.instLEInt) _ (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.Order.eq_of_le_of_le_0.h7.prem0)

-- Int.Internal.Linear.eq_diseq_subst, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h5.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h5.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≠
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ = 0 →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≠ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h5.prem0 HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h5.prem1)

-- Int.Internal.Linear.eq_diseq_subst, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h6.prem0 : Int.Internal.Linear.diseq_eq_subst_cert 0 (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h6.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≠
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.diseq_eq_subst_cert x p₁ p₂ p₃ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≠ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h6.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h6.prem0 HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h6.prem1)

-- Int.Internal.Linear.eq_diseq_subst, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h7.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0) (Int.Internal.Linear.Poly.num 0) ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h7.prem0 : Int.Internal.Linear.diseq_eq_subst_cert 0 (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
        (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h7.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.diseq_eq_subst_cert x p₁ p₂ p₃ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₁ = 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h7.inst (@hc_h (Lean.RArray.leaf 0) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h7.prem0 HypCheckProof.Int.Internal.Linear.eq_diseq_subst.h7.prem1)

-- Int.Internal.Linear.eq_le_subst_nonneg, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h5.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h5.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ = 0 →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h5.prem0 HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h5.prem1)

-- Int.Internal.Linear.eq_le_subst_nonneg, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h6.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0) (Int.Internal.Linear.Poly.num 1) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h6.prem0 : Int.Internal.Linear.eq_le_subst_nonneg_cert 0 (Int.Internal.Linear.Poly.num (-1))
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 1) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h6.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h6 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.eq_le_subst_nonneg_cert x p₁ p₂ p₃ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h6.inst (@hc_h (Lean.RArray.leaf 0) (0) (Int.Internal.Linear.Poly.num (-1)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h6.prem0 HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h6.prem1)

-- Int.Internal.Linear.eq_le_subst_nonneg, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h7.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0) (Int.Internal.Linear.Poly.num 1) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h7.prem0 : Int.Internal.Linear.eq_le_subst_nonneg_cert 0 (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
        (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.num 1) =
      Bool.true := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h7.prem1 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h7 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.eq_le_subst_nonneg_cert x p₁ p₂ p₃ = Bool.true →
          Int.Internal.Linear.Poly.denote' ctx p₁ = 0 → Int.Internal.Linear.Poly.denote' ctx p₃ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h7.inst (@hc_h (Lean.RArray.leaf 0) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 1) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h7.prem0 HypCheckProof.Int.Internal.Linear.eq_le_subst_nonneg.h7.prem1)

-- Lean.Grind.CommRing.PPoly.denote_eq_zero_of_coeff, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denote_eq_zero_of_coeff.h7.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.PPoly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (fun (a : Nat) => @OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@OfNat.ofNat Int (nat_lit 0)
          (@Zero.toOfNat0 Int
            (@Lean.Grind.AddCommMonoid.toZero Int
              (@Lean.Grind.NatModule.toAddCommMonoid Int
                (@Lean.Grind.Semiring.toNatModule Int
                  (@Lean.Grind.Ring.toSemiring Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denote_eq_zero_of_coeff.h7.prem0 : @LE.le Nat instLENat (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).size
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.PPoly.denote_eq_zero_of_coeff.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.Ring α] (f : Nat → α) (B n : Nat) (p : Lean.Grind.CommRing.PPoly),
        @LE.le Nat instLENat p.size n →
          @Eq α (@Lean.Grind.CommRing.PPoly.denote α inst f B p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α (@Lean.Grind.Ring.toSemiring α inst))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.PPoly.denote_eq_zero_of_coeff.h7.inst (@hc_h (Int) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (fun (a : Nat) => @OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.CommRing.PPoly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) HypCheckProof.Lean.Grind.CommRing.PPoly.denote_eq_zero_of_coeff.h7.prem0)

-- Lean.Grind.Linarith.diseq_norm, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_norm.h6.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.diseq_norm.h6.prem0 : @Ne Int
      (@Lean.Grind.Linarith.Expr.denote_k Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) Lean.Grind.Linarith.Expr.zero)
      (@Lean.Grind.Linarith.Expr.denote_k Int
        (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt))
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.diseq_norm.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] (ctx : Lean.Grind.Linarith.Context α)
        (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @Ne α (@Lean.Grind.Linarith.Expr.denote_k α inst ctx lhs) (@Lean.Grind.Linarith.Expr.denote_k α inst ctx rhs) →
          @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.diseq_norm.h6.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Expr.var (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.diseq_norm.h6.prem0)

-- Lean.Grind.Linarith.diseq_norm, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.diseq_norm.h7.inst : Not
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
theorem HypCheckProof.Lean.Grind.Linarith.diseq_norm.h7.prem0 : @Eq Bool
      (Lean.Grind.Linarith.norm_cert Lean.Grind.Linarith.Expr.zero Lean.Grind.Linarith.Expr.zero
        Lean.Grind.Linarith.Poly.nil)
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.diseq_norm.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.IntModule α] (ctx : Lean.Grind.Linarith.Context α)
        (lhs rhs : Lean.Grind.Linarith.Expr) (p : Lean.Grind.Linarith.Poly),
        @Eq Bool (Lean.Grind.Linarith.norm_cert lhs rhs p) Bool.true →
          @Ne α (@Lean.Grind.Linarith.Poly.denote' α inst ctx p)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α (@Lean.Grind.IntModule.toNatModule α inst)))))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.diseq_norm.h7.inst (@hc_h (Int) (@Lean.Grind.Ring.toIntModule Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Expr.zero) (Lean.Grind.Linarith.Poly.nil) HypCheckProof.Lean.Grind.Linarith.diseq_norm.h7.prem0)

-- Lean.Grind.CommRing.Expr.denote_toPPX_k, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPPX_k.h7.inst : ¬Lean.Grind.CommRing.PPoly.denote (fun (a : Nat) => -1) 2
          (Lean.Grind.CommRing.Expr.toPPX_k 2 Bool.false
            ((Lean.Grind.CommRing.Expr.var 0).mul (Lean.Grind.CommRing.Expr.var 0))) =
        Lean.Grind.CommRing.Expr.denoteF (fun (a : Nat) => -1)
          ((Lean.Grind.CommRing.Expr.var 0).mul (Lean.Grind.CommRing.Expr.var 0)) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPPX_k.h7.prem0 : 1 < 2 := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPPX_k.h7 : ¬∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Nat → α) (B : Nat),
        1 < B →
          ∀ (bal : Bool) (e : Lean.Grind.CommRing.Expr),
            Lean.Grind.CommRing.PPoly.denote ctx B (Lean.Grind.CommRing.Expr.toPPX_k B bal e) =
              Lean.Grind.CommRing.Expr.denoteF ctx e := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPPX_k.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (fun (a : Nat) => -1) (2) HypCheckProof.Lean.Grind.CommRing.Expr.denote_toPPX_k.h7.prem0 (Bool.false) ((Lean.Grind.CommRing.Expr.var 0).mul (Lean.Grind.CommRing.Expr.var 0)))

-- Lean.Grind.CommRing.Poly.denote_cancelVarB_k, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_cancelVarB_k.h7.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.cancelVarB_k
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
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_cancelVarB_k.h7.prem0 : @Ne Int (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_cancelVarB_k.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (p : Lean.Grind.CommRing.Poly)
        (c : Int) (x : Lean.Grind.CommRing.Var),
        @Ne Int c (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          @Eq α
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx
              (Lean.Grind.CommRing.Poly.cancelVarB_k c x p))
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_cancelVarB_k.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.Lean.Grind.CommRing.Poly.denote_cancelVarB_k.h7.prem0)

-- Lean.Grind.CommRing.Expr.denote_neg_of, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_of.h6.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).neg)
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (Lean.Grind.CommRing.Mon.mult
                { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                  k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                Lean.Grind.CommRing.Mon.unit)
              (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_of.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr)
        (pa p : Lean.Grind.CommRing.Poly),
        @Eq Lean.Grind.CommRing.Poly p
            (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              pa) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a.neg)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_of.h6.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (Lean.Grind.CommRing.Poly.mulConst_k (Int.negSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
        (Lean.Grind.CommRing.Mon.mult
          { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
            k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
          Lean.Grind.CommRing.Mon.unit)
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))) rfl)

-- Lean.Grind.CommRing.Expr.denote_neg_of, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_of.h7.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_of.h7.prem0 : @Eq Int
      (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
      (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
        (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_of.h7 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr)
        (pa p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx pa) →
          @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a.neg)
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_of.h7.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) HypCheckProof.Lean.Grind.CommRing.Expr.denote_neg_of.h7.prem0)

-- Lean.Grind.CommRing.Poly.denoteS_addConst, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_addConst.h6.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denoteS Int
          (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.num
                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))).addConst
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@HAdd.hAdd Int Int Int
          (@instHAdd Int
            (@Lean.Grind.Semiring.toAdd Int
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))))
          (@Lean.Grind.CommRing.Poly.denoteS Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Poly.num
              (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
          (@Nat.cast Int
            (@Lean.Grind.Semiring.natCast Int
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))
            (Int.toNat (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_addConst.h6.prem0 : @GE.ge Int Int.instLEInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_addConst.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.Semiring α] (ctx : Lean.Grind.CommRing.Context α) (p : Lean.Grind.CommRing.Poly)
        (k : Int),
        @GE.ge Int Int.instLEInt k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          @Eq α (@Lean.Grind.CommRing.Poly.denoteS α inst ctx (p.addConst k))
            (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α inst))
              (@Lean.Grind.CommRing.Poly.denoteS α inst ctx p) (@Nat.cast α (@Lean.Grind.Semiring.natCast α inst) k.toNat))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_addConst.h6.inst (@hc_h (Int) (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.CommRing.Poly.denoteS_addConst.h6.prem0)

-- Lean.Grind.Preorder.le_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Preorder.le_of_lt.h3.inst : ¬1 ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Preorder.le_of_lt.h3.prem0 : 1 ≠ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.Preorder.le_of_lt.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] {a b : α}, a < b → a ≤ b := fun hc_h => HypCheckProof.Lean.Grind.Preorder.le_of_lt.h3.inst (@hc_h (Nat) (instLENat) ({ lt := fun (a b : Nat) => a ≠ b : LT Nat }) (1) (0) HypCheckProof.Lean.Grind.Preorder.le_of_lt.h3.prem0)

-- Lean.Grind.LinearOrder.trichotomy, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.LinearOrder.trichotomy.h3.inst : ¬(Bool.false = Bool.true ∨ Bool.false = Bool.true ∨ Bool.true = Bool.false) := by
  decide
theorem HypCheckProof.Lean.Grind.LinearOrder.trichotomy.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst : Std.IsLinearOrder α] (a b : α), a < b ∨ a = b ∨ b < a := fun hc_h => HypCheckProof.Lean.Grind.LinearOrder.trichotomy.h3.inst (@hc_h (Bool) (Bool.instLE) ({ lt := fun (a b : Bool) => a = b : LT Bool }) (@Std.IsLinearOrder.mk _ _ (@Std.IsPartialOrder.mk _ _ (@Std.IsPreorder.mk _ _ (by (try dsimp only);   decide) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (Bool.false) (Bool.true))

-- Lean.Grind.LinearOrder.trichotomy, hypothesis 4: necessary
/- FAILED: 4:360: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLTNat
inferred
  { lt := fun a b => a % 2 < b % 2 } | 26:123: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  instLTNat
inferred
  { lt := fun a b => a % 2 < b % 2 }
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.LinearOrder.trichotomy.h4.inst : ¬(0 % 2 < 2 % 2 ∨ 0 = 2 ∨ 2 % 2 < 0 % 2) := by
  decide
theorem HypCheckProof.Lean.Grind.LinearOrder.trichotomy.h4 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst : Std.LawfulOrderLT α] (a b : α), a < b ∨ a = b ∨ b < a := fun hc_h => HypCheckProof.Lean.Grind.LinearOrder.trichotomy.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) ({ lt := fun (a b : Nat) => a % 2 < b % 2 : LT Nat }) (@Std.LawfulOrderLT.mk _ _ _ (by (try dsimp only);   (intros; omega))) (0) (2))
-/

-- Int.Internal.Linear.not_le_norm_expr, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.not_le_norm_expr.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.not_le_norm_expr.h4.prem0 : ¬Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0) ≤
        Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.not_le_norm_expr.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        ¬Int.Internal.Linear.Expr.denote_k ctx lhs ≤ Int.Internal.Linear.Expr.denote_k ctx rhs →
          Int.Internal.Linear.Poly.denote' ctx p ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.not_le_norm_expr.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.not_le_norm_expr.h4.prem0)

-- Int.Internal.Linear.not_le_norm_expr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.not_le_norm_expr.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.not_le_norm_expr.h5.prem0 : Int.Internal.Linear.not_le_norm_expr_cert (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0)
        (Int.Internal.Linear.Poly.num 1) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.not_le_norm_expr.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.not_le_norm_expr_cert lhs rhs p = Bool.true → Int.Internal.Linear.Poly.denote' ctx p ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.not_le_norm_expr.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.not_le_norm_expr.h5.prem0)

-- Int.Internal.Linear.diseq_of_core, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_of_core.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_of_core.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≠
      Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_of_core.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ ≠ Int.Internal.Linear.Poly.denote' ctx p₂ →
          Int.Internal.Linear.Poly.denote' ctx p₃ ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_of_core.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.diseq_of_core.h4.prem0)

-- Int.Internal.Linear.diseq_of_core, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_of_core.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_of_core.h5.prem0 : Int.Internal.Linear.eq_of_core_cert (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0)
        (Int.Internal.Linear.Poly.num 0) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_of_core.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ p₃ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.eq_of_core_cert p₁ p₂ p₃ = Bool.true → Int.Internal.Linear.Poly.denote' ctx p₃ ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_of_core.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.diseq_of_core.h5.prem0)

-- Lean.Grind.CommRing.inv_zero_eqC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.inv_zero_eqC.h3.inst : Not
      (@Eq Rat
        (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
          (@Lean.Grind.CommRing.denoteInt Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@OfNat.ofNat Rat (nat_lit 0)
          (@Zero.toOfNat0 Rat
            (@Lean.Grind.AddCommMonoid.toZero Rat
              (@Lean.Grind.NatModule.toAddCommMonoid Rat
                (@Lean.Grind.Semiring.toNatModule Rat
                  (@Lean.Grind.CommSemiring.toSemiring Rat
                    (@Lean.Grind.CommRing.toCommSemiring Rat
                      (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.inv_zero_eqC.h3.prem0 : @Eq Bool
      (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq)
        (@HMod.hMod Int Int Int (@instHMod Int Int.instMod) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
          (@Nat.cast Int instNatCastInt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
      Bool.true := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.inv_zero_eqC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Field α] (b : Int),
        @Eq Bool
            (@BEq.beq Int (@instBEqOfDecidableEq Int Int.instDecidableEq)
              (@HMod.hMod Int Int Int (@instHMod Int Int.instMod) b (@Nat.cast Int instNatCastInt c))
              (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            Bool.true →
          @Eq α
            (@Inv.inv α (@Lean.Grind.Field.toInv α inst)
              (@Lean.Grind.CommRing.denoteInt α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) b))
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α
                        (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.inv_zero_eqC.h3.inst (@hc_h (Rat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instFieldRat) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Lean.Grind.CommRing.inv_zero_eqC.h3.prem0)

-- Lean.Grind.CommRing.inv_zero_eqC, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.inv_zero_eqC.h5.inst : Not
      (@Eq Rat
        (@Inv.inv Rat (@Lean.Grind.Field.toInv Rat Lean.Grind.instFieldRat)
          (@Lean.Grind.CommRing.denoteInt Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        (@OfNat.ofNat Rat (nat_lit 0)
          (@Zero.toOfNat0 Rat
            (@Lean.Grind.AddCommMonoid.toZero Rat
              (@Lean.Grind.NatModule.toAddCommMonoid Rat
                (@Lean.Grind.Semiring.toNatModule Rat
                  (@Lean.Grind.CommSemiring.toSemiring Rat
                    (@Lean.Grind.CommRing.toCommSemiring Rat
                      (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))))))) := by
  decide +kernel
theorem HypCheckProof.Lean.Grind.CommRing.inv_zero_eqC.h5 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            c]
        (b : Int),
        @Eq α
          (@Inv.inv α (@Lean.Grind.Field.toInv α inst)
            (@Lean.Grind.CommRing.denoteInt α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)) b))
          (@OfNat.ofNat α (nat_lit 0)
            (@Zero.toOfNat0 α
              (@Lean.Grind.AddCommMonoid.toZero α
                (@Lean.Grind.NatModule.toAddCommMonoid α
                  (@Lean.Grind.Semiring.toNatModule α
                    (@Lean.Grind.CommSemiring.toSemiring α
                      (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))))))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.inv_zero_eqC.h5.inst (@hc_h (Rat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.instFieldRat) _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))

-- Int.Internal.Linear.eq_le_weaken_neg, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_weaken_neg.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_weaken_neg.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_weaken_neg.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly) (k : Int),
        Int.Internal.Linear.Poly.denote' ctx p₁ = 0 → Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_weaken_neg.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) HypCheckProof.Int.Internal.Linear.eq_le_weaken_neg.h4.prem0)

-- Int.Internal.Linear.eq_le_weaken_neg, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_weaken_neg.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 1) ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_le_weaken_neg.h5.prem0 : Int.Internal.Linear.le_weaken_cert ((Int.Internal.Linear.Poly.num (-1)).mul_k (-1)) (Int.Internal.Linear.Poly.num 1) 0 =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_le_weaken_neg.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly) (k : Int),
        Int.Internal.Linear.le_weaken_cert (p₁.mul_k (-1)) p₂ k = Bool.true → Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_le_weaken_neg.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num (-1)) (Int.Internal.Linear.Poly.num 1) (0) HypCheckProof.Int.Internal.Linear.eq_le_weaken_neg.h5.prem0)

-- Int.Internal.Linear.le_norm_expr, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm_expr.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm_expr.h4.prem0 : Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) ≤
      Int.Internal.Linear.Expr.denote_k (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_norm_expr.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Expr.denote_k ctx lhs ≤ Int.Internal.Linear.Expr.denote_k ctx rhs →
          Int.Internal.Linear.Poly.denote' ctx p ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_norm_expr.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.le_norm_expr.h4.prem0)

-- Int.Internal.Linear.le_norm_expr, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm_expr.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm_expr.h5.prem0 : Int.Internal.Linear.norm_eq_cert (Int.Internal.Linear.Expr.var 0) (Int.Internal.Linear.Expr.num 0)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_norm_expr.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (lhs rhs : Int.Internal.Linear.Expr) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.norm_eq_cert lhs rhs p = Bool.true → Int.Internal.Linear.Poly.denote' ctx p ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_norm_expr.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Expr.var 0) (Int.Internal.Linear.Expr.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.le_norm_expr.h5.prem0)

-- Int.Internal.Linear.eq_coeff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_coeff.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_coeff.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_coeff.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly) (k : Int),
        Int.Internal.Linear.Poly.denote' ctx p = 0 → Int.Internal.Linear.Poly.denote' ctx p' = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_coeff.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) HypCheckProof.Int.Internal.Linear.eq_coeff.h4.prem0)

-- Int.Internal.Linear.eq_coeff, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_coeff.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_coeff.h5.prem0 : Int.Internal.Linear.eq_coeff_cert (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0))
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) 1 =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_coeff.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly) (k : Int),
        Int.Internal.Linear.eq_coeff_cert p p' k = Bool.true → Int.Internal.Linear.Poly.denote' ctx p' = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_coeff.h5.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (1) HypCheckProof.Int.Internal.Linear.eq_coeff.h5.prem0)

-- Int.Internal.Linear.norm_eq_coeff', hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.norm_eq_coeff'.h4.inst : Not
      (Iff
        (@Eq Int
          (Int.Internal.Linear.Poly.denote (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Int.Internal.Linear.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Eq Int
          (Int.Internal.Linear.Poly.denote (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Int.Internal.Linear.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (@OfNat.ofNat Int.Internal.Linear.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (Int.Internal.Linear.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.norm_eq_coeff'.h4.prem0 : @GT.gt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.norm_eq_coeff'.h4 : Not
      (∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly) (k : Int),
        @GT.gt Int Int.instLTInt k (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) →
          Iff (@Eq Int (Int.Internal.Linear.Poly.denote ctx p) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))
            (@Eq Int (Int.Internal.Linear.Poly.denote ctx p') (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := fun hc_h => HypCheckProof.Int.Internal.Linear.norm_eq_coeff'.h4.inst (@hc_h (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Int.Internal.Linear.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Int.Internal.Linear.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Int.Internal.Linear.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (Int.Internal.Linear.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) HypCheckProof.Int.Internal.Linear.norm_eq_coeff'.h4.prem0)

-- Int.Internal.Linear.norm_eq_coeff', hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.norm_eq_coeff'.h5.inst : ¬(Int.Internal.Linear.Poly.denote (Lean.RArray.leaf 1)
            ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).mul 0) =
          0 ↔
        Int.Internal.Linear.Poly.denote (Lean.RArray.leaf 1)
            (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
          0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.norm_eq_coeff'.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly) (k : Int),
        p = p'.mul k → (Int.Internal.Linear.Poly.denote ctx p = 0 ↔ Int.Internal.Linear.Poly.denote ctx p' = 0) := fun hc_h => HypCheckProof.Int.Internal.Linear.norm_eq_coeff'.h5.inst (@hc_h (Lean.RArray.leaf 1) ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).mul 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (0) rfl)

-- Int.Internal.Linear.dvd_norm_poly, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_norm_poly.h4.inst : ¬0 ∣
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_norm_poly.h4.prem0 : 0 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_norm_poly.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (d : Int) (p p' : Int.Internal.Linear.Poly),
        d ∣ Int.Internal.Linear.Poly.denote' ctx p → d ∣ Int.Internal.Linear.Poly.denote' ctx p' := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_norm_poly.h4.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.dvd_norm_poly.h4.prem0)

-- Int.Internal.Linear.dvd_norm_poly, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_norm_poly.h5.inst : ¬0 ∣
        Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_norm_poly.h5.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Int.Internal.Linear.dvd_norm_poly.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (d : Int) (p p' : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p = Int.Internal.Linear.Poly.denote' ctx p' →
          d ∣ Int.Internal.Linear.Poly.denote' ctx p' := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_norm_poly.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.dvd_norm_poly.h5.prem0)

-- Int.Internal.Linear.eq_def, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def.h4.prem0 : Int.Internal.Linear.Var.denote (Lean.RArray.leaf 1) 0 =
      Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_def.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (xPoly p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Var.denote ctx x = Int.Internal.Linear.Poly.denote' ctx xPoly →
          Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_def.h4.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_def.h4.prem0)

-- Int.Internal.Linear.eq_def, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def.h5.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add (-1) 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_def.h5.prem0 : Int.Internal.Linear.eq_def_cert 0 (Int.Internal.Linear.Poly.num 0)
        (Int.Internal.Linear.Poly.add (-1) 0 (Int.Internal.Linear.Poly.num 0)) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_def.h5 : ¬∀ (ctx : Int.Internal.Linear.Context) (x : Int.Internal.Linear.Var) (xPoly p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.eq_def_cert x xPoly p = Bool.true → Int.Internal.Linear.Poly.denote' ctx p = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_def.h5.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add (-1) 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_def.h5.prem0)

-- Lean.Grind.Field.intCast_div_of_dvd, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.intCast_div_of_dvd.h4.inst : Not
      (@Eq Rat
        (@Int.cast Rat
          (@Lean.Grind.Ring.intCast Rat
            (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))
          (@HDiv.hDiv Int Int Int (@instHDiv Int Int.instDiv) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
        (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat (@Lean.Grind.Field.toDiv Rat Lean.Grind.instFieldRat))
          (@Int.cast Rat
            (@Lean.Grind.Ring.intCast Rat
              (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))
            (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Int.cast Rat
            (@Lean.Grind.Ring.intCast Rat
              (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))
            (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.intCast_div_of_dvd.h4.prem0 : @Ne Rat
      (@Int.cast Rat
        (@Lean.Grind.Ring.intCast Rat
          (@Lean.Grind.CommRing.toRing Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))
        (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))))
      (@OfNat.ofNat Rat (nat_lit 0)
        (@Zero.toOfNat0 Rat
          (@Lean.Grind.AddCommMonoid.toZero Rat
            (@Lean.Grind.NatModule.toAddCommMonoid Rat
              (@Lean.Grind.Semiring.toNatModule Rat
                (@Lean.Grind.CommSemiring.toSemiring Rat
                  (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat)))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Field.intCast_div_of_dvd.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α] {x y : Int},
        @Ne α
            (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)))
              y)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@Lean.Grind.AddCommMonoid.toZero α
                  (@Lean.Grind.NatModule.toAddCommMonoid α
                    (@Lean.Grind.Semiring.toNatModule α
                      (@Lean.Grind.CommSemiring.toSemiring α
                        (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))))))) →
          @Eq α
            (@Int.cast α (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst)))
              (@HDiv.hDiv Int Int Int (@instHDiv Int Int.instDiv) x y))
            (@HDiv.hDiv α α α (@instHDiv α (@Lean.Grind.Field.toDiv α inst))
              (@Int.cast α
                (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))) x)
              (@Int.cast α
                (@Lean.Grind.Ring.intCast α (@Lean.Grind.CommRing.toRing α (@Lean.Grind.Field.toCommRing α inst))) y))) := fun hc_h => HypCheckProof.Lean.Grind.Field.intCast_div_of_dvd.h4.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))) HypCheckProof.Lean.Grind.Field.intCast_div_of_dvd.h4.prem0)

-- Lean.Grind.OrderedAdd.neg_nonneg_iff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.neg_nonneg_iff.h4.inst : ¬(0 ≤ -UInt8.ofNat 1 ↔ UInt8.ofNat 1 ≤ 0) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.neg_nonneg_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommGroup M] {a : M}, 0 ≤ -a ↔ a ≤ 0 := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.neg_nonneg_iff.h4.inst (@hc_h (UInt8) (instLEUInt8) _ (Lean.Grind.Ring.toAddCommGroup) (UInt8.ofNat 1))

-- Lean.Grind.AC.Seq.denote_insert, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_insert.h2.inst : ¬Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := Bool.true : PLift Bool })
                (Lean.RArray.leaf { down := Bool.false : PLift Bool }),
            op := fun (a b : Bool) => !(a && b) : Lean.Grind.AC.Context Bool }
          (Lean.Grind.AC.Seq.insert 1 (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0))) =
        {
              vars :=
                Lean.RArray.branch 1 (Lean.RArray.leaf { down := Bool.true : PLift Bool })
                  (Lean.RArray.leaf { down := Bool.false : PLift Bool }),
              op := fun (a b : Bool) => !(a && b) : Lean.Grind.AC.Context Bool }.op
          (Lean.Grind.AC.Var.denote
            {
              vars :=
                Lean.RArray.branch 1 (Lean.RArray.leaf { down := Bool.true : PLift Bool })
                  (Lean.RArray.leaf { down := Bool.false : PLift Bool }),
              op := fun (a b : Bool) => !(a && b) : Lean.Grind.AC.Context Bool }
            1)
          (Lean.Grind.AC.Seq.denote
            {
              vars :=
                Lean.RArray.branch 1 (Lean.RArray.leaf { down := Bool.true : PLift Bool })
                  (Lean.RArray.leaf { down := Bool.false : PLift Bool }),
              op := fun (a b : Bool) => !(a && b) : Lean.Grind.AC.Context Bool }
            (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0))) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_insert.h2.prem0 : Std.Commutative
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := Bool.true : PLift Bool })
              (Lean.RArray.leaf { down := Bool.false : PLift Bool }),
          op := fun (a b : Bool) => !(a && b) : Lean.Grind.AC.Context Bool }.op := (@Std.Commutative.mk _ _ (by (try dsimp only);   decide))
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_insert.h2 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₂ : Std.Commutative ctx.op} (x : Lean.Grind.AC.Var)
        (s : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx (Lean.Grind.AC.Seq.insert x s) =
          ctx.op (Lean.Grind.AC.Var.denote ctx x) (Lean.Grind.AC.Seq.denote ctx s) := fun hc_h => HypCheckProof.Lean.Grind.AC.Seq.denote_insert.h2.inst (@hc_h (Bool) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := Bool.true : PLift Bool })
          (Lean.RArray.leaf { down := Bool.false : PLift Bool }),
      op := fun (a b : Bool) => !(a && b) : Lean.Grind.AC.Context Bool }) HypCheckProof.Lean.Grind.AC.Seq.denote_insert.h2.prem0 (1) (Lean.Grind.AC.Seq.cons 0 (Lean.Grind.AC.Seq.var 0)))

-- Lean.Grind.AC.Seq.denote_insert, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_insert.h3.inst : ¬Lean.Grind.AC.Seq.denote
          {
            vars :=
              Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                (Lean.RArray.leaf { down := 2 : PLift Nat }),
            op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
          (Lean.Grind.AC.Seq.insert 1 (Lean.Grind.AC.Seq.var 0)) =
        {
              vars :=
                Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                  (Lean.RArray.leaf { down := 2 : PLift Nat }),
              op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }.op
          (Lean.Grind.AC.Var.denote
            {
              vars :=
                Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                  (Lean.RArray.leaf { down := 2 : PLift Nat }),
              op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
            1)
          (Lean.Grind.AC.Seq.denote
            {
              vars :=
                Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat })
                  (Lean.RArray.leaf { down := 2 : PLift Nat }),
              op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }
            (Lean.Grind.AC.Seq.var 0)) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_insert.h3.prem0 : Std.Associative
      {
          vars :=
            Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
          op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }.op := (@Std.Associative.mk _ _ (by (try dsimp only);   (intros; simp_all; done)))
theorem HypCheckProof.Lean.Grind.AC.Seq.denote_insert.h3 : ¬∀ {α : Type} (ctx : Lean.Grind.AC.Context α) {inst₁ : Std.Associative ctx.op} (x : Lean.Grind.AC.Var)
        (s : Lean.Grind.AC.Seq),
        Lean.Grind.AC.Seq.denote ctx (Lean.Grind.AC.Seq.insert x s) =
          ctx.op (Lean.Grind.AC.Var.denote ctx x) (Lean.Grind.AC.Seq.denote ctx s) := fun hc_h => HypCheckProof.Lean.Grind.AC.Seq.denote_insert.h3.inst (@hc_h (Nat) ({
      vars :=
        Lean.RArray.branch 1 (Lean.RArray.leaf { down := 1 : PLift Nat }) (Lean.RArray.leaf { down := 2 : PLift Nat }),
      op := fun (a x : Nat) => a : Lean.Grind.AC.Context Nat }) HypCheckProof.Lean.Grind.AC.Seq.denote_insert.h3.prem0 (1) (Lean.Grind.AC.Seq.var 0))

-- Lean.Grind.CommRing.dvd_norm_expr, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.dvd_norm_expr.h8.inst : Not
      (@Eq Prop
        (@Dvd.dvd Int Int.instDvd (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))
        (@Dvd.dvd Int Int.instDvd (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))
          (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.dvd_norm_expr.h8 : Not
      (∀ (ctx : Lean.Grind.CommRing.Context Int) (k : Int) (e e' : Lean.Grind.CommRing.Expr) (k' : Int)
        (q : Lean.Grind.CommRing.Poly) (g c : Int),
        @Eq Prop
          (@Dvd.dvd Int Int.instDvd k
            (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) ctx e))
          (@Dvd.dvd Int Int.instDvd k'
            (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) ctx e'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.dvd_norm_expr.h8.inst (@hc_h (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Lean.Grind.CommRing.le_norm_tight_expr, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_tight_expr.h8.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.le_norm_tight_expr.h8 : Not
      (∀ (ctx : Lean.Grind.CommRing.Context Int) (lhs rhs lhs' rhs' : Lean.Grind.CommRing.Expr)
        (q : Lean.Grind.CommRing.Poly) (k c : Int),
        @Eq Prop
          (@LE.le Int Int.instLEInt
            (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) ctx lhs)
            (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) ctx rhs))
          (@LE.le Int Int.instLEInt
            (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) ctx lhs')
            (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) ctx rhs'))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.le_norm_tight_expr.h8.inst (@hc_h (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Int.Internal.Linear.le_norm_rfl, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm_rfl.h3.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm_rfl.h3.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_norm_rfl.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_norm_rfl.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.le_norm_rfl.h3.prem0)

-- Int.Internal.Linear.le_norm_rfl, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm_rfl.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).norm_k ≤
        0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_norm_rfl.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        p₂ = p₁.norm_k → Int.Internal.Linear.Poly.denote' ctx p₂ ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_norm_rfl.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).norm_k) rfl)

-- Int.Internal.Linear.le_norm_poly, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm_poly.h3.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm_poly.h3.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≤ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.le_norm_poly.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p ≤ 0 → Int.Internal.Linear.Poly.denote' ctx p' ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_norm_poly.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.le_norm_poly.h3.prem0)

-- Int.Internal.Linear.le_norm_poly, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm_poly.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≤
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.le_norm_poly.h4.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Int.Internal.Linear.le_norm_poly.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p = Int.Internal.Linear.Poly.denote' ctx p' →
          Int.Internal.Linear.Poly.denote' ctx p' ≤ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.le_norm_poly.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.le_norm_poly.h4.prem0)

-- Int.Internal.Linear.diseq_norm_rfl, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_norm_rfl.h3.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_norm_rfl.h3.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≠
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_norm_rfl.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ ≠ 0 → Int.Internal.Linear.Poly.denote' ctx p₂ ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_norm_rfl.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.diseq_norm_rfl.h3.prem0)

-- Int.Internal.Linear.diseq_norm_rfl, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_norm_rfl.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0).norm_k ≠ 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_norm_rfl.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        p₂ = p₁.norm_k → Int.Internal.Linear.Poly.denote' ctx p₂ ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_norm_rfl.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ((Int.Internal.Linear.Poly.num 0).norm_k) rfl)

-- Int.Internal.Linear.dvd_unsat, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_unsat.h3.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_unsat.h3.prem0 : 0 ∣ Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_unsat.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (k : Int) (p : Int.Internal.Linear.Poly),
        k ∣ Int.Internal.Linear.Poly.denote' ctx p → False := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_unsat.h3.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.dvd_unsat.h3.prem0)

-- Int.Internal.Linear.dvd_unsat, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_unsat.h4.inst : ¬False := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.dvd_unsat.h4.prem0 : Int.Internal.Linear.Poly.isUnsatDvd_k 0 (Int.Internal.Linear.Poly.num 1) = Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.dvd_unsat.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (k : Int) (p : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.isUnsatDvd_k k p = Bool.true → False := fun hc_h => HypCheckProof.Int.Internal.Linear.dvd_unsat.h4.inst (@hc_h (Lean.RArray.leaf 1) (0) (Int.Internal.Linear.Poly.num 1) HypCheckProof.Int.Internal.Linear.dvd_unsat.h4.prem0)

-- Int.Internal.Linear.diseq_neg, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_neg.h3.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_neg.h3.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ≠
      0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_neg.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p ≠ 0 → Int.Internal.Linear.Poly.denote' ctx p' ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_neg.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.diseq_neg.h3.prem0)

-- Int.Internal.Linear.diseq_neg, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_neg.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) ≠ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.diseq_neg.h4.prem0 : (Int.Internal.Linear.Poly.num 0).beq' ((Int.Internal.Linear.Poly.num 0).mul_k (-1)) = Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.diseq_neg.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p p' : Int.Internal.Linear.Poly),
        p'.beq' (p.mul_k (-1)) = Bool.true → Int.Internal.Linear.Poly.denote' ctx p' ≠ 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.diseq_neg.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.num 0) HypCheckProof.Int.Internal.Linear.diseq_neg.h4.prem0)

-- Int.Internal.Linear.eq_norm, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm.h3.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm.h3.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_norm.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ = 0 → Int.Internal.Linear.Poly.denote' ctx p₂ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_norm.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_norm.h3.prem0)

-- Int.Internal.Linear.eq_norm, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm.h4.prem0 : (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).norm_k.beq'
        (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
      Bool.true := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_norm.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        p₁.norm_k.beq' p₂ = Bool.true → Int.Internal.Linear.Poly.denote' ctx p₂ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_norm.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_norm.h4.prem0)

-- Int.Internal.Linear.eq_norm_rfl, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm_rfl.h3.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) =
        0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm_rfl.h3.prem0 : Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) = 0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_norm_rfl.h3 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        Int.Internal.Linear.Poly.denote' ctx p₁ = 0 → Int.Internal.Linear.Poly.denote' ctx p₂ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_norm_rfl.h3.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.num 0) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) HypCheckProof.Int.Internal.Linear.eq_norm_rfl.h3.prem0)

-- Int.Internal.Linear.eq_norm_rfl, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Int.Internal.Linear.eq_norm_rfl.h4.inst : ¬Int.Internal.Linear.Poly.denote' (Lean.RArray.leaf 1)
          (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).norm_k =
        0 := by
  decide
theorem HypCheckProof.Int.Internal.Linear.eq_norm_rfl.h4 : ¬∀ (ctx : Int.Internal.Linear.Context) (p₁ p₂ : Int.Internal.Linear.Poly),
        p₂ = p₁.norm_k → Int.Internal.Linear.Poly.denote' ctx p₂ = 0 := fun hc_h => HypCheckProof.Int.Internal.Linear.eq_norm_rfl.h4.inst (@hc_h (Lean.RArray.leaf 1) (Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)) ((Int.Internal.Linear.Poly.add 1 0 (Int.Internal.Linear.Poly.num 0)).norm_k) rfl)

-- Lean.Grind.Field.natCast_ne_zero, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Field.natCast_ne_zero.h4.inst : Not
      (@Ne Rat
        (@Nat.cast Rat
          (@Lean.Grind.Semiring.natCast Rat
            (@Lean.Grind.CommSemiring.toSemiring Rat
              (@Lean.Grind.CommRing.toCommSemiring Rat (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat Rat (nat_lit 0)
          (@Zero.toOfNat0 Rat
            (@Lean.Grind.AddCommMonoid.toZero Rat
              (@Lean.Grind.NatModule.toAddCommMonoid Rat
                (@Lean.Grind.Semiring.toNatModule Rat
                  (@Lean.Grind.CommSemiring.toSemiring Rat
                    (@Lean.Grind.CommRing.toCommSemiring Rat
                      (@Lean.Grind.Field.toCommRing Rat Lean.Grind.instFieldRat))))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.Field.natCast_ne_zero.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
        {n : Nat},
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
                      (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst))))))))) := fun hc_h => HypCheckProof.Lean.Grind.Field.natCast_ne_zero.h4.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))

-- Lean.Grind.CommRing.inv_int_eq, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.inv_int_eq.h4.inst : Not
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
theorem HypCheckProof.Lean.Grind.CommRing.inv_int_eq.h4 : Not
      (∀ {α : Type} [inst : Lean.Grind.Field α]
        [inst_1 :
          @Lean.Grind.IsCharP α
            (@Lean.Grind.CommSemiring.toSemiring α
              (@Lean.Grind.CommRing.toCommSemiring α (@Lean.Grind.Field.toCommRing α inst)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))]
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
              (nat_lit 1)))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.inv_int_eq.h4.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))

-- Lean.Grind.CommRing.Stepwise.of_kronOkM_k, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.of_kronOkM_k.h7.inst : ¬((1 < 0 ∧
          (Lean.Grind.CommRing.Poly.num 0).maxDeg_k < 0 ∧
            (Lean.Grind.CommRing.Poly.num 0).maxDeg_k < 0 ∧
              Lean.Grind.CommRing.MList.ok_k 0 Lean.Grind.CommRing.MList.nil = Bool.true) ∧
        2 *
            ((Lean.Grind.CommRing.Poly.num 0).norm1_k + (Lean.Grind.CommRing.Poly.num 0).norm1_k +
                Lean.Grind.CommRing.MList.nil.norm_k +
              0 * (Lean.Grind.CommRing.PPoly.num 0).norm1_k) <
          2 ^ 0) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.of_kronOkM_k.h7 : ¬∀ {K B c : Nat} {p₁ p : Lean.Grind.CommRing.Poly} {E : Lean.Grind.CommRing.PPoly} {ls : Lean.Grind.CommRing.MList},
        (1 < B ∧ p.maxDeg_k < B ∧ p₁.maxDeg_k < B ∧ Lean.Grind.CommRing.MList.ok_k B ls = Bool.true) ∧
          2 * (p.norm1_k + p₁.norm1_k + ls.norm_k + c * E.norm1_k) < 2 ^ K := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.of_kronOkM_k.h7.inst (@hc_h (0) (0) (0) (Lean.Grind.CommRing.Poly.num 0) (Lean.Grind.CommRing.Poly.num 0) (Lean.Grind.CommRing.PPoly.num 0) (Lean.Grind.CommRing.MList.nil))

-- Lean.Grind.CommRing.Stepwise.of_kronOk_k, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.of_kronOk_k.h7.inst : ¬((1 < 0 ∧
          (Lean.Grind.CommRing.Poly.num 0).maxDeg_k < 0 ∧
            (Lean.Grind.CommRing.Poly.num 0).maxDeg_k < 0 ∧
              Lean.Grind.CommRing.KList.ok_k 0 Lean.Grind.CommRing.KList.nil = Bool.true) ∧
        2 *
            ((Lean.Grind.CommRing.Poly.num 0).norm1_k + (Lean.Grind.CommRing.Poly.num 0).norm1_k +
                Lean.Grind.CommRing.KList.nil.norm_k +
              0 * (Lean.Grind.CommRing.PPoly.num 0).norm1_k) <
          2 ^ 0) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.of_kronOk_k.h7 : ¬∀ {K B c : Nat} {p₁ p : Lean.Grind.CommRing.Poly} {E : Lean.Grind.CommRing.PPoly} {ls : Lean.Grind.CommRing.KList},
        (1 < B ∧ p.maxDeg_k < B ∧ p₁.maxDeg_k < B ∧ Lean.Grind.CommRing.KList.ok_k B ls = Bool.true) ∧
          2 * (p.norm1_k + p₁.norm1_k + ls.norm_k + c * E.norm1_k) < 2 ^ K := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.of_kronOk_k.h7.inst (@hc_h (0) (0) (0) (Lean.Grind.CommRing.Poly.num 0) (Lean.Grind.CommRing.Poly.num 0) (Lean.Grind.CommRing.PPoly.num 0) (Lean.Grind.CommRing.KList.nil))

-- Lean.Grind.CommRing.Stepwise.of_impOk_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.of_impOk_k.h6.inst : ¬((1 < 0 ∧ (Lean.Grind.CommRing.Expr.num 0).degB_k < 0 ∧ (Lean.Grind.CommRing.Poly.num 0).maxDeg_k < 0) ∧
        2 *
            ((Lean.Grind.CommRing.Expr.num 0).majorant_k + (Lean.Grind.CommRing.Poly.num 0).norm1_k +
              0 * (Lean.Grind.CommRing.PPoly.num 0).norm1_k) <
          2 ^ 0) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Stepwise.of_impOk_k.h6 : ¬∀ {K B c : Nat} {e : Lean.Grind.CommRing.Expr} {p : Lean.Grind.CommRing.Poly} {E : Lean.Grind.CommRing.PPoly},
        (1 < B ∧ e.degB_k < B ∧ p.maxDeg_k < B) ∧ 2 * (e.majorant_k + p.norm1_k + c * E.norm1_k) < 2 ^ K := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Stepwise.of_impOk_k.h6.inst (@hc_h (0) (0) (0) (Lean.Grind.CommRing.Expr.num 0) (Lean.Grind.CommRing.Poly.num 0) (Lean.Grind.CommRing.PPoly.num 0))

-- Lean.Grind.Linarith.Poly.denoteN_add, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Linarith.Poly.denoteN_add.h6.inst : Not
      (@Eq Int
        (@Lean.Grind.Linarith.Poly.denoteN Int
          (@Lean.Grind.Semiring.toNatModule Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.Linarith.Poly.add
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
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
            (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))).toNat
            (@Lean.Grind.Linarith.Var.denote Int
              (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
          (@Lean.Grind.Linarith.Poly.denoteN Int
            (@Lean.Grind.Semiring.toNatModule Int
              (@Lean.Grind.CommSemiring.toSemiring Int
                (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))
            (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
              (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil)))) := by
  decide
theorem HypCheckProof.Lean.Grind.Linarith.Poly.denoteN_add.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.NatModule α] (ctx : Lean.Grind.Linarith.Context α) (k : Int)
        (x : Lean.Grind.Linarith.Var) (p : Lean.Grind.Linarith.Poly),
        @Eq α (@Lean.Grind.Linarith.Poly.denoteN α inst ctx (Lean.Grind.Linarith.Poly.add k x p))
          (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.AddCommMonoid.toAdd α (@Lean.Grind.NatModule.toAddCommMonoid α inst)))
            (@HSMul.hSMul Nat α α (@instHSMul Nat α (@Lean.Grind.NatModule.nsmul α inst)) k.toNat
              (@Lean.Grind.Linarith.Var.denote α ctx x))
            (@Lean.Grind.Linarith.Poly.denoteN α inst ctx p))) := fun hc_h => HypCheckProof.Lean.Grind.Linarith.Poly.denoteN_add.h6.inst (@hc_h (Int) (@Lean.Grind.Semiring.toNatModule Int
      (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt))) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Lean.Grind.Linarith.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (@OfNat.ofNat Lean.Grind.Linarith.Var (nat_lit 0) (instOfNatNat (nat_lit 0))) Lean.Grind.Linarith.Poly.nil))

-- Lean.Grind.CommRing.Expr.denote_powLeafB_k, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_powLeafB_k.h6.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).add
                (Lean.Grind.CommRing.Expr.var
                  (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1))))).powLeafB_k
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_powLeafB_k.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (a : Lean.Grind.CommRing.Expr)
        (k : Nat) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (a.powLeafB_k k p))
          (@HPow.hPow α Nat α
            (@Lean.Grind.Semiring.npow α
              (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))
            (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx a) k)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_powLeafB_k.h6.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) ((Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)))).add
      (Lean.Grind.CommRing.Expr.var (@OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))

-- Lean.Grind.CommRing.Poly.denote_powC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_powC.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
                (Lean.Grind.CommRing.Mon.mult
                  { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                    k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
                  Lean.Grind.CommRing.Mon.unit)
                (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))).powC
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HPow.hPow Int Nat Int
          (@Lean.Grind.Semiring.npow Int
            (@Lean.Grind.CommSemiring.toSemiring Int (@Lean.Grind.CommRing.toCommSemiring Int Lean.Grind.instCommRingInt)))
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
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_powC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α)
        (p : Lean.Grind.CommRing.Poly) (k : Nat),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx (p.powC k c))
          (@HPow.hPow α Nat α
            (@Lean.Grind.Semiring.npow α
              (@Lean.Grind.CommSemiring.toSemiring α (@Lean.Grind.CommRing.toCommSemiring α inst)))
            (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p) k)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_powC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))

-- Lean.Grind.CommRing.Expr.denote_eq_of_toPolyX, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_eq_of_toPolyX.h6.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Expr.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
            (Lean.Grind.CommRing.Mon.mult
              { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
                k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
              Lean.Grind.CommRing.Mon.unit)
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))) := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.denote_eq_of_toPolyX.h6 : Not
      (∀ {α : Type} [inst : Lean.Grind.CommRing α] (ctx : Lean.Grind.CommRing.Context α) (bal : Bool)
        (e : Lean.Grind.CommRing.Expr) (p : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Expr.denote α (@Lean.Grind.CommRing.toRing α inst) ctx e)
          (@Lean.Grind.CommRing.Poly.denote α (@Lean.Grind.CommRing.toRing α inst) ctx p)) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.denote_eq_of_toPolyX.h6.inst (@hc_h (Int) (Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Bool.false) (Lean.Grind.CommRing.Expr.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.add (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
      (Lean.Grind.CommRing.Mon.mult
        { x := @OfNat.ofNat Lean.Grind.CommRing.Var (nat_lit 0) (instOfNatNat (nat_lit 0)),
          k := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : Lean.Grind.CommRing.Power }
        Lean.Grind.CommRing.Mon.unit)
      (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))))

-- Lean.Grind.CommRing.Poly.denote_combineC, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_combineC.h3.inst : Not
      (@Eq Int
        (@Lean.Grind.CommRing.Poly.denote Int (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt)
          (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          ((Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))).combineC
            (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
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
theorem HypCheckProof.Lean.Grind.CommRing.Poly.denote_combineC.h3 : Not
      (∀ {α : Type} {c : Nat} [inst : Lean.Grind.Ring α] (ctx : Lean.Grind.CommRing.Context α)
        (p₁ p₂ : Lean.Grind.CommRing.Poly),
        @Eq α (@Lean.Grind.CommRing.Poly.denote α inst ctx (p₁.combineC p₂ c))
          (@HAdd.hAdd α α α (@instHAdd α (@Lean.Grind.Semiring.toAdd α (@Lean.Grind.Ring.toSemiring α inst)))
            (@Lean.Grind.CommRing.Poly.denote α inst ctx p₁) (@Lean.Grind.CommRing.Poly.denote α inst ctx p₂))) := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Poly.denote_combineC.h3.inst (@hc_h (Int) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Lean.Grind.CommRing.toRing Int Lean.Grind.instCommRingInt) (@Lean.RArray.leaf Int (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Lean.Grind.CommRing.Poly.num (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))))

