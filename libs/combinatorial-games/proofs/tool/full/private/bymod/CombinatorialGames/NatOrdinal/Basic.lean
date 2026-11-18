import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.CombinatorialGames.NatOrdinal.Basic.0.NatOrdinal.mul_add_lt₃', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.mul_add_lt₃'.h6 : ¬∀ {a b c a' b' c' : NatOrdinal.{0}},
        LT.lt.{1} b' b →
          LT.lt.{1} c' c →
            LT.lt.{1}
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b c))
                    (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b' c)))
                  (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b c')))
                (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b' c')))
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b c))
                    (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b' c)))
                  (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b c')))
                (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b' c'))) := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (0) (0) (by
  simp) (by
  simp)) (by
  simp)

-- _private.CombinatorialGames.NatOrdinal.Basic.0.NatOrdinal.mul_add_lt₃', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.mul_add_lt₃'.h7 : ¬∀ {a b c a' b' c' : NatOrdinal.{0}},
        LT.lt.{1} a' a →
          LT.lt.{1} c' c →
            LT.lt.{1}
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b c))
                    (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b' c)))
                  (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b c')))
                (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b' c')))
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b c))
                    (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b' c)))
                  (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b c')))
                (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b' c'))) := fun hc_h => absurd (@hc_h (1) (0) (1) (0) (0) (0) (by
  simp) (by
  simp)) (by
  simp)

-- _private.CombinatorialGames.NatOrdinal.Basic.0.NatOrdinal.mul_add_lt₃', hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.mul_add_lt₃'.h8 : ¬∀ {a b c a' b' c' : NatOrdinal.{0}},
        LT.lt.{1} a' a →
          LT.lt.{1} b' b →
            LT.lt.{1}
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b c))
                    (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b' c)))
                  (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b c')))
                (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b' c')))
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b c))
                    (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b' c)))
                  (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b c')))
                (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b' c'))) := fun hc_h => absurd (@hc_h (1) (1) (0) (0) (0) (0) (by
  simp) (by
  simp)) (by
  simp)

