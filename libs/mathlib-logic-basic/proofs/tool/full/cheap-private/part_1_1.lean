import HCImportsM

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.Mathlib.Basic.ENNReal.Inv.0.ENNReal.exists_lt_mul_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_lt_mul_left.h3 : ¬∀ {a b c : ENNReal}, ∃ a' < a, c < a' * b := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

