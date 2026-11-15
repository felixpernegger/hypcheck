import HCImportsM

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.Mathlib.Basic.ENNReal.Inv.0.ENNReal.exists_lt_mul_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_lt_mul_right.h3 : ¬∀ {a b c : ENNReal}, ∃ b' < b, c < a * b' := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- _private.Mathlib.Basic.NNReal.Defs.0.NNReal.Bound.coe_lt_coe_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.Bound.coe_lt_coe_of_lt.h2 : ¬∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

