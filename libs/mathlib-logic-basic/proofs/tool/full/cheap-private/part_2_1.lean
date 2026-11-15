import HCImportsM

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.Mathlib.Basic.NNReal.Defs.0.NNReal.Bound.coe_pos_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.Bound.coe_pos_of_pos.h1 : ¬∀ {r : NNReal}, 0 < ↑r := fun hc_h => absurd (@hc_h (0)) (by
  simp)

