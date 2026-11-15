import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Mathlib.Data.EReal.Operations.0.EReal.exists_lt_add_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.exists_lt_add_left.h3 : ¬∀ {a b c : EReal}, ∃ a' < a, c < a' + b := fun hc_h => absurd (@hc_h (0) (⊥) (0)) (by
  simp)

