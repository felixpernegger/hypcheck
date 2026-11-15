import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- ISize.ne_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.ISize.ne_of_lt.h2 : ¬∀ {a b : ISize}, a ≠ b := by
  (simp_all; done)

-- USize.ne_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.USize.ne_of_lt.h2 : ¬∀ {a b : USize}, a ≠ b := by
  (simp_all; done)

