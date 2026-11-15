import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Mathlib.Data.Nat.Log.0.Nat.log.go_aux, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log.go_aux.h3 : ¬∀ {n b fuel : ℕ}, b ≤ n → n < (b * b) ^ fuel := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.Nat.Log.0.Nat.log.go_aux, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log.go_aux.h4 : ¬∀ {n b fuel : ℕ}, n < b ^ (fuel + 1) → n < (b * b) ^ fuel := fun hc_h => absurd (@hc_h (1) (2) (0) (by
  decide)) (by
  decide +kernel)

