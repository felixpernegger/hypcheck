import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Mathlib.Data.Nat.Fib.Zeckendorf.0.Nat.zeckendorf_aux, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.zeckendorf_aux.h1 : ¬∀ {m : ℕ}, m - Nat.fib m.greatestFib < m := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

