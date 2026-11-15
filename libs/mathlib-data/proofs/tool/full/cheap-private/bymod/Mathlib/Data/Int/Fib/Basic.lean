import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Mathlib.Data.Int.Fib.Basic.0.Int.fib_natCast_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.fib_natCast_dvd.h2 : ¬∀ {m : ℕ} {n : ℤ}, Int.fib ↑m ∣ Int.fib n := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

