import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Cslib.Algorithms.Lean.Query.Sort.Merge.Lemmas.0.Cslib.Query.mergeSort_bound, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Query.mergeSort_bound.h1 : ¬∀ (n : ℕ),
        (n + 1) / 2 * Nat.clog 2 ((n + 1) / 2) + (n / 2 * Nat.clog 2 (n / 2) + ((n + 1) / 2 + n / 2)) ≤ n * Nat.clog 2 n := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

