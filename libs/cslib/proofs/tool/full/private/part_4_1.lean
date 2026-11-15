import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.Cslib.Algorithms.Lean.Query.Sort.LowerBound.0.Cslib.Query.map_finEmbedding_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Query.map_finEmbedding_injective.h2 : ¬∀ {n : ℕ} {α : Type}, ↑n ≤ Cardinal.mk α := fun hc_h => absurd (@hc_h (3) (Bool)) (by
  norm_num)

-- _private.Cslib.Computability.Circuit.Boolean.Lupanov.0.Cslib.Circuits.Boolean.Lupanov.bound_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Circuits.Boolean.Lupanov.bound_le.h1 : ¬∀ (n : ℕ),
        Cslib.Circuits.Boolean.Lupanov.bound (3 * n.log2) (n - 3 * n.log2) (n - 5 * n.log2) ≤
          (2 ^ (3 * n.log2) / (n - 5 * n.log2) + 1) * 2 ^ (n - 3 * n.log2) + 3 * n ^ 4 + 16 * n * 2 ^ (n - 3 * n.log2) := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

