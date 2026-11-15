import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Cslib.Algorithms.Lean.Query.Sort.LowerBound.0.Cslib.Query.finPrefix_natEmbedding_finVal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Query.finPrefix_natEmbedding_finVal.h2 : ¬∀ {n : ℕ} {α : Type} (i : Fin n), ↑n ≤ Cardinal.mk α := fun hc_h => absurd (@hc_h (3) (Bool) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3))) (by
  norm_num)

-- _private.Cslib.Algorithms.Lean.Query.Sort.LowerBound.0.Cslib.Query.map_finEmbedding_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Query.map_finEmbedding_injective.h2 : ¬∀ {n : ℕ} {α : Type}, ↑n ≤ Cardinal.mk α := fun hc_h => absurd (@hc_h (3) (Bool)) (by
  norm_num)

-- _private.Cslib.Algorithms.Lean.Query.Sort.LowerBound.0.Cslib.Query.finPrefix_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Query.finPrefix_injective.h2 : ¬∀ {n : ℕ} {α : Type}, ↑n ≤ Cardinal.mk α := fun hc_h => absurd (@hc_h (3) (Bool)) (by
  norm_num)

