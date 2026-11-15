import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Mathlib.Data.Nat.PadicValNat.0.Nat.pow_dvd_iff_le_of_spec, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_dvd_iff_le_of_spec.h5 : ¬∀ {p k n a b : ℕ}, p ^ a * b = n → ¬p ∣ b → (p ^ k ∣ n ↔ k ≤ a) := fun hc_h => absurd (@hc_h (0) (2) _ (1) (1) rfl (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.Nat.PadicValNat.0.Nat.pow_dvd_iff_le_of_spec, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_dvd_iff_le_of_spec.h6 : ¬∀ {p k n a b : ℕ}, 1 < p → ¬p ∣ b → (p ^ k ∣ n ↔ k ≤ a) := fun hc_h => absurd (@hc_h (2) (1) (0) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Mathlib.Data.Nat.PadicValNat.0.Nat.pow_dvd_iff_le_of_spec, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_dvd_iff_le_of_spec.h7 : ¬∀ {p k n a b : ℕ}, 1 < p → p ^ a * b = n → (p ^ k ∣ n ↔ k ≤ a) := fun hc_h => absurd (@hc_h (2) (1) _ (0) (0) (by
  decide) rfl) (by
  decide +kernel)

