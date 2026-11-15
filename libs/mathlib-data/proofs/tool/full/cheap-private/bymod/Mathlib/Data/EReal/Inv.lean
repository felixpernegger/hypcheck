import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Mathlib.Data.EReal.Inv.0.EReal.exists_lt_mul_left_of_nonneg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.exists_lt_mul_left_of_nonneg.h5 : ¬∀ {a b c : EReal}, 0 ≤ a → 0 ≤ c → ∃ a' ∈ Set.Ioo 0 a, c < a' * b := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  rfl) (by
  rfl)) (by
  simp)

-- _private.Mathlib.Data.EReal.Inv.0.EReal.exists_mul_left_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.exists_mul_left_lt.h5 : ¬∀ {a b c : EReal}, a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊤ ∨ 0 < b → ∃ a' ∈ Set.Ioo a ⊤, a' * b < c := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  simp) (by
  decide)) (by
  simp)

-- _private.Mathlib.Data.EReal.Inv.0.EReal.exists_mul_right_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.exists_mul_right_lt.h5 : ¬∀ {a b c : EReal}, 0 < a ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ 0 → ∃ b' ∈ Set.Ioo b ⊤, a * b' < c := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  simp) (by
  decide)) (by
  simp)

-- _private.Mathlib.Data.EReal.Inv.0.EReal.exists_lt_mul_right_of_nonneg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.exists_lt_mul_right_of_nonneg.h5 : ¬∀ {a b c : EReal}, 0 ≤ a → 0 ≤ c → ∃ b' ∈ Set.Ioo 0 b, c < a * b' := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  rfl) (by
  rfl)) (by
  simp)

