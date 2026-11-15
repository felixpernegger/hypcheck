import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Cslib.Computability.Circuit.Boolean.Lupanov.0.Cslib.Circuits.Boolean.Lupanov.mainTerm_le, hypothesis 2: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Cslib.Circuits.Boolean.Lupanov.mainTerm_le.h2.gneg : ∀ (P n : ℕ),
      ¬5 * n.log2 < n →
        (P + 1) * (5 * n.log2) ≤ n →
          P * n * ((2 ^ (3 * n.log2) / (n - 5 * n.log2) + 1) * 2 ^ (n - 3 * n.log2)) ≤
            (P + 1) * 2 ^ n + (P + 1) * n * 2 ^ (n - 3 * n.log2) := by
  (intros; grind)
theorem HypCheckProof.Cslib.Circuits.Boolean.Lupanov.mainTerm_le.h2 : ∀ (P n : ℕ),
      (P + 1) * (5 * n.log2) ≤ n →
        P * n * ((2 ^ (3 * n.log2) / (n - 5 * n.log2) + 1) * 2 ^ (n - 3 * n.log2)) ≤
          (P + 1) * 2 ^ n + (P + 1) * n * 2 ^ (n - 3 * n.log2) := by
  intro hc_x0 hc_x1 hc_x3
  exact Classical.byCases (fun hc_h => @Cslib.Circuits.Boolean.Lupanov.mainTerm_le hc_x0 hc_x1 hc_h hc_x3) (fun hc_hn => @HypCheckProof.Cslib.Circuits.Boolean.Lupanov.mainTerm_le.h2.gneg hc_x0 hc_x1 hc_hn hc_x3)

-- _private.Cslib.Computability.Circuit.Boolean.Lupanov.0.Cslib.Circuits.Boolean.Lupanov.mainTerm_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Circuits.Boolean.Lupanov.mainTerm_le.h3 : ¬∀ (P n : ℕ),
        5 * n.log2 < n →
          P * n * ((2 ^ (3 * n.log2) / (n - 5 * n.log2) + 1) * 2 ^ (n - 3 * n.log2)) ≤
            (P + 1) * 2 ^ n + (P + 1) * n * 2 ^ (n - 3 * n.log2) := fun hc_h => absurd (@hc_h (1) (32) (by
  decide)) (by
  decide +kernel)

-- _private.Cslib.Computability.Circuit.Boolean.Lupanov.0.Cslib.Circuits.Boolean.Lupanov.bound_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Circuits.Boolean.Lupanov.bound_le.h1 : ¬∀ (n : ℕ),
        Cslib.Circuits.Boolean.Lupanov.bound (3 * n.log2) (n - 3 * n.log2) (n - 5 * n.log2) ≤
          (2 ^ (3 * n.log2) / (n - 5 * n.log2) + 1) * 2 ^ (n - 3 * n.log2) + 3 * n ^ 4 + 16 * n * 2 ^ (n - 3 * n.log2) := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- _private.Cslib.Computability.Circuit.Boolean.Lupanov.0.Cslib.Circuits.Boolean.Lupanov.error_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Circuits.Boolean.Lupanov.error_le.h2 : ¬∀ (c n : ℕ), 3 * n.log2 ≤ n → c * n ^ 2 * 2 ^ (n - 3 * n.log2) ≤ 2 ^ n := fun hc_h => absurd (@hc_h (2) (1) (by
  decide)) (by
  decide +kernel)

