import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.CombinatorialGames.NatOrdinal.Pow.0.NatOrdinal.wpow_mul_natCast_add_of_lt_aux, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.wpow_mul_natCast_add_of_lt_aux.h2 : ¬∀ {x y : NatOrdinal.{0}} (n : ℕ),
        (∀ (z : NatOrdinal.{0}), LT.lt.{1} z (Wpow.wpow.{1} x) → LT.lt.{1} (HAdd.hAdd.{1, 1, 1} z y) (Wpow.wpow.{1} x)) ∧
          Eq.{2} (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} (Wpow.wpow.{1} x) ↑n) y)
            (NatOrdinal.of.{0}
              (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} (HPow.hPow.{1, 1, 1} Ordinal.omega0.{0} (NatOrdinal.val.{0} x)) ↑n)
                (NatOrdinal.val.{0} y))) := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  simp)

