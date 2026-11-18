import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.CombinatorialGames.Mathlib.EtaSet.0.Order.IsEta.card_subtype_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Order.IsEta.card_subtype_lt.h2 : ¬∀ {δ : Type} {t : δ → δ → Prop} (x : δ), IsWellOrder δ t := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (0)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toTrichotomous.trichotomous (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

