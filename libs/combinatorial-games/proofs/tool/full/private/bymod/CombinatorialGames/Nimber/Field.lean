import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.CombinatorialGames.Nimber.Field.0.Nimber.add_ne_zero_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.add_ne_zero_of_lt.h2 : ¬∀ {a b : Nimber.{0}}, Ne.{2} (HAdd.hAdd.{1, 1, 1} a b) 0 := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

