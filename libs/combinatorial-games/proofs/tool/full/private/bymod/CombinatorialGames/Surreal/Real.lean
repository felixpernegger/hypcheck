import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.CombinatorialGames.Surreal.Real.0.Real.mulOption_lt_toIGame, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.mulOption_lt_toIGame.h4 : ¬∀ {x : ℝ} {q r s : ℚ}, LT.lt.{1} (IGame.mulOption.{0} ↑x ↑q ↑r ↑s) ↑(HMul.hMul.{0, 0, 0} x ↑q) := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) (0) (0) (0)) (by
  simp)

-- _private.CombinatorialGames.Surreal.Real.0.Real.toIGame_lt_mulOption, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toIGame_lt_mulOption.h4 : ¬∀ {x : ℝ} {q r s : ℚ}, LT.lt.{1} (↑(HMul.hMul.{0, 0, 0} x ↑q)) (IGame.mulOption.{0} ↑x ↑q ↑r ↑s) := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) (0) (0) (0)) (by
  simp)

