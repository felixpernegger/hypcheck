import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.CombinatorialGames.Surreal.Division.0.mulOption_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.mulOption_le.h7 : ¬∀ (x y : IGame.{0}) {a b : IGame.{0}} [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} a]
        [inst : IGame.Numeric.{0} b], LE.le.{1} b y → LE.le.{1} (IGame.mulOption.{0} x y a b) (HMul.hMul.{1, 1, 1} x b) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ _ (by
  simp)) (by
  simp)

