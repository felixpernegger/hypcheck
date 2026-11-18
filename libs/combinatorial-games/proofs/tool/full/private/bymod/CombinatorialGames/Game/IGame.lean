import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.CombinatorialGames.Game.IGame.0.IGame.add_le_add_left', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.add_le_add_left'.h2 : ¬∀ {x y : IGame.{0}} (z : IGame.{0}), LE.le.{1} (HAdd.hAdd.{1, 1, 1} z x) (HAdd.hAdd.{1, 1, 1} z y) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- _private.CombinatorialGames.Game.IGame.0.IGame.add_le_add_right', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.add_le_add_right'.h2 : ¬∀ {x y : IGame.{0}} (z : IGame.{0}), LE.le.{1} (HAdd.hAdd.{1, 1, 1} x z) (HAdd.hAdd.{1, 1, 1} y z) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- _private.CombinatorialGames.Game.IGame.0.IGame.le_trans', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.le_trans'.h3 : ¬∀ {x y z : IGame.{0}}, LE.le.{1} y z → LE.le.{1} x z := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  rfl)) (by
  simp)

-- _private.CombinatorialGames.Game.IGame.0.IGame.le_trans', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.le_trans'.h4 : ¬∀ {x y z : IGame.{0}}, LE.le.{1} x y → LE.le.{1} x z := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  rfl)) (by
  simp)

