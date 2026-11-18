import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.CombinatorialGames.Game.IGame.0.IGame.add_le_add_left', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.add_le_add_left'.h2 : ¬∀ {x y : IGame.{0}} (z : IGame.{0}), LE.le.{1} (HAdd.hAdd.{1, 1, 1} z x) (HAdd.hAdd.{1, 1, 1} z y) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- _private.CombinatorialGames.Game.Loopy.IGame.0.IGame.toLGame'_inj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.toLGame'_inj.h2 : ¬∀ {x y : IGame.{0}}, Eq.{2} x y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  simp)

-- _private.CombinatorialGames.Surreal.Cut.0.Surreal.Cut.simplestBtwn_spec, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.simplestBtwn_spec.h2 : ¬∀ {x y : Surreal.Cut.{0}}, LT.lt.{1} x y := fun hc_h => absurd (@hc_h (Bot.bot.{1}) (Bot.bot.{1})) (by
  simp)

-- _private.CombinatorialGames.Surreal.Dyadic.0.Dyadic.numeric_upper, hypothesis 1: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.numeric_upper.h1.gneg.{u} : ∀ (x : Dyadic), ¬IGame.Numeric.{u} ↑x → IGame.Numeric.{u} ↑x.upper := by
  (intros; infer_instance)
theorem HypCheckProof.Dyadic.numeric_upper.h1.{u} : ∀ (x : Dyadic), IGame.Numeric.{u} ↑x.upper := by
  intro hc_x0
  exact Classical.byCases (fun hc_h => @Dyadic.numeric_upper hc_x0 hc_h) (fun hc_hn => @HypCheckProof.Dyadic.numeric_upper.h1.gneg hc_x0 hc_hn)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.numeric_upper.h1.derivable.{u} : ∀ (x : Dyadic), IGame.Numeric.{u} ↑x := by
  (intros; infer_instance)

