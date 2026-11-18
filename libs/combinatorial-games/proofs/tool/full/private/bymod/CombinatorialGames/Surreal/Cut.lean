import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.CombinatorialGames.Surreal.Cut.0.Surreal.Cut.simplestBtwn_spec, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.simplestBtwn_spec.h2 : ¬∀ {x y : Surreal.Cut.{0}}, LT.lt.{1} x y := fun hc_h => absurd (@hc_h (Bot.bot.{1}) (Bot.bot.{1})) (by
  simp)

