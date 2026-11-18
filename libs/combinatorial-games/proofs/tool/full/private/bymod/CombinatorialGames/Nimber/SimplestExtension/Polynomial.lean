import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.CombinatorialGames.Nimber.SimplestExtension.Polynomial.0.Nimber.leastNoRoots_mem, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.leastNoRoots_mem.h1 : ¬∀ {x : Nimber.{0}}, Ne.{2} (Nimber.leastNoRoots.{0} x) Top.top.{1} := fun hc_h => absurd (@hc_h (0)) (by
  simp)

