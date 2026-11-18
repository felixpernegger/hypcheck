import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.CombinatorialGames.Surreal.Leading.0.Surreal.leadingTerm_mono', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.leadingTerm_mono'.h3 : ¬∀ {x y : Surreal.{0}}, LE.le.{1} 0 x → LE.le.{1} (Surreal.leadingTerm.{0} x) (Surreal.leadingTerm.{0} y) := fun hc_h => absurd (@hc_h ((1 : Surreal) : Surreal.{0}) ((0 : Surreal) : Surreal.{0}) (by
  simp)) (by
  simp)

-- _private.CombinatorialGames.Surreal.Leading.0.Surreal.leadingCoeff_nonpos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.leadingCoeff_nonpos.h1 : ¬∀ {x : Surreal.{0}}, LE.le.{0} (Surreal.leadingCoeff.{0} x) 0 := fun hc_h => absurd (@hc_h ((1 : Surreal) : Surreal.{0})) (by
  simp)

-- _private.CombinatorialGames.Surreal.Leading.0.Surreal.leadingCoeff_nonneg, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.leadingCoeff_nonneg.h1 : ¬∀ {x : Surreal.{0}}, LE.le.{0} 0 (Surreal.leadingCoeff.{0} x) := fun hc_h => absurd (@hc_h ((-1 : Surreal) : Surreal.{0})) (by
  simp)

