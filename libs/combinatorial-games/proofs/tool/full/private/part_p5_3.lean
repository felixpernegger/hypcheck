import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.CombinatorialGames.Nimber.NatOrdinal.0.Nimber.two_opow_log_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.two_opow_log_lt.h1 : ¬∀ {a : Ordinal.{0}}, LT.lt.{1} (HPow.hPow.{1, 1, 1} 2 (Ordinal.log.{0} 2 a)) a := fun hc_h => absurd (@hc_h ((0 : Ordinal) : Ordinal.{0})) (by
  simp)

-- _private.CombinatorialGames.Surreal.Leading.0.Surreal.leadingCoeff_nonpos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.leadingCoeff_nonpos.h1 : ¬∀ {x : Surreal.{0}}, LE.le.{0} (Surreal.leadingCoeff.{0} x) 0 := fun hc_h => absurd (@hc_h ((1 : Surreal) : Surreal.{0})) (by
  simp)

-- _private.CombinatorialGames.Surreal.Leading.0.Surreal.leadingCoeff_nonneg, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.leadingCoeff_nonneg.h1 : ¬∀ {x : Surreal.{0}}, LE.le.{0} 0 (Surreal.leadingCoeff.{0} x) := fun hc_h => absurd (@hc_h ((-1 : Surreal) : Surreal.{0})) (by
  simp)

