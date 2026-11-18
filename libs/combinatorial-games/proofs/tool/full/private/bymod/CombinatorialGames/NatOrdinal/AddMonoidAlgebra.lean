import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.CombinatorialGames.NatOrdinal.AddMonoidAlgebra.0.Ordinal.CNF.coeff_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordinal.CNF.coeff_lt.h1 : ¬∀ {b : Ordinal.{0}} (o e : Ordinal.{0}), LT.lt.{1} ((Ordinal.CNF.coeff.{0} b o) e) b := fun hc_h => absurd (@hc_h ((0 : Ordinal) : Ordinal.{0}) ((0 : Ordinal) : Ordinal.{0}) ((0 : Ordinal) : Ordinal.{0})) (by
  simp)

