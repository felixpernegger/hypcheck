import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.CombinatorialGames.Nimber.SimplestExtension.Basic.0.Nimber.inv_lt_of_not_isField_aux, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.inv_lt_of_not_isField_aux.h1 : ¬∀ {x : Nimber.{0}},
        ¬Nimber.IsField.{0} x →
          LT.lt.{1} (Inv.inv.{1} x) x ∧ ∀ (y : Nimber.{0}), LT.lt.{1} y (Inv.inv.{1} x) → LT.lt.{1} (Inv.inv.{1} y) x := fun hc_h => absurd (@hc_h (0) (by
  aesop)) (by
  simp)

