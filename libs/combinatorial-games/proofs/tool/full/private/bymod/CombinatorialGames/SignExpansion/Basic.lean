import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.CombinatorialGames.SignExpansion.Basic.0.SignExpansion.nonempty_of_not_isUpperSet, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignExpansion.nonempty_of_not_isUpperSet.h1 : ¬∀ {f : NatOrdinal.{0} → SignType},
        Set.Nonempty.{1} (Set.preimage.{1, 0} f (Singleton.singleton.{0, 0} 0)) ∧
          Set.Nonempty.{1}
            (Set.ofPred.{1} fun (b : NatOrdinal.{0}) =>
              LT.lt.{1} (InfSet.sInf.{1} (Set.preimage.{1, 0} f (Singleton.singleton.{0, 0} 0))) b ∧ Ne.{1} (f b) 0) := fun hc_h => absurd (@hc_h (fun (a : NatOrdinal.{0}) => SignType.zero)) (by
  simp)

