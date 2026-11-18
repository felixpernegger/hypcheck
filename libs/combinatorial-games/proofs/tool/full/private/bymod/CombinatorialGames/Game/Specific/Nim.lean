import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.CombinatorialGames.Game.Specific.Nim.0.IGame.nim_fuzzy_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.nim_fuzzy_of_lt.h2 : Not
      (∀ {a b : Nimber.{0}},
        @IncompRel.{1} IGame.{0} (fun (x1 x2 : IGame.{0}) => @LE.le.{1} IGame.{0} IGame.instLE.{0} x1 x2) (IGame.nim.{0} a)
          (IGame.nim.{0} b)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat.{1} Nimber.{0} (nat_lit 0) (@Zero.toOfNat0.{1} Nimber.{0} instZeroNimber.{0})) (@OfNat.ofNat.{1} Nimber.{0} (nat_lit 0) (@Zero.toOfNat0.{1} Nimber.{0} instZeroNimber.{0}))) (by
  simp)

