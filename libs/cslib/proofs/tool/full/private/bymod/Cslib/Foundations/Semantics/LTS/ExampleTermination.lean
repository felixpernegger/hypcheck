import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Cslib.Foundations.Semantics.LTS.ExampleTermination.0.Cslib.LTS.Example.successorLTS_transGen_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.LTS.Example.successorLTS_transGen_lt.h2 : ¬∀ {n m : ℕ}, n < m := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

