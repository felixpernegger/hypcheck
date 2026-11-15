import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Cslib.Computability.Circuit.Boolean.LupanovConstruction.0.Cslib.Circuits.Boolean.Lupanov.table_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Cslib.Circuits.Boolean.Lupanov.table_eq.h4 : ¬∀ {k d s : ℕ} (f : Cslib.BooleanFunction (k + d)), Cslib.Circuits.Boolean.Lupanov.table f s = f := fun hc_h => absurd (@hc_h (0) (0) (0) (fun (a : Cslib.BitString (0 + 0)) => Bool.true)) (by
  decide +kernel)

