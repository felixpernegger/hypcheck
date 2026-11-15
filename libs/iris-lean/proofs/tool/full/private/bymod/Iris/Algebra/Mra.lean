import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/
-- _private.Iris.Algebra.Mra.0.Iris.Mra.rel_iff_of_toMra_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Mra.rel_iff_of_toMra_eq.h4 : ¬∀ {α : Type} {R : α → α → Prop} {a b : α} (c : α), R c a ↔ R c b := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (1) (0)) (by
  decide +kernel)

