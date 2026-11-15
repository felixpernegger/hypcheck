import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/
-- _private.Iris.Instances.IProp.Instance.0.Iris.list_not_mem_of_gt_max, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.list_not_mem_of_gt_max.h2 : ¬∀ (G : List Nat) (k : Nat), ¬k ∈ G := fun hc_h => absurd (@hc_h ([0]) (0)) (by
  decide +kernel)

