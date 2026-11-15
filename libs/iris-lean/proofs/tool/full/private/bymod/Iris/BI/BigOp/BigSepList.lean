import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/
-- _private.Iris.BI.BigOp.BigSepList.0.Iris.BI.list_split, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.BI.list_split.h4 : ¬∀ {A : Type} {l : List A} {i : Nat} {x : A}, l = List.take i l ++ x :: List.drop (i + 1) l := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (0)) (by
  decide +kernel)

