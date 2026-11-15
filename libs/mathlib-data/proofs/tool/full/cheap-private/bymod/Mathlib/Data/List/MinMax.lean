import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.Mathlib.Data.List.MinMax.0.List.foldl_argAux_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldl_argAux_mem.h6 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] (l : List α) (a m : α), m ∈ a :: l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) ([]) (0) (1)) (by
  decide +kernel)

