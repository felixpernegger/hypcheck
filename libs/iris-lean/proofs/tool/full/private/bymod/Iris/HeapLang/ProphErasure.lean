import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/
-- _private.Iris.HeapLang.ProphErasure.0.Iris.HeapLang.map_eq_append_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.HeapLang.map_eq_append_cons.h7 : ¬∀ {α β : Type} {f : α → β} {l : List α} {xs : List β} {y : β} {ys : List β},
        ∃ (la : List α), ∃ (a : α), ∃ (lb : List α), l = la ++ a :: lb ∧ List.map f la = xs ∧ f a = y ∧ List.map f lb = ys := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n + 1 : Nat → Nat) ([]) ([]) (0) ([])) (by
  simp)

