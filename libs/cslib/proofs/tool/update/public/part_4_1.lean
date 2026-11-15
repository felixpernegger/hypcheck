import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- OrderHom.le_prevFixed_of_map_ge, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.OrderHom.le_prevFixed_of_map_ge.h5 : ¬∀ {α : Type} [inst : CompleteLattice α] (f : α →o α) {x y : α}, y ≤ x → y ≤ f y → f x ≤ x := fun hc_h => absurd (@hc_h (Bool) (Bool.completeBooleanAlgebra.toCompleteLattice) ({ toFun := fun (x : Bool) => Bool.true, monotone' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool →o Bool }) (Bool.false) (Bool.false) (by
  decide) (by
  decide)) (by
  decide +kernel)

