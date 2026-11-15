import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- OrderHom.nextFixed_le_of_map_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.OrderHom.nextFixed_le_of_map_le.h5 : ¬∀ {α : Type} [inst : CompleteLattice α] (f : α →o α) {x y : α}, x ≤ y → f y ≤ y → x ≤ f x := fun hc_h => absurd (@hc_h (Bool) (Bool.completeBooleanAlgebra.toCompleteLattice) ({ toFun := fun (x : Bool) => Bool.false, monotone' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool →o Bool }) (Bool.true) (Bool.true) (by
  decide) (by
  decide)) (by
  decide +kernel)

