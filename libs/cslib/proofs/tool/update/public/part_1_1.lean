import Cslib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- OrderHom.prevFixed_induction, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.OrderHom.prevFixed_induction.h4 : ¬∀ {α : Type} [inst : CompleteLattice α] (f : α →o α) {x : α} {p : α → Prop},
        p x → (∀ (s : Set α), (∀ a ∈ s, p a) → p (InfSet.sInf s)) → f x ≤ x := fun hc_h => absurd (@hc_h (Bool) (Bool.completeBooleanAlgebra.toCompleteLattice) ({ toFun := fun (x : Bool) => Bool.true, monotone' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool →o Bool }) (Bool.false) (fun _ => True : Bool → Prop) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp)) (by
  decide +kernel)

