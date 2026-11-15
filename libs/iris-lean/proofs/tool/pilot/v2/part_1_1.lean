import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/

-- FracAuth.includedN, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FracAuth.includedN.h8 : ¬∀ {A : Type} [inst : Iris.ORA A] [inst_1 : Iris.OrdInc A] {n : Nat} {dq : Iris.DFrac} {q : Iris.Qp} {a b : A},
        Option.some b ≼{n} Option.some a := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) _ (0) (Iris.DFrac.discard : Iris.DFrac) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.incN_of_dist_of_incN, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.incN_of_dist_of_incN.h8 : ¬∀ {α : Type} [inst : Iris.OFE α] [inst_1 : Iris.Op α] {n : Nat} {a b c : α}, Iris.OFE.Dist n a b → a ≼{n} c := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toOFE) (Iris.DFrac.instCMRADFrac.toOp) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- Iris.Option.valid_of_ord_valid, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.Option.valid_of_ord_valid.h4 : ¬∀ {α : Type} [inst : Iris.ORA α] {a b : α}, Option.some b ≼ₒ Option.some a → ✓ b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (Iris.DFrac.ownDiscard 1 : Iris.DFrac) (by
  rfl)) (by
  nofun)

-- FracAuth.agreeN, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FracAuth.agreeN.h6 : ¬∀ {A : Type} [inst : Iris.ORA A] {n : Nat} {dq : Iris.DFrac} {a b : A}, Iris.OFE.Dist n a b := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (0) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.own 1 : Iris.DFrac)) (by
  nofun)

-- Iris.ORA.op_mono_right_ord, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ORA.op_mono_right_ord.h5 : ¬∀ {α : Type} [inst : Iris.ORA α] {x y : α} (z : α), z • x ≼ₒ z • y := fun hc_h => absurd (@hc_h (Iris.DFrac : Type) (Iris.DFrac.instCMRADFrac.toORA) (Iris.DFrac.own 1 : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac) (Iris.DFrac.discard : Iris.DFrac)) (by
  nofun)

