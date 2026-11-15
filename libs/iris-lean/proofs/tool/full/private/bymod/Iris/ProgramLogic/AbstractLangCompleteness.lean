import Iris

/-! Proofs emitted by HypCheck.lean (Lean 4.35.0). -/
-- _private.Iris.ProgramLogic.AbstractLangCompleteness.0.Iris.ProgramLogic.qp_div_ofPNat_succ_nil, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iris.ProgramLogic.qp_div_ofPNat_succ_nil.h3 : ¬∀ {α : Type} (qc : Iris.Qp) {l : List α}, qc.divide_even (l.length + 1) (Nat.succ_pos l.length) = qc := fun hc_h => absurd (@hc_h (Nat) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { q : Rat // 0 < q })) ([0])) (by
  decide +kernel)

