import Lean
import Lake

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Elab.Tactic.Omega.List.nonzeroMinimum_pos, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_pos.h2.inst : ¬0 < Lean.Elab.Tactic.Omega.List.nonzeroMinimum [] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_pos.h2.prem0 : 1 ≠ 0 := by
  decide
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_pos.h2 : ¬∀ {a : Nat} {xs : List Nat}, a ≠ 0 → 0 < Lean.Elab.Tactic.Omega.List.nonzeroMinimum xs := fun hc_h => HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_pos.h2.inst (@hc_h (1) ([]) HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_pos.h2.prem0)

-- Lean.Elab.Tactic.Omega.List.nonzeroMinimum_pos, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_pos.h3.inst : ¬0 < Lean.Elab.Tactic.Omega.List.nonzeroMinimum [0] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_pos.h3.prem0 : 0 ∈ [0] := by
  decide
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_pos.h3 : ¬∀ {a : Nat} {xs : List Nat}, a ∈ xs → 0 < Lean.Elab.Tactic.Omega.List.nonzeroMinimum xs := fun hc_h => HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_pos.h3.inst (@hc_h (0) ([0]) HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_pos.h3.prem0)

-- Lean.Elab.Tactic.Omega.List.minNatAbs_eq_nonzero_iff, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.minNatAbs_eq_nonzero_iff.h2.inst : ¬(Lean.Elab.Tactic.Omega.List.minNatAbs [] = 0 ↔
        (∃ (y : Int), y ∈ [] ∧ y.natAbs = 0) ∧ ∀ (y : Int), y ∈ [] → 0 ≤ y.natAbs ∨ y = 0) := by
  decide
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.minNatAbs_eq_nonzero_iff.h2 : ¬∀ {z : Nat} (xs : List Int),
        Lean.Elab.Tactic.Omega.List.minNatAbs xs = z ↔
          (∃ (y : Int), y ∈ xs ∧ y.natAbs = z) ∧ ∀ (y : Int), y ∈ xs → z ≤ y.natAbs ∨ y = 0 := fun hc_h => HypCheckProof.Lean.Elab.Tactic.Omega.List.minNatAbs_eq_nonzero_iff.h2.inst (@hc_h (0) ([]))

-- Lean.Elab.Tactic.Omega.List.nonzeroMinimum_mem, hypothesis 1: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_mem.h1.inst : ¬Lean.Elab.Tactic.Omega.List.nonzeroMinimum [] ∈ [] := by
  decide
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_mem.h1 : ¬∀ {xs : List Nat}, Lean.Elab.Tactic.Omega.List.nonzeroMinimum xs ∈ xs := fun hc_h => HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_mem.h1.inst (@hc_h ([]))

