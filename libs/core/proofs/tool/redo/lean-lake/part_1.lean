import Lean
import Lake

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Elab.Tactic.Omega.List.nonzeroMinimum_le, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_le.h2.inst : ¬Lean.Elab.Tactic.Omega.List.nonzeroMinimum [2] ≤ 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_le.h2.prem0 : 1 ≠ 0 := by
  decide
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_le.h2 : ¬∀ {a : Nat} {xs : List Nat}, a ≠ 0 → Lean.Elab.Tactic.Omega.List.nonzeroMinimum xs ≤ a := fun hc_h => HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_le.h2.inst (@hc_h (1) ([2]) HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_le.h2.prem0)

-- Lean.Elab.Tactic.Omega.List.nonzeroMinimum_le, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_le.h3.inst : ¬Lean.Elab.Tactic.Omega.List.nonzeroMinimum [0, 1] ≤ 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_le.h3.prem0 : 0 ∈ [0, 1] := by
  decide
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_le.h3 : ¬∀ {a : Nat} {xs : List Nat}, a ∈ xs → Lean.Elab.Tactic.Omega.List.nonzeroMinimum xs ≤ a := fun hc_h => HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_le.h3.inst (@hc_h (0) ([0, 1]) HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_le.h3.prem0)

-- Lean.Elab.Tactic.Omega.List.nonzeroMinimum_eq_nonzero_iff, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_eq_nonzero_iff.h2.inst : ¬(Lean.Elab.Tactic.Omega.List.nonzeroMinimum [] = 0 ↔ 0 ∈ [] ∧ ∀ (x : Nat), x ∈ [] → 0 ≤ x ∨ x = 0) := by
  decide
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_eq_nonzero_iff.h2 : ¬∀ {xs : List Nat} {y : Nat},
        Lean.Elab.Tactic.Omega.List.nonzeroMinimum xs = y ↔ y ∈ xs ∧ ∀ (x : Nat), x ∈ xs → y ≤ x ∨ x = 0 := fun hc_h => HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_eq_nonzero_iff.h2.inst (@hc_h ([]) (0))

-- Lean.Elab.Tactic.Omega.List.nonzeroMinimum_eq_of_nonzero, hypothesis 1: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_eq_of_nonzero.h1.inst : ¬∃ (x : Nat), x ∈ [] ∧ Lean.Elab.Tactic.Omega.List.nonzeroMinimum [] = x := by
  decide
theorem HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_eq_of_nonzero.h1 : ¬∀ {xs : List Nat}, ∃ (x : Nat), x ∈ xs ∧ Lean.Elab.Tactic.Omega.List.nonzeroMinimum xs = x := fun hc_h => HypCheckProof.Lean.Elab.Tactic.Omega.List.nonzeroMinimum_eq_of_nonzero.h1.inst (@hc_h ([]))

