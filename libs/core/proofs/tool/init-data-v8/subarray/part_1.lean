import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Subarray.getElem_eq_getElem_array, hypothesis 3: necessary
set_option maxHeartbeats 20000 in
theorem HypCheckProof.Subarray.getElem_eq_getElem_array.h3 : ¬∀ {α : Type} {i : Nat} {xs : Subarray α}, i < Std.Slice.size xs := fun hc_h => absurd (@hc_h (Nat) (0) ({
      internalRepresentation :=
        { array := #[], start := 0, stop := 0, start_le_stop := of_decide_eq_true (id (Eq.refl Bool.true)),
          stop_le_array_size := of_decide_eq_true (id (Eq.refl Bool.true)) : Std.Slice.Internal.SubarrayData Nat } :
      Std.Slice (Std.Slice.Internal.SubarrayData Nat) })) (by
  decide)

