import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- String.Pos.slice_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.slice_inj.h5 : ¬∀ {s : String} {p₀ p₁ pos pos' : s.Pos} {h₁' : p₀ ≤ pos'} {h₂ : pos ≤ p₁} {h₂' : pos' ≤ p₁}, p₀ ≤ pos := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Pos.slice_inj, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.slice_inj.h6 : ¬∀ {s : String} {p₀ p₁ pos pos' : s.Pos} {h₁ : p₀ ≤ pos} {h₂ : pos ≤ p₁} {h₂' : pos' ≤ p₁}, p₀ ≤ pos' := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Pos.slice_inj, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.slice_inj.h7 : ¬∀ {s : String} {p₀ p₁ pos pos' : s.Pos} {h₁ : p₀ ≤ pos} {h₁' : p₀ ≤ pos'} {h₂' : pos' ≤ p₁}, pos ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Pos.slice_inj, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.slice_inj.h8 : ¬∀ {s : String} {p₀ p₁ pos pos' : s.Pos} {h₁ : p₀ ≤ pos} {h₁' : p₀ ≤ pos'} {h₂ : pos ≤ p₁}, pos' ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.slice_le_slice_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.slice_le_slice_iff.h5 : ¬∀ {s : String.Slice} {p₀ p₁ q r : s.Pos} {h₁' : p₀ ≤ r} {h₂ : q ≤ p₁} {h₂' : r ≤ p₁}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.slice_le_slice_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.slice_le_slice_iff.h6 : ¬∀ {s : String.Slice} {p₀ p₁ q r : s.Pos} {h₁ : p₀ ≤ q} {h₂ : q ≤ p₁} {h₂' : r ≤ p₁}, p₀ ≤ r := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.slice_le_slice_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.slice_le_slice_iff.h7 : ¬∀ {s : String.Slice} {p₀ p₁ q r : s.Pos} {h₁ : p₀ ≤ q} {h₁' : p₀ ≤ r} {h₂' : r ≤ p₁}, q ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.slice_le_slice_iff, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.slice_le_slice_iff.h8 : ¬∀ {s : String.Slice} {p₀ p₁ q r : s.Pos} {h₁ : p₀ ≤ q} {h₁' : p₀ ≤ r} {h₂ : q ≤ p₁}, r ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.sliceTo_le_sliceTo_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceTo_le_sliceTo_iff.h4 : ¬∀ {s : String.Slice} {p₀ q r : s.Pos} {h₂ : r ≤ p₀}, q ≤ p₀ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.sliceTo_le_sliceTo_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceTo_le_sliceTo_iff.h5 : ¬∀ {s : String.Slice} {p₀ q r : s.Pos} {h₁ : q ≤ p₀}, r ≤ p₀ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Pos.sliceTo_lt_sliceTo_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceTo_lt_sliceTo_iff.h4 : ¬∀ {s : String} {p₀ q r : s.Pos} {h₂ : r ≤ p₀}, q ≤ p₀ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.sliceTo_lt_sliceTo_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceTo_lt_sliceTo_iff.h5 : ¬∀ {s : String} {p₀ q r : s.Pos} {h₁ : q ≤ p₀}, r ≤ p₀ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.get_eq_get_ofSlice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.get_eq_get_ofSlice.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.get_eq_get_ofSlice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.get_eq_get_ofSlice.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.ofSlice_prev, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSlice_prev.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.ofSlice_prev, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSlice_prev.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.offset_toModifyOfLE, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.offset_toModifyOfLE.h5 : ¬∀ {s : String} {q p : s.Pos} {f : Char → Char} {hp : p ≠ s.endPos}, q ≤ p := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (fun (a : Char) => 'a') (by
  decide)) (by
  decide)

-- String.Slice.Pos.ofSlice_le_ofSlice_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSlice_le_ofSlice_iff.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.ofSlice_inj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSlice_inj.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.le_ofSlice_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.le_ofSlice_iff.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos} {q : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.ofSlice_lt_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSlice_lt_iff.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos} {q : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.splits_cast_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.splits_cast_iff.h2 : ¬∀ {s₁ s₂ : String.Slice} {p : s₁.Pos} {t₁ t₂ : String}, s₁.copy = s₂.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("")) (by
  decide)

-- String.Pos.Splits.splits_rotateRight, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.splits_rotateRight.h5 : ¬∀ {s : String} {p : s.Pos} {t₁ t₂ t₃ : String}, p.Splits t₁ (t₂ ++ t₃) := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("") ("a")) (by
  simp)

-- String.Slice.Pos.Splits.next, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.next.h5 : ¬∀ {t₁ : String} {c : Char} {t₂ : String} {s : String.Slice} {p : s.Pos}, p.Splits t₁ (String.singleton c ++ t₂) := fun hc_h => absurd (@hc_h ("") ('a') ("") ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  simp)

-- String.Pos.splits_cast_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.splits_cast_iff.h2 : ¬∀ {s₁ s₂ : String} {p : s₁.Pos} {t₁ t₂ : String}, s₁ = s₂ := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("")) (by
  decide)

-- String.Pos.Splits.next, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.next.h5 : ¬∀ {t₁ : String} {c : Char} {t₂ s : String} {p : s.Pos}, p.Splits t₁ (String.singleton c ++ t₂) := fun hc_h => absurd (@hc_h ("") ('a') ("") ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  simp)

-- String.Slice.Pos.lt_next_next, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.lt_next_next.h3 : ¬∀ {s : String.Slice} {p : s.Pos} {h : p ≠ s.endPos}, p.next h ≠ s.endPos := fun hc_h => absurd (fun hc_k0 => @hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) hc_k0) (by
  decide)

-- String.Slice.Pos.sliceFrom_lt_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceFrom_lt_iff.h4 : ¬∀ {s : String.Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("ab".toSlice.sliceFrom
          { offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "ab".toSlice.Pos }).Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.lt_sliceFrom_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.lt_sliceFrom_iff.h4 : ¬∀ {s : String.Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("ab".toSlice.sliceFrom
          { offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "ab".toSlice.Pos }).Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.Splits.copy_sliceTo_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.copy_sliceTo_eq.h4 : ¬∀ {t₁ : String} {t₂ : String} {s : String.Slice} {p : s.Pos}, (s.sliceTo p).copy = t₁ := fun hc_h => absurd (@hc_h ("a") ("") ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Pos.Splits.offset_eq_decreaseBy, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.offset_eq_decreaseBy.h4 : ¬∀ {t₁ : String} {t₂ s : String} {p : s.Pos}, p.offset = s.rawEndPos.decreaseBy t₂.utf8ByteSize := fun hc_h => absurd (@hc_h ("") ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pattern.SearchStep.cast_rejected, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.SearchStep.cast_rejected.h2 : ¬∀ {s t : String.Slice} {startPos endPos : s.Pos}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.offset_ofSlice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.offset_ofSlice.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.cast_le_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.cast_le_iff.h4 : ¬∀ {s t : String.Slice} {pos : s.Pos} {pos' : t.Pos}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.le_cast_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.le_cast_iff.h4 : ¬∀ {s t : String} {pos : t.Pos} {pos' : s.Pos}, s = t := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.Pos.cast_inj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.cast_inj.h2 : ¬∀ {s t : String.Slice} {p q : s.Pos}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Pos.cast_inj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.cast_inj.h2 : ¬∀ {s t : String} {p q : s.Pos}, s = t := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.Pos.cast_lt_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.cast_lt_iff.h4 : ¬∀ {s t : String.Slice} {pos : s.Pos} {pos' : t.Pos}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.lt_cast_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.lt_cast_iff.h4 : ¬∀ {s t : String} {pos : t.Pos} {pos' : s.Pos}, s = t := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Pos.Raw.isValidForSlice_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.isValidForSlice_slice.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos} (pos : String.Pos.Raw), p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ : String.Pos.Raw })) (by
  decide)

-- String.Slice.Pattern.Model.split_bool_eq_internal, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.Model.split_bool_eq_internal.h4 : ¬∀ {p : Char → Bool} {s : String.Slice} (f curr : s.Pos), f ≤ curr := fun hc_h => absurd (@hc_h (fun (a : Char) => Bool.false) ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.sliceTo_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.sliceTo_slice.h3 : ¬∀ {s : String} {p₁ p₂ : s.Pos}, p₁ ≤ p₂ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.sliceFrom_lt_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceFrom_lt_iff.h4 : ¬∀ {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("a".sliceFrom
          { offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "a".Pos }).Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.slice_eq_self_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.slice_eq_self_iff.h3 : ¬∀ {s : String.Slice} {p₁ p₂ : s.Pos}, p₁ ≤ p₂ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.slice_eq_endPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.slice_eq_endPos.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.next_ofSliceFrom, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.next_ofSliceFrom.h3 : ¬∀ {s : String.Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos}, String.Slice.Pos.ofSliceFrom p ≠ s.endPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("".toSlice.sliceFrom
          { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "".toSlice.Pos }).Pos })) (by
  decide)

-- String.lt_posGE_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.lt_posGE_iff.h2 : ¬∀ {s : String} {p : String.Pos.Raw} {q : s.Pos}, p ≤ s.rawEndPos := fun hc_h => absurd (@hc_h ("") ({ byteIdx := 1 : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.posGE_le_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.posGE_le_iff.h2 : ¬∀ {s : String} {p : String.Pos.Raw} {q : s.Pos}, p ≤ s.rawEndPos := fun hc_h => absurd (@hc_h ("") ({ byteIdx := 1 : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.posLT_lt_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posLT_lt_iff.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw} {q : s.Pos}, 0 < p := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.le_posLT_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.le_posLT_iff.h2 : ¬∀ {s : String} {p : String.Pos.Raw} {q : s.Pos}, 0 < p := fun hc_h => absurd (@hc_h ("") ({ : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.posGE_eq_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.posGE_eq_iff.h2 : ¬∀ {s : String} {p : String.Pos.Raw} {q : s.Pos}, p ≤ s.rawEndPos := fun hc_h => absurd (@hc_h ("") ({ byteIdx := 1 : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.lt_posGT_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.lt_posGT_iff.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw} {q : s.Pos}, p < s.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.isEmpty_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.isEmpty_slice.h3 : ¬∀ {s : String} {p₁ p₂ : s.Pos}, p₁ ≤ p₂ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.copy_sliceFrom_cast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.copy_sliceFrom_cast.h2 : ¬∀ {s t : String} {pos : s.Pos}, s = t := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.copy_sliceTo_cast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.copy_sliceTo_cast.h2 : ¬∀ {s t : String} {pos : s.Pos}, s = t := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.copy_sliceFrom_cast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.copy_sliceFrom_cast.h2 : ¬∀ {s t : String.Slice} {pos : s.Pos}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Pos.eq_prev_of_prev?_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.eq_prev_of_prev?_eq_some.h3 : ¬∀ {s : String} {p q : s.Pos}, p.prev? = Option.some q := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.Subslice.startInclusive_cast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Subslice.startInclusive_cast.h2 : ¬∀ {s t : String.Slice} {sl : s.Subslice}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({
      startInclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos },
      endExclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos },
      startInclusive_le_endExclusive := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Subslice })) (by
  decide)

-- String.str_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.str_slice.h3 : ¬∀ {s : String} {startInclusive endExclusive : s.Pos}, startInclusive ≤ endExclusive := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.utf8ByteSize_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.utf8ByteSize_slice.h3 : ¬∀ {s : String.Slice} {newStart newEnd : s.Pos}, newStart ≤ newEnd := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.str_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.str_slice.h3 : ¬∀ {s : String.Slice} {newStart newEnd : s.Pos}, newStart ≤ newEnd := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.cast_eq_endPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.cast_eq_endPos.h3 : ¬∀ {s t : String.Slice} {p : s.Pos}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.offset_sliceFrom, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.offset_sliceFrom.h3 : ¬∀ {s : String.Slice} {p₀ pos : s.Pos}, p₀ ≤ pos := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.ofSliceTo_sliceTo, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSliceTo_sliceTo.h3 : ¬∀ {s : String} {p₀ p : s.Pos}, p ≤ p₀ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.slice_eq_slice!, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.slice_eq_slice!.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.eq_append_of_dropSuffix?_char_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.eq_append_of_dropSuffix?_char_eq_some.h3 : ¬∀ {c : Char} {s res : String.Slice}, s.copy = res.copy ++ String.singleton c := fun hc_h => absurd (@hc_h ('a') ("".toSlice : String.Slice) ("".toSlice : String.Slice)) (by
  decide)

-- String.Pos.get_ofToSlice, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.get_ofToSlice.h2 : ¬∀ {s : String} {p : s.toSlice.Pos}, String.Pos.ofToSlice p ≠ s.endPos := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.copy_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.copy_pos.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, String.Pos.Raw.IsValidForSlice s p := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw })) (by
  decide)

-- String.Slice.splits_prev_endPos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.splits_prev_endPos.h1 : ¬∀ {s : String.Slice}, s.endPos ≠ s.startPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice)) (by
  decide)

-- String.Slice.splits_next_startPos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.splits_next_startPos.h1 : ¬∀ {s : String.Slice}, s.startPos ≠ s.endPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice)) (by
  decide)

