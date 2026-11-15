import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- String.Pos.Splits.of_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.of_eq.h6 : ¬∀ {s : String} {p : s.Pos} {t₁ t₂ t₃ t₄ : String}, t₁ = t₃ → t₂ = t₄ → p.Splits t₃ t₄ := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("a") ("") ("a") rfl rfl) (by
  simp)

-- String.Pos.Splits.of_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.of_eq.h7 : ¬∀ {s : String} {p : s.Pos} {t₁ t₂ t₃ t₄ : String}, p.Splits t₁ t₂ → t₂ = t₄ → p.Splits t₃ t₄ := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("") ("a") ("") ((@String.Pos.Splits.mk ("") (@String.Pos.mk "" { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
        (@String.instDecidableIsValid "" { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
              (@String.instDecidableIsValid "" { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide))) rfl) (by
  simp)

-- String.Pos.Splits.of_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.of_eq.h8 : ¬∀ {s : String} {p : s.Pos} {t₁ t₂ t₃ t₄ : String}, p.Splits t₁ t₂ → t₁ = t₃ → p.Splits t₃ t₄ := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("") ("") ("a") ((@String.Pos.Splits.mk ("") (@String.Pos.mk "" { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
        (@String.instDecidableIsValid "" { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
              (@String.instDecidableIsValid "" { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide))) rfl) (by
  simp)

-- String.Slice.Pos.ne_startPos_of_slice_ne_startPos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ne_startPos_of_slice_ne_startPos.h4 : ¬∀ {s : String.Slice} {p p₀ p₁ : s.Pos} {h₂ : p ≤ p₁}, p₀ ≤ p := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.ne_startPos_of_slice_ne_startPos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ne_startPos_of_slice_ne_startPos.h5 : ¬∀ {s : String.Slice} {p p₀ p₁ : s.Pos} {h₁ : p₀ ≤ p}, p ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.ne_startPos_of_slice_ne_startPos, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ne_startPos_of_slice_ne_startPos.h6 : ¬∀ {s : String.Slice} {p p₀ p₁ : s.Pos} {h₁ : p₀ ≤ p} {h₂ : p ≤ p₁}, p ≠ s.startPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) (by
  decide) (by
  decide)) (by
  decide)

-- String.Pos.get_slice, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.get_slice.h4 : ¬∀ {s : String} {p p₀ p₁ : s.Pos} {h₂ : p ≤ p₁}, p₀ ≤ p := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.get_slice, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.get_slice.h5 : ¬∀ {s : String} {p p₀ p₁ : s.Pos} {h₁ : p₀ ≤ p}, p ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.get_slice, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.get_slice.h6 : ¬∀ {s : String} {p p₀ p₁ : s.Pos} {h₁ : p₀ ≤ p} {h₂ : p ≤ p₁},
        p.slice p₀ p₁ h₁ h₂ ≠ (s.slice p₀ p₁ (String.Pos.le_trans h₁ h₂)).endPos := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) hc_k0 hc_k1) (by
  decide)

-- String.Pos.ne_endPos_of_slice_ne_endPos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ne_endPos_of_slice_ne_endPos.h4 : ¬∀ {s : String} {p p₀ p₁ : s.Pos} {h₂ : p ≤ p₁}, p₀ ≤ p := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.ne_endPos_of_slice_ne_endPos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ne_endPos_of_slice_ne_endPos.h5 : ¬∀ {s : String} {p p₀ p₁ : s.Pos} {h₁ : p₀ ≤ p}, p ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.ne_endPos_of_slice_ne_endPos, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ne_endPos_of_slice_ne_endPos.h6 : ¬∀ {s : String} {p p₀ p₁ : s.Pos} {h₁ : p₀ ≤ p} {h₂ : p ≤ p₁}, p ≠ s.endPos := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) (by
  decide) (by
  decide)) (by
  decide)

-- String.Pos.Raw.IsValid.modify_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.IsValid.modify_of_le.h3 : ¬∀ {s : String} {p : s.Pos} {f : Char → Char} {q : String.Pos.Raw},
        String.Pos.Raw.IsValid s q → q ≤ p.offset → p ≠ s.endPos := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) (fun (a : Char) => 'a') ({ : String.Pos.Raw }) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide)

-- String.Pos.Raw.IsValid.modify_of_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.IsValid.modify_of_le.h6 : ¬∀ {s : String} {p : s.Pos} {f : Char → Char} {hp : p ≠ s.endPos} {q : String.Pos.Raw},
        String.Pos.Raw.IsValid s q → String.Pos.Raw.IsValid (p.modify f hp) q := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h ("é") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "é".Pos }) (fun (a : Char) => 'a') hc_k0 ({ byteIdx := 2 : String.Pos.Raw }) hc_k1) (by
  decide)

-- String.Pos.Splits.eq_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.eq_left.h6 : ¬∀ {s : String} {p : s.Pos} {t₁ : String} {t₂ : String} {t₃ t₄ : String}, p.Splits t₃ t₄ → t₁ = t₃ := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("a") ("") ("") ("") ((@String.Pos.Splits.mk ("") (@String.Pos.mk "" { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
        (@String.instDecidableIsValid "" { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
              (@String.instDecidableIsValid "" { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Pos.Splits.eq_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.eq_left.h7 : ¬∀ {s : String} {p : s.Pos} {t₁ t₂ t₃ : String} {t₄ : String}, p.Splits t₁ t₂ → t₁ = t₃ := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("") ("a") ("") ((@String.Pos.Splits.mk ("") (@String.Pos.mk "" { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
        (@String.instDecidableIsValid "" { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
              (@String.instDecidableIsValid "" { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Pos.Splits.of_prev, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.of_prev.h6 : ¬∀ {t₁ : String} {c : Char} {t₂ s : String} {p : s.Pos} {hp : p ≠ s.startPos}, p.Splits (t₁ ++ String.singleton c) t₂ := fun hc_h => absurd (@hc_h ("") ('a') ("") ("0") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "0".Pos }) (by
  decide)) (by
  simp)

-- String.Slice.Pattern.Internal.memcmpSliceCompare_eq_compare, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.Internal.memcmpSliceCompare_eq_compare.h5 : ¬∀ {lhs rhs : String.Slice} {lstart rstart : String.Pos.Raw} {len : Nat} {h₂ : rstart.increaseBy len ≤ rhs.rawEndPos},
        lstart.increaseBy len ≤ lhs.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw }) ({ : String.Pos.Raw }) (0) (by
  decide)) (by
  decide)

-- String.Slice.Pattern.Internal.memcmpSliceCompare_eq_compare, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.Internal.memcmpSliceCompare_eq_compare.h6 : ¬∀ {lhs rhs : String.Slice} {lstart rstart : String.Pos.Raw} {len : Nat} {h₁ : lstart.increaseBy len ≤ lhs.rawEndPos},
        rstart.increaseBy len ≤ rhs.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("".toSlice : String.Slice) ({ : String.Pos.Raw }) ({ byteIdx := 1 : String.Pos.Raw }) (0) (by
  decide)) (by
  decide)

-- String.Pos.lt_trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.lt_trans.h4 : ¬∀ {s : String} {p q r : s.Pos}, q < r → p < r := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.lt_trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.lt_trans.h5 : ¬∀ {s : String} {p q r : s.Pos}, p < q → p < r := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.ofSlice_ne_endPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSlice_ne_endPos.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.sliceTo_lt_sliceTo_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceTo_lt_sliceTo_iff.h4 : ¬∀ {s : String.Slice} {p₀ q r : s.Pos} {h₂ : r ≤ p₀}, q ≤ p₀ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.sliceTo_lt_sliceTo_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceTo_lt_sliceTo_iff.h5 : ¬∀ {s : String.Slice} {p₀ q r : s.Pos} {h₁ : q ≤ p₀}, r ≤ p₀ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Pos.ofSlice_next, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSlice_next.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pattern.Model.ForwardSliceSearcher.offset_of_isLongestRevMatchAt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.offset_of_isLongestRevMatchAt.h5 : ¬∀ {pat s : String.Slice} {pos₁ pos₂ : s.Pos},
        pat.isEmpty = Bool.false → pos₂.offset = pos₁.offset.increaseBy pat.utf8ByteSize := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Pos.lt_of_le_of_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.lt_of_le_of_ne.h3 : ¬∀ {s : String} {p q : s.Pos}, p ≠ q → p < q := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.lt_of_le_of_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.lt_of_le_of_ne.h4 : ¬∀ {s : String} {p q : s.Pos}, p ≤ q → p < q := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.next_le_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.next_le_of_lt.h4 : ¬∀ {s : String} {p q : s.Pos} {h : p ≠ s.endPos}, p.next h ≤ q := fun hc_h => absurd (fun hc_k0 => @hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) hc_k0) (by
  decide)

-- String.Slice.Pattern.Model.ForwardStringSearcher.le_of_matchesAt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardStringSearcher.le_of_matchesAt.h4 : ¬∀ {pat : String} {s : String.Slice} {pos : s.Pos}, pat ≠ "" → pos.offset.increaseBy pat.utf8ByteSize ≤ s.rawEndPos := fun hc_h => absurd (@hc_h ("a") ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.get_eq_of_skipSuffixWhile_le_char, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.get_eq_of_skipSuffixWhile_le_char.h3 : ¬∀ {c : Char} {s : String.Slice} {pos : s.Pos} (h' : pos < s.endPos), pos.get (String.Slice.Pos.ne_endPos_of_lt h') = c := fun hc_h => absurd (fun hc_k0 => @hc_h ('a') ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) hc_k0) (by
  decide)

-- String.apply_eq_true_of_skipSuffixWhile_le_bool, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.apply_eq_true_of_skipSuffixWhile_le_bool.h3 : ¬∀ {p : Char → Bool} {s : String} {pos : s.Pos} (h' : pos < s.endPos),
        p (pos.get (String.Pos.ne_endPos_of_lt h')) = Bool.true := fun hc_h => absurd (fun hc_k0 => @hc_h (fun (a : Char) => Bool.false) ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) hc_k0) (by
  decide)

-- String.Pos.Splits.pastModify, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.pastModify.h6 : ¬∀ {f : Char → Char} {s : String} {p : s.Pos} {t₁ t₂ : String} {c : Char}, p.Splits t₁ (String.singleton c ++ t₂) := fun hc_h => absurd (@hc_h (fun (a : Char) => 'a') ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("") ('a')) (by
  simp)

-- String.Slice.Pos.lt_ofSlice_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.lt_ofSlice_iff.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos} {q : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.posGT_eq_next, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posGT_eq_next.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, String.Pos.Raw.IsValidForSlice s p → p < s.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw }) (by
  decide)) (by
  decide)

-- String.Slice.posGT_eq_next, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posGT_eq_next.h3 : ¬∀ {s : String.Slice} {p : String.Pos.Raw} {h : p < s.rawEndPos}, String.Pos.Raw.IsValidForSlice s p := fun hc_h => absurd (@hc_h ("aé".toSlice : String.Slice) ({ byteIdx := 2 : String.Pos.Raw }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.Splits.prevn, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.prevn.h4 : ¬∀ {s : String.Slice} {t₁ t₂ : String} {p : s.Pos} (n : Nat),
        (p.prevn n).Splits (String.ofList (List.take (t₁.toList.length - n) t₁.toList))
          (String.ofList (List.drop (t₁.toList.length - n) t₁.toList) ++ t₂) := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("") ("a") ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) (0)) (by
  simp)

-- String.Pos.prev_prev_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.prev_prev_lt.h3 : ¬∀ {s : String} {p : s.Pos} {h : p ≠ s.startPos}, p.prev h ≠ s.startPos := fun hc_h => absurd (fun hc_k0 => @hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) hc_k0) (by
  decide +kernel)

-- String.Pos.lt_sliceTo_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.lt_sliceTo_iff.h4 : ¬∀ {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos}, q ≤ p₀ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("a".sliceTo
          { offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }).Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.sliceTo_lt_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceTo_lt_iff.h4 : ¬∀ {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos}, q ≤ p₀ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("a".sliceTo
          { offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }).Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.Splits.toSlice, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.toSlice.h4 : ¬∀ {s : String} {p : s.Pos} {t₁ t₂ : String}, p.toSlice.Splits t₁ t₂ := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("a")) (by
  simp)

-- String.Slice.Pos.splits_of_splits_copy, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.splits_of_splits_copy.h4 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ t₂ : String}, p.Splits t₁ t₂ := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("a")) (by
  simp)

-- String.Pos.Splits.toByteArray_left_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.toByteArray_left_eq.h4 : ¬∀ {s : String} {p : s.Pos} {t₁ : String} {t₂ : String}, t₁.toByteArray = s.toByteArray.extract 0 p.offset.byteIdx := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("a") ("")) (by
  decide)

-- String.Slice.splits_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.splits_slice.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pattern.SearchStep.cast_matched, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.SearchStep.cast_matched.h2 : ¬∀ {s t : String.Slice} {startPos endPos : s.Pos}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.ofSlice_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSlice_le.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.offset_ofSlice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.offset_ofSlice.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.cast_le_cast_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.cast_le_cast_iff.h4 : ¬∀ {s t : String} {pos pos' : s.Pos}, s = t := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Pos.le_ofSlice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.le_ofSlice.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.le_ofSlice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.le_ofSlice.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.cast_lt_cast_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.cast_lt_cast_iff.h4 : ¬∀ {s t : String.Slice} {pos pos' : s.Pos}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Pos.cast_lt_cast_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.cast_lt_cast_iff.h4 : ¬∀ {s t : String} {pos pos' : s.Pos}, s = t := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Pos.slice_ofSlice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.slice_ofSlice.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.cast_le_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.cast_le_iff.h4 : ¬∀ {s t : String} {pos : s.Pos} {pos' : t.Pos}, s = t := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pattern.Model.split_char_eq_split_beq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.Model.split_char_eq_split_beq.h4 : ¬∀ {c : Char} {s : String.Slice} (f curr : s.Pos), f ≤ curr := fun hc_h => absurd (@hc_h ('a') ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.sliceFrom_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.sliceFrom_slice.h3 : ¬∀ {s : String} {p₁ p₂ : s.Pos}, p₁ ≤ p₂ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.sliceFrom_le_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceFrom_le_iff.h4 : ¬∀ {s : String.Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("ab".toSlice.sliceFrom
          { offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "ab".toSlice.Pos }).Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.slice_eq_startPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.slice_eq_startPos.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.next_ofSliceFrom, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.next_ofSliceFrom.h3 : ¬∀ {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos}, String.Pos.ofSliceFrom p ≠ s.endPos := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("".sliceFrom
          { offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }).Pos })) (by
  decide)

-- String.Slice.Pos.ofSliceFrom_ne_startPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSliceFrom_ne_startPos.h3 : ¬∀ {s : String.Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos}, String.Slice.Pos.ofSliceFrom p ≠ s.startPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("".toSlice.sliceFrom
          { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "".toSlice.Pos }).Pos })) (by
  decide)

-- String.posLT_lt_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.posLT_lt_iff.h2 : ¬∀ {s : String} {p : String.Pos.Raw} {q : s.Pos}, 0 < p := fun hc_h => absurd (@hc_h ("") ({ : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.posGT_eq_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.posGT_eq_iff.h2 : ¬∀ {s : String} {p : String.Pos.Raw} {q : s.Pos}, p < s.rawEndPos := fun hc_h => absurd (@hc_h ("") ({ : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.posLT_eq_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posLT_eq_iff.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw} {q : s.Pos}, 0 < p := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.posGT_le_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.posGT_le_iff.h2 : ¬∀ {s : String} {p : String.Pos.Raw} {q : s.Pos}, p < s.rawEndPos := fun hc_h => absurd (@hc_h ("") ({ : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.posGT_le_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posGT_le_iff.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw} {q : s.Pos}, p < s.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.isEmpty_slice_eq_false_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.isEmpty_slice_eq_false_iff.h3 : ¬∀ {s : String.Slice} {p₁ p₂ : s.Pos}, p₁ ≤ p₂ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.copy_slice_eq_append_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.copy_slice_eq_append_of_lt.h3 : ¬∀ {s : String} {p q : s.Pos}, p < q := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.Pos.splits_ofEqAppend, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.splits_ofEqAppend.h3 : ¬∀ {s : String.Slice} {t₁ t₂ : String}, s.copy = t₁ ++ t₂ := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("") ("a")) (by
  decide)

-- String.Pos.eq_next_of_next?_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.eq_next_of_next?_eq_some.h3 : ¬∀ {s : String} {p q : s.Pos}, p.next? = Option.some q := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.subslice!_eq_subslice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.subslice!_eq_subslice.h3 : ¬∀ {s : String.Slice} {newStart newEnd : s.Pos}, newStart ≤ newEnd := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Subslice.endExclusive_cast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Subslice.endExclusive_cast.h2 : ¬∀ {s t : String.Slice} {sl : s.Subslice}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({
      startInclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos },
      endExclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos },
      startInclusive_le_endExclusive := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Subslice })) (by
  decide)

-- String.Pos.ofSliceFrom_sliceFrom, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSliceFrom_sliceFrom.h3 : ¬∀ {s : String} {p₀ p : s.Pos}, p₀ ≤ p := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.extract_eq_copy_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.extract_eq_copy_slice.h3 : ¬∀ {s : String.Slice} (p₀ p₁ : s.Pos), p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.offset_cast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.offset_cast.h3 : ¬∀ {s t : String.Slice} {pos : s.Pos}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.ofSlice_endPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSlice_endPos.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.slice_toSlice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.slice_toSlice.h3 : ¬∀ {s : String} {p₁ p₂ : s.Pos}, p₁.toSlice ≤ p₂.toSlice := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.eq_append_of_dropSuffix?_char_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.eq_append_of_dropSuffix?_char_eq_some.h3 : ¬∀ {c : Char} {s : String} {res : String.Slice}, s = res.copy ++ String.singleton c := fun hc_h => absurd (@hc_h ('a') ("") ("".toSlice : String.Slice)) (by
  decide)

-- String.eq_append_of_dropPrefix?_char_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.eq_append_of_dropPrefix?_char_eq_some.h3 : ¬∀ {c : Char} {s : String} {res : String.Slice}, s = String.singleton c ++ res.copy := fun hc_h => absurd (@hc_h ('a') ("") ("".toSlice : String.Slice)) (by
  decide)

-- String.Slice.eq_append_of_dropPrefix?_char_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.eq_append_of_dropPrefix?_char_eq_some.h3 : ¬∀ {c : Char} {s res : String.Slice}, s.copy = String.singleton c ++ res.copy := fun hc_h => absurd (@hc_h ('a') ("".toSlice : String.Slice) ("".toSlice : String.Slice)) (by
  decide)

-- String.eq_append_of_dropSuffix?_bool_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.eq_append_of_dropSuffix?_bool_eq_some.h3 : ¬∀ {p : Char → Bool} {s : String} {res : String.Slice},
        ∃ (c : Char), s = res.copy ++ String.singleton c ∧ p c = Bool.true := fun hc_h => absurd (@hc_h (fun (a : Char) => Bool.false) ("") ("".toSlice : String.Slice)) (by
  simp)

-- String.Slice.eq_append_of_dropPrefix?_slice_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.eq_append_of_dropPrefix?_slice_eq_some.h3 : ¬∀ {pat s res : String.Slice}, s.copy = pat.copy ++ res.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("".toSlice : String.Slice) ("ab".toSlice : String.Slice)) (by
  decide)

-- String.Slice.eq_append_of_dropPrefix?_string_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.eq_append_of_dropPrefix?_string_eq_some.h3 : ¬∀ {pat : String} {s res : String.Slice}, s.copy = pat ++ res.copy := fun hc_h => absurd (@hc_h ("") ("".toSlice : String.Slice) ("ab".toSlice : String.Slice)) (by
  decide)

-- String.eq_append_of_dropPrefix?_string_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.eq_append_of_dropPrefix?_string_eq_some.h3 : ¬∀ {s pat : String} {res : String.Slice}, s = pat ++ res.copy := fun hc_h => absurd (@hc_h ("") ("") ("ab".toSlice : String.Slice)) (by
  decide)

-- String.Slice.eq_append_of_dropSuffix?_string_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.eq_append_of_dropSuffix?_string_eq_some.h3 : ¬∀ {pat : String} {s res : String.Slice}, s.copy = res.copy ++ pat := fun hc_h => absurd (@hc_h ("") ("".toSlice : String.Slice) ("ab".toSlice : String.Slice)) (by
  decide)

-- String.eq_append_of_dropPrefix?_slice_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.eq_append_of_dropPrefix?_slice_eq_some.h3 : ¬∀ {pat res : String.Slice} {s : String}, s = pat.copy ++ res.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("".toSlice : String.Slice) ("a")) (by
  decide)

-- String.Slice.Pos.ext, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ext.h3 : ¬∀ {s : String.Slice} {x y : s.Pos}, x = y := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.str_ne_endPos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.str_ne_endPos.h2 : ¬∀ {s : String.Slice} (p : s.Pos), p.str ≠ s.str.endPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.posGT_eq_posGE, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posGT_eq_posGE.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, p < s.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw })) (by
  decide)

-- String.Slice.offset_posLT_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.offset_posLT_lt.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, 0 < p := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw })) (by
  decide)

-- String.Slice.pos_eq_posLE, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.pos_eq_posLE.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, String.Pos.Raw.IsValidForSlice s p := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw })) (by
  decide)

-- String.Slice.posLT_eq_posLE, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posLT_eq_posLE.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, 0 < p := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw })) (by
  decide)

-- String.Pos.prev?_eq_none, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.prev?_eq_none.h2 : ¬∀ {s : String} {p : s.Pos}, p.prev? = Option.none := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.posLT_offset, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.posLT_offset.h2 : ¬∀ {s : String.Slice} {p : s.Pos}, 0 < p.offset := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.lt_offset_posGT, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.lt_offset_posGT.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, p < s.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw })) (by
  decide)

-- String.Pos.Raw.IsValid.isValidUTF8_extract_utf8ByteSize, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.IsValid.isValidUTF8_extract_utf8ByteSize.h2 : ¬∀ {s : String} {p : String.Pos.Raw}, (s.toByteArray.extract p.byteIdx s.utf8ByteSize).IsValidUTF8 := fun hc_h => absurd (@hc_h ("é") ({ byteIdx := 1 : String.Pos.Raw })) (by
  decide)

-- String.Slice.offset_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.offset_pos.h2 : ¬∀ {s : String.Slice} {off : String.Pos.Raw}, String.Pos.Raw.IsValidForSlice s off := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw })) (by
  decide)

-- String.Slice.pos_eq_posGE, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.pos_eq_posGE.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, String.Pos.Raw.IsValidForSlice s p := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw })) (by
  decide)

-- String.Slice.Pos.cast_endPos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.cast_endPos.h2 : ¬∀ {s t : String.Slice}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice)) (by
  decide)

-- String.Slice.posGE_inc, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posGE_inc.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, p.inc ≤ s.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw })) (by
  decide)

-- String.Slice.Pos.prev?_eq_none, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.prev?_eq_none.h2 : ¬∀ {s : String.Slice} {p : s.Pos}, p.prev? = Option.none := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.prev_ofToSlice, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.prev_ofToSlice.h2 : ¬∀ {s : String} {p : s.toSlice.Pos}, String.Pos.ofToSlice p ≠ s.startPos := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.offset_posGE_eq_self_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.offset_posGE_eq_self_iff.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, p ≤ s.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw })) (by
  decide)

-- String.Pos.byteIdx_lt_utf8ByteSize, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.byteIdx_lt_utf8ByteSize.h2 : ¬∀ {s : String} (p : s.Pos), p.offset.byteIdx < s.utf8ByteSize := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.Pos.str_lt_endExclusive, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.str_lt_endExclusive.h2 : ¬∀ {s : String.Slice} (p : s.Pos), p.str < s.endExclusive := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.Pattern.ForwardSliceSearcher.startsWith_of_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.ForwardSliceSearcher.startsWith_of_isEmpty.h2 : ¬∀ {pat s : String.Slice}, String.Slice.Pattern.ForwardPattern.startsWith pat s = Bool.true := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ("".toSlice : String.Slice)) (by
  decide)

-- String.Slice.Pattern.BackwardSliceSearcher.endsWith_of_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.BackwardSliceSearcher.endsWith_of_isEmpty.h2 : ¬∀ {pat s : String.Slice}, String.Slice.Pattern.BackwardPattern.endsWith pat s = Bool.true := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ("".toSlice : String.Slice)) (by
  decide)

-- String.Pos.Raw.IsValidForSlice.le_utf8ByteSize, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.IsValidForSlice.le_utf8ByteSize.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, p.byteIdx ≤ s.utf8ByteSize := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw })) (by
  decide)

-- String.Pos.Raw.IsValidForSlice.isValid_offsetBy, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.IsValidForSlice.isValid_offsetBy.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, String.Pos.Raw.IsValid s.str (p.offsetBy s.startInclusive.offset) := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw })) (by
  decide)

-- String.Pos.Raw.isValidForSlice_of_eq_rawEndPos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.isValidForSlice_of_eq_rawEndPos.h2 : ¬∀ {p : String.Pos.Raw} {s : String.Slice}, String.Pos.Raw.IsValidForSlice s p := fun hc_h => absurd (@hc_h ({ byteIdx := 1 : String.Pos.Raw }) ("".toSlice : String.Slice)) (by
  decide)

-- String.Pos.Raw.IsValidForSlice.le_rawEndPos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.IsValidForSlice.le_rawEndPos.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, p ≤ s.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw })) (by
  decide)

-- String.Slice.isUTF8FirstByte_utf8ByteAt_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.isUTF8FirstByte_utf8ByteAt_zero.h1 : ¬∀ {s : String.Slice}, 0 < s.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice)) (by
  decide)

