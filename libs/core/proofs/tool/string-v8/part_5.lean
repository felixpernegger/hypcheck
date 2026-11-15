import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- String.Pos.slice_le_slice_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.slice_le_slice_iff.h5 : ¬∀ {s : String} {p₀ p₁ q r : s.Pos} {h₁' : p₀ ≤ r} {h₂ : q ≤ p₁} {h₂' : r ≤ p₁}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Pos.slice_le_slice_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.slice_le_slice_iff.h6 : ¬∀ {s : String} {p₀ p₁ q r : s.Pos} {h₁ : p₀ ≤ q} {h₂ : q ≤ p₁} {h₂' : r ≤ p₁}, p₀ ≤ r := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Pos.slice_le_slice_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.slice_le_slice_iff.h7 : ¬∀ {s : String} {p₀ p₁ q r : s.Pos} {h₁ : p₀ ≤ q} {h₁' : p₀ ≤ r} {h₂' : r ≤ p₁}, q ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Pos.slice_le_slice_iff, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.slice_le_slice_iff.h8 : ¬∀ {s : String} {p₀ p₁ q r : s.Pos} {h₁ : p₀ ≤ q} {h₁' : p₀ ≤ r} {h₂ : q ≤ p₁}, r ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.Splits.le_iff_exists_eq_append, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.le_iff_exists_eq_append.h7 : ¬∀ {s : String.Slice} {p₁ p₂ : s.Pos} {t₁ t₂ t₃ t₄ : String},
        p₂.Splits t₃ t₄ → (p₁ ≤ p₂ ↔ ∃ (t₅ : String), t₃ = t₁ ++ t₅ ∧ t₂ = t₅ ++ t₄) := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("a") ("") ("") ((@String.Slice.Pos.Splits.mk ("".toSlice) (@String.Slice.Pos.mk "".toSlice { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  simp)

-- String.Slice.Pos.Splits.le_iff_exists_eq_append, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.le_iff_exists_eq_append.h8 : ¬∀ {s : String.Slice} {p₁ p₂ : s.Pos} {t₁ t₂ t₃ t₄ : String},
        p₁.Splits t₁ t₂ → (p₁ ≤ p₂ ↔ ∃ (t₅ : String), t₃ = t₁ ++ t₅ ∧ t₂ = t₅ ++ t₄) := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("") ("") ("a") ((@String.Slice.Pos.Splits.mk ("".toSlice) (@String.Slice.Pos.mk "".toSlice { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  simp)

-- String.Slice.Pos.ne_endPos_of_slice_ne_endPos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ne_endPos_of_slice_ne_endPos.h4 : ¬∀ {s : String.Slice} {p p₀ p₁ : s.Pos} {h₂ : p ≤ p₁}, p₀ ≤ p := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.ne_endPos_of_slice_ne_endPos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ne_endPos_of_slice_ne_endPos.h5 : ¬∀ {s : String.Slice} {p p₀ p₁ : s.Pos} {h₁ : p₀ ≤ p}, p ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.ne_endPos_of_slice_ne_endPos, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ne_endPos_of_slice_ne_endPos.h6 : ¬∀ {s : String.Slice} {p p₀ p₁ : s.Pos} {h₁ : p₀ ≤ p} {h₂ : p ≤ p₁}, p ≠ s.endPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.get_slice, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.get_slice.h4 : ¬∀ {s : String.Slice} {p p₀ p₁ : s.Pos} {h₂ : p ≤ p₁}, p₀ ≤ p := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.get_slice, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.get_slice.h5 : ¬∀ {s : String.Slice} {p p₀ p₁ : s.Pos} {h₁ : p₀ ≤ p}, p ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.get_slice, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.get_slice.h6 : ¬∀ {s : String.Slice} {p p₀ p₁ : s.Pos} {h₁ : p₀ ≤ p} {h₂ : p ≤ p₁},
        p.slice p₀ p₁ h₁ h₂ ≠ (s.slice p₀ p₁ (String.Slice.Pos.le_trans h₁ h₂)).endPos := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) hc_k0 hc_k1) (by
  decide)

-- String.Pos.ne_startPos_of_slice_ne_startPos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ne_startPos_of_slice_ne_startPos.h4 : ¬∀ {s : String} {p p₀ p₁ : s.Pos} {h₂ : p ≤ p₁}, p₀ ≤ p := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.ne_startPos_of_slice_ne_startPos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ne_startPos_of_slice_ne_startPos.h5 : ¬∀ {s : String} {p p₀ p₁ : s.Pos} {h₁ : p₀ ≤ p}, p ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.ne_startPos_of_slice_ne_startPos, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ne_startPos_of_slice_ne_startPos.h6 : ¬∀ {s : String} {p p₀ p₁ : s.Pos} {h₁ : p₀ ≤ p} {h₂ : p ≤ p₁}, p ≠ s.startPos := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.Splits.eq_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.eq_left.h6 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ : String} {t₂ : String} {t₃ t₄ : String}, p.Splits t₃ t₄ → t₁ = t₃ := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("a") ("") ("") ("") ((@String.Slice.Pos.Splits.mk ("".toSlice) (@String.Slice.Pos.mk "".toSlice { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Slice.Pos.Splits.eq_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.eq_left.h7 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ t₂ t₃ : String} {t₄ : String}, p.Splits t₁ t₂ → t₁ = t₃ := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("") ("a") ("") ((@String.Slice.Pos.Splits.mk ("".toSlice) (@String.Slice.Pos.mk "".toSlice { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Pos.Splits.pos_eq_of_eq_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.pos_eq_of_eq_right.h6 : ¬∀ {s : String} {p q : s.Pos} {s_1 : String} {s' t : String}, q.Splits s' t → p = q := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ("") ("a") ("") ((@String.Pos.Splits.mk ("a") (@String.Pos.mk "a" { byteIdx := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : String.Pos.Raw }
      (@of_decide_eq_true
        (String.Pos.Raw.IsValid "a" { byteIdx := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : String.Pos.Raw })
        (@String.instDecidableIsValid "a"
          { byteIdx := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide
              (String.Pos.Raw.IsValid "a"
                { byteIdx := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : String.Pos.Raw })
              (@String.instDecidableIsValid "a"
                { byteIdx := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("a") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Pos.Splits.pos_eq_of_eq_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.pos_eq_of_eq_right.h7 : ¬∀ {s : String} {p q : s.Pos} {s_1 : String} {s' : String} {t : String}, p.Splits s_1 t → p = q := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ("") ("") ("a") ((@String.Pos.Splits.mk ("a") (@String.Pos.mk "a" { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValid "a" { : String.Pos.Raw })
        (@String.instDecidableIsValid "a" { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValid "a" { : String.Pos.Raw })
              (@String.instDecidableIsValid "a" { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("a") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Slice.Pos.Splits.pos_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.pos_eq.h6 : ¬∀ {s : String.Slice} {p q : s.Pos} {s_1 : String} {t : String} {t' : String}, q.Splits s_1 t' → p = q := fun hc_h => absurd (@hc_h ("a".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "a".toSlice.Pos }) ("a") ("") ("") ((@String.Slice.Pos.Splits.mk ("a".toSlice) (@String.Slice.Pos.mk "a".toSlice { byteIdx := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : String.Pos.Raw }
      (@of_decide_eq_true
        (String.Pos.Raw.IsValidForSlice "a".toSlice
          { byteIdx := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "a".toSlice
          { byteIdx := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide
              (String.Pos.Raw.IsValidForSlice "a".toSlice
                { byteIdx := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "a".toSlice
                { byteIdx := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("a") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Slice.Pos.Splits.pos_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.pos_eq.h7 : ¬∀ {s : String.Slice} {p q : s.Pos} {s_1 t : String} {t' : String}, p.Splits s_1 t → p = q := fun hc_h => absurd (@hc_h ("a".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "a".toSlice.Pos }) ("") ("a") ("") ((@String.Slice.Pos.Splits.mk ("a".toSlice) (@String.Slice.Pos.mk "a".toSlice { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValidForSlice "a".toSlice { : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "a".toSlice { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValidForSlice "a".toSlice { : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "a".toSlice { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("a") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Slice.Pos.Splits.eq_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.eq_right.h6 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ : String} {t₂ t₃ t₄ : String}, p.Splits t₃ t₄ → t₂ = t₄ := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("a") ("") ("") ((@String.Slice.Pos.Splits.mk ("".toSlice) (@String.Slice.Pos.mk "".toSlice { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Slice.Pos.Splits.eq_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.eq_right.h7 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ t₂ : String} {t₃ : String} {t₄ : String}, p.Splits t₁ t₂ → t₂ = t₄ := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("") ("") ("a") ((@String.Slice.Pos.Splits.mk ("".toSlice) (@String.Slice.Pos.mk "".toSlice { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Slice.Pos.Splits.of_next, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.of_next.h6 : ¬∀ {t₁ : String} {c : Char} {t₂ : String} {s : String.Slice} {p : s.Pos} {hp : p ≠ s.endPos},
        p.Splits t₁ (String.singleton c ++ t₂) := fun hc_h => absurd (@hc_h ("") ('a') ("") ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  simp)

-- String.Slice.Pos.Splits.get_eq_of_singleton, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.get_eq_of_singleton.h6 : ¬∀ {s : String.Slice} {p : s.Pos} {h : p ≠ s.endPos} {t₁ t₂ : String} {c : Char}, p.get h = c := fun hc_h => absurd (fun hc_k0 => @hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) hc_k0 ("") ("") ('0')) (by
  decide)

-- String.Pos.Splits.get_eq_of_singleton, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.get_eq_of_singleton.h6 : ¬∀ {s : String} {p : s.Pos} {h : p ≠ s.endPos} {t₁ t₂ : String} {c : Char}, p.get h = c := fun hc_h => absurd (fun hc_k0 => @hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) hc_k0 ("") ("") ('0')) (by
  decide)

-- String.Slice.Pos.Splits.of_prev, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.of_prev.h6 : ¬∀ {t₁ : String} {c : Char} {t₂ : String} {s : String.Slice} {p : s.Pos} {hp : p ≠ s.startPos},
        p.Splits (t₁ ++ String.singleton c) t₂ := fun hc_h => absurd (@hc_h ("") ('a') ("") ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide)) (by
  simp)

-- String.Slice.Pattern.Internal.memcmpSliceLt_eq_true_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.Internal.memcmpSliceLt_eq_true_iff.h5 : ¬∀ {lhs rhs : String.Slice} {lstart rstart : String.Pos.Raw} {len : Nat} {h₂ : rstart.increaseBy len ≤ rhs.rawEndPos},
        lstart.increaseBy len ≤ lhs.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw }) ({ : String.Pos.Raw }) (0) (by
  decide)) (by
  decide)

-- String.Slice.Pattern.Internal.memcmpSliceLt_eq_true_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.Internal.memcmpSliceLt_eq_true_iff.h6 : ¬∀ {lhs rhs : String.Slice} {lstart rstart : String.Pos.Raw} {len : Nat} {h₁ : lstart.increaseBy len ≤ lhs.rawEndPos},
        rstart.increaseBy len ≤ rhs.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("".toSlice : String.Slice) ({ : String.Pos.Raw }) ({ byteIdx := 1 : String.Pos.Raw }) (0) (by
  decide)) (by
  decide)

-- String.Slice.Pos.ofSlice_ne_startPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSlice_ne_startPos.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.sliceFrom_lt_sliceFrom_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceFrom_lt_sliceFrom_iff.h4 : ¬∀ {s : String.Slice} {p₀ q r : s.Pos} {h₂ : p₀ ≤ r}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.sliceFrom_lt_sliceFrom_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceFrom_lt_sliceFrom_iff.h5 : ¬∀ {s : String.Slice} {p₀ q r : s.Pos} {h₁ : p₀ ≤ q}, p₀ ≤ r := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.sliceFrom_le_sliceFrom_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceFrom_le_sliceFrom_iff.h4 : ¬∀ {s : String.Slice} {p₀ q r : s.Pos} {h₂ : p₀ ≤ r}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.sliceFrom_le_sliceFrom_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceFrom_le_sliceFrom_iff.h5 : ¬∀ {s : String.Slice} {p₀ q r : s.Pos} {h₁ : p₀ ≤ q}, p₀ ≤ r := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pattern.Model.ForwardStringSearcher.offset_of_isLongestRevMatchAt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardStringSearcher.offset_of_isLongestRevMatchAt.h5 : ¬∀ {pat : String} {s : String.Slice} {pos₁ pos₂ : s.Pos},
        pat ≠ "" → pos₂.offset = pos₁.offset.increaseBy pat.utf8ByteSize := fun hc_h => absurd (@hc_h ("a") ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.sliceTo_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceTo_inj.h4 : ¬∀ {s : String.Slice} {p₀ pos pos' : s.Pos} {h' : pos' ≤ p₀}, pos ≤ p₀ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.sliceTo_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceTo_inj.h5 : ¬∀ {s : String.Slice} {p₀ pos pos' : s.Pos} {h : pos ≤ p₀}, pos' ≤ p₀ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Pos.cast_cast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.cast_cast.h3 : ¬∀ {s t u : String} {htu : t = u} {pos : s.Pos}, s = t := fun hc_h => absurd (@hc_h ("") ("a") ("a") rfl ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Pos.cast_cast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.cast_cast.h4 : ¬∀ {s t u : String} {hst : s = t} {pos : s.Pos}, t = u := fun hc_h => absurd (@hc_h ("") ("") ("a") rfl ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.Pos.ofSlice_slice, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSlice_slice.h4 : ¬∀ {s : String.Slice} {p₀ p₁ pos : s.Pos} {h₂ : pos ≤ p₁}, p₀ ≤ pos := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.ofSlice_slice, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSlice_slice.h5 : ¬∀ {s : String.Slice} {p₀ p₁ pos : s.Pos} {h₁ : p₀ ≤ pos}, pos ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Pos.le_trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.le_trans.h4 : ¬∀ {s : String} {p q r : s.Pos}, q ≤ r → p ≤ r := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.le_trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.le_trans.h5 : ¬∀ {s : String} {p q r : s.Pos}, p ≤ q → p ≤ r := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.offset_slice, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.offset_slice.h4 : ¬∀ {s : String} {p₀ p₁ pos : s.Pos} {h₂ : pos ≤ p₁}, p₀ ≤ pos := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.offset_slice, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.offset_slice.h5 : ¬∀ {s : String} {p₀ p₁ pos : s.Pos} {h₁ : p₀ ≤ pos}, pos ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.ofSlice_inj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSlice_inj.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.offset_ofStr, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.offset_ofStr.h2 : ¬∀ {s : String.Slice} {pos : s.str.Pos} {h₂ : pos ≤ s.endExclusive}, s.startInclusive ≤ pos := fun hc_h => absurd (@hc_h ("abc".toSlice.drop 1 : String.Slice) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("abc".toSlice.drop 1).str.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.offset_ofStr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.offset_ofStr.h3 : ¬∀ {s : String.Slice} {pos : s.str.Pos} {h₁ : s.startInclusive ≤ pos}, pos ≤ s.endExclusive := fun hc_h => absurd (@hc_h ("abc".toSlice.take 2 : String.Slice) ({ offset := { byteIdx := 3 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("abc".toSlice.take 2).str.Pos }) (by
  decide)) (by
  decide)

-- String.Pos.ofSlice_lt_ofSlice_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSlice_lt_ofSlice_iff.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.ofSlice_lt_ofSlice_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSlice_lt_ofSlice_iff.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.ofSlice_le_ofSlice_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSlice_le_ofSlice_iff.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.sliceTo_lt_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceTo_lt_iff.h4 : ¬∀ {s : String.Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos}, q ≤ p₀ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("ab".toSlice.sliceTo
          { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "ab".toSlice.Pos }).Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.le_sliceFrom_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.le_sliceFrom_iff.h4 : ¬∀ {s : String.Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("ab".toSlice.sliceFrom
          { offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "ab".toSlice.Pos }).Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.Splits.copy_sliceTo_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.copy_sliceTo_eq.h4 : ¬∀ {t₁ : String} {t₂ : String} {s : String} {p : s.Pos}, (s.sliceTo p).copy = t₁ := fun hc_h => absurd (@hc_h ("a") ("") ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.Pos.Splits.toByteArray_eq_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.toByteArray_eq_left.h4 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ : String} {t₂ : String},
        t₁.toByteArray = s.copy.toByteArray.extract 0 p.offset.byteIdx := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("a") ("")) (by
  decide)

-- String.Pos.Splits.offset_eq_rawEndPos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.offset_eq_rawEndPos.h4 : ¬∀ {s : String} {p : s.Pos} {t₁ : String} {t₂ : String}, p.offset = t₁.rawEndPos := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("a") ("")) (by
  decide)

-- String.Slice.startInclusive_subslice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.startInclusive_subslice.h3 : ¬∀ {s : String.Slice} {newStart newEnd : s.Pos}, newStart ≤ newEnd := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.ofSlice_startPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSlice_startPos.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.le_of_not_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.le_of_not_lt.h3 : ¬∀ {s : String.Slice} {p q : s.Pos}, p ≤ q := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.cast_eq_startPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.cast_eq_startPos.h3 : ¬∀ {s t : String.Slice} {p : s.Pos}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Pos.offset_sliceFrom, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.offset_sliceFrom.h3 : ¬∀ {s : String} {p₀ pos : s.Pos}, p₀ ≤ pos := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.cast_eq_endPos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.cast_eq_endPos.h2 : ¬∀ {s t : String} {p : s.Pos}, s = t := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.startInclusive_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.startInclusive_slice.h3 : ¬∀ {s : String.Slice} {newStart newEnd : s.Pos}, newStart ≤ newEnd := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.offset_add_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.offset_add_slice.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.eq_append_of_dropSuffix?_slice_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.eq_append_of_dropSuffix?_slice_eq_some.h3 : ¬∀ {pat s res : String.Slice}, s.copy = res.copy ++ pat.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("".toSlice : String.Slice) ("ab".toSlice : String.Slice)) (by
  decide)

-- String.Pos.ext, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ext.h3 : ¬∀ {s : String} {x y : s.Pos}, x = y := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

