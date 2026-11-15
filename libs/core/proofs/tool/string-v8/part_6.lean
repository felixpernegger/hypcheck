import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- String.Pos.slice_lt_slice_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.slice_lt_slice_iff.h5 : ¬∀ {s : String} {p₀ p₁ q r : s.Pos} {h₁' : p₀ ≤ r} {h₂ : q ≤ p₁} {h₂' : r ≤ p₁}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Pos.slice_lt_slice_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.slice_lt_slice_iff.h6 : ¬∀ {s : String} {p₀ p₁ q r : s.Pos} {h₁ : p₀ ≤ q} {h₂ : q ≤ p₁} {h₂' : r ≤ p₁}, p₀ ≤ r := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Pos.slice_lt_slice_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.slice_lt_slice_iff.h7 : ¬∀ {s : String} {p₀ p₁ q r : s.Pos} {h₁ : p₀ ≤ q} {h₁' : p₀ ≤ r} {h₂' : r ≤ p₁}, q ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Pos.slice_lt_slice_iff, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.slice_lt_slice_iff.h8 : ¬∀ {s : String} {p₀ p₁ q r : s.Pos} {h₁ : p₀ ≤ q} {h₁' : p₀ ≤ r} {h₂ : q ≤ p₁}, r ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Pos.Splits.eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.eq.h6 : ¬∀ {s : String} {p : s.Pos} {t₁ t₂ t₃ t₄ : String}, p.Splits t₃ t₄ → t₁ = t₃ ∧ t₂ = t₄ := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("a") ("") ("") ((@String.Pos.Splits.mk ("") (@String.Pos.mk "" { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
        (@String.instDecidableIsValid "" { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
              (@String.instDecidableIsValid "" { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Pos.Splits.eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.eq.h7 : ¬∀ {s : String} {p : s.Pos} {t₁ t₂ t₃ t₄ : String}, p.Splits t₁ t₂ → t₁ = t₃ ∧ t₂ = t₄ := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("") ("") ("a") ((@String.Pos.Splits.mk ("") (@String.Pos.mk "" { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
        (@String.instDecidableIsValid "" { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
              (@String.instDecidableIsValid "" { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Slice.Pos.Splits.eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.eq.h6 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ t₂ t₃ t₄ : String}, p.Splits t₃ t₄ → t₁ = t₃ ∧ t₂ = t₄ := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("a") ("") ("") ((@String.Slice.Pos.Splits.mk ("".toSlice) (@String.Slice.Pos.mk "".toSlice { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Slice.Pos.Splits.eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.eq.h7 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ t₂ t₃ t₄ : String}, p.Splits t₁ t₂ → t₁ = t₃ ∧ t₂ = t₄ := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("") ("") ("a") ((@String.Slice.Pos.Splits.mk ("".toSlice) (@String.Slice.Pos.mk "".toSlice { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Pos.Splits.cast, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.cast.h5 : ¬∀ {s₁ s₂ : String} {p : s₁.Pos} {t₁ t₂ : String}, p.Splits t₁ t₂ → s₁ = s₂ := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("") ((@String.Pos.Splits.mk ("") (@String.Pos.mk "" { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
        (@String.instDecidableIsValid "" { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
              (@String.instDecidableIsValid "" { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Pos.Splits.cast, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.cast.h6 : ¬∀ {s₁ s₂ : String} {p : s₁.Pos} {t₁ t₂ : String} (h : s₁ = s₂), (p.cast h).Splits t₁ t₂ := fun hc_h => absurd (@hc_h ("") ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("a") rfl) (by
  simp)

-- String.Slice.Pos.Splits.cast, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.cast.h5 : ¬∀ {s₁ s₂ : String.Slice} {p : s₁.Pos} {t₁ t₂ : String}, p.Splits t₁ t₂ → s₁.copy = s₂.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("") ((@String.Slice.Pos.Splits.mk ("".toSlice) (@String.Slice.Pos.mk "".toSlice { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Slice.Pos.Splits.cast, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.cast.h6 : ¬∀ {s₁ s₂ : String.Slice} {p : s₁.Pos} {t₁ t₂ : String} (h : s₁.copy = s₂.copy), (p.cast h).Splits t₁ t₂ := fun hc_h => absurd (fun hc_k0 => @hc_h ("".toSlice : String.Slice) ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("a") hc_k0) (by
  simp)

-- String.Pos.Splits.of_next, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.of_next.h6 : ¬∀ {t₁ : String} {c : Char} {t₂ s : String} {p : s.Pos} {hp : p ≠ s.endPos}, p.Splits t₁ (String.singleton c ++ t₂) := fun hc_h => absurd (@hc_h ("") ('a') ("") ("0") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "0".Pos }) (by
  decide)) (by
  simp)

-- String.Pos.sliceTo_le_sliceTo_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceTo_le_sliceTo_iff.h4 : ¬∀ {s : String} {p₀ q r : s.Pos} {h₂ : r ≤ p₀}, q ≤ p₀ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.sliceTo_le_sliceTo_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceTo_le_sliceTo_iff.h5 : ¬∀ {s : String} {p₀ q r : s.Pos} {h₁ : q ≤ p₀}, r ≤ p₀ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.ofSlice_ne_endPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSlice_ne_endPos.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.sliceFrom_le_sliceFrom_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceFrom_le_sliceFrom_iff.h4 : ¬∀ {s : String} {p₀ q r : s.Pos} {h₂ : p₀ ≤ r}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.sliceFrom_le_sliceFrom_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceFrom_le_sliceFrom_iff.h5 : ¬∀ {s : String} {p₀ q r : s.Pos} {h₁ : p₀ ≤ q}, p₀ ≤ r := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.sliceFrom_lt_sliceFrom_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceFrom_lt_sliceFrom_iff.h4 : ¬∀ {s : String} {p₀ q r : s.Pos} {h₂ : p₀ ≤ r}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.sliceFrom_lt_sliceFrom_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceFrom_lt_sliceFrom_iff.h5 : ¬∀ {s : String} {p₀ q r : s.Pos} {h₁ : p₀ ≤ q}, p₀ ≤ r := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.ofSlice_ne_startPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSlice_ne_startPos.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pattern.Model.ForwardStringSearcher.offset_of_isLongestMatchAt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardStringSearcher.offset_of_isLongestMatchAt.h5 : ¬∀ {pat : String} {s : String.Slice} {pos₁ pos₂ : s.Pos},
        pat ≠ "" → pos₂.offset = pos₁.offset.increaseBy pat.utf8ByteSize := fun hc_h => absurd (@hc_h ("a") ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.Splits.exists_eq_append_singleton, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.exists_eq_append_singleton.h5 : ¬∀ {t₁ : String} {t₂ : String} {s : String.Slice} {p : s.Pos} (hp : p ≠ s.endPos),
        ∃ (t₁' : String), t₁ = t₁' ++ String.singleton (p.get hp) := fun hc_h => absurd (fun hc_k0 => @hc_h ("") ("") ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) hc_k0) (by
  (simp <;> decide))

-- String.Pos.Splits.exists_eq_append_singleton, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.exists_eq_append_singleton.h5 : ¬∀ {t₁ : String} {t₂ : String} {s : String} {p : s.Pos} (hp : p ≠ s.endPos),
        ∃ (t₁' : String), t₁ = t₁' ++ String.singleton (p.get hp) := fun hc_h => absurd (fun hc_k0 => @hc_h ("") ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) hc_k0) (by
  (simp <;> decide))

-- String.Slice.Pos.sliceFrom_cast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceFrom_cast.h2 : ¬∀ {s t : String.Slice} (p q : s.Pos), s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.sliceFrom_cast, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceFrom_cast.h5 : ¬∀ {s t : String.Slice} {hst : s.copy = t.copy} (p q : s.Pos), p.cast hst ≤ q.cast hst := fun hc_h => absurd (fun hc_k0 => @hc_h ("ab".toSlice : String.Slice) ("ab".toSlice : String.Slice) hc_k0 ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.Splits.exists_eq_singleton_append, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.exists_eq_singleton_append.h4 : ¬∀ {t₁ t₂ : String} {s : String.Slice} {p : s.Pos}, p.Splits t₁ t₂ → p ≠ s.endPos := fun hc_h => absurd (@hc_h ("") ("") ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ((@String.Slice.Pos.Splits.mk ("".toSlice) (@String.Slice.Pos.mk "".toSlice { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Slice.Pos.Splits.exists_eq_singleton_append, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.exists_eq_singleton_append.h5 : ¬∀ {t₁ : String} {t₂ : String} {s : String.Slice} {p : s.Pos} (hp : p ≠ s.endPos),
        ∃ (t₂' : String), t₂ = String.singleton (p.get hp) ++ t₂' := fun hc_h => absurd (fun hc_k0 => @hc_h ("") ("") ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) hc_k0) (by
  (simp <;> decide))

-- String.Slice.Pos.sliceTo_cast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceTo_cast.h2 : ¬∀ {s t : String.Slice} (p q : s.Pos), s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.sliceTo_cast, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceTo_cast.h5 : ¬∀ {s t : String.Slice} {hst : s.copy = t.copy} (p q : s.Pos), q.cast hst ≤ p.cast hst := fun hc_h => absurd (fun hc_k0 => @hc_h ("ab".toSlice : String.Slice) ("ab".toSlice : String.Slice) hc_k0 ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.Splits.exists_eq_singleton_append, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.exists_eq_singleton_append.h5 : ¬∀ {t₁ : String} {t₂ s : String} {p : s.Pos} (hp : p ≠ s.endPos),
        ∃ (t₂' : String), t₂ = String.singleton (p.get hp) ++ t₂' := fun hc_h => absurd (fun hc_k0 => @hc_h ("") ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) hc_k0) (by
  (simp <;> decide))

-- String.Pos.Splits.exists_eq_singleton_append_of_ne_startPos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.exists_eq_singleton_append_of_ne_startPos.h5 : ¬∀ {t₁ : String} {t₂ s : String} {p : s.Pos} (hp : p ≠ s.startPos),
        ∃ (t₂' : String),
          t₂ =
            String.singleton
                ((p.prev hp).get
                  ((fun {s : String} (p : s.Pos) (hp : p ≠ s.startPos) =>
                      of_eq_true (Eq.trans (congrArg Not String.Pos.prev_ne_endPos._simp_1) not_false_eq_true))
                    p hp)) ++
              t₂' := fun hc_h => absurd (fun hc_k0 => @hc_h ("") ("") ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) hc_k0) (by
  (simp <;> decide))

-- String.Slice.Pos.Splits.exists_eq_singleton_append_of_ne_startPos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.exists_eq_singleton_append_of_ne_startPos.h5 : ¬∀ {t₁ : String} {t₂ : String} {s : String.Slice} {p : s.Pos} (hp : p ≠ s.startPos),
        ∃ (t₂' : String),
          t₂ =
            String.singleton
                ((p.prev hp).get
                  ((fun {s : String.Slice} (p : s.Pos) (hp : p ≠ s.startPos) =>
                      of_eq_true (Eq.trans (congrArg Not String.Slice.Pos.prev_ne_endPos._simp_1) not_false_eq_true))
                    p hp)) ++
              t₂' := fun hc_h => absurd (fun hc_k0 => @hc_h ("") ("") ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) hc_k0) (by
  (simp <;> decide))

-- String.Pos.Splits.exists_eq_append_singleton_of_ne_startPos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.exists_eq_append_singleton_of_ne_startPos.h5 : ¬∀ {t₁ : String} {t₂ : String} {s : String} {p : s.Pos} (hp : p ≠ s.startPos),
        ∃ (t₁' : String),
          t₁ =
            t₁' ++
              String.singleton
                ((p.prev hp).get
                  ((fun {s : String} (p : s.Pos) (hp : p ≠ s.startPos) =>
                      of_eq_true (Eq.trans (congrArg Not String.Pos.prev_ne_endPos._simp_1) not_false_eq_true))
                    p hp)) := fun hc_h => absurd (fun hc_k0 => @hc_h ("") ("") ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) hc_k0) (by
  (simp <;> decide))

-- String.Pos.lt_of_lt_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.lt_of_lt_of_le.h4 : ¬∀ {s : String} {p q r : s.Pos}, q ≤ r → p < r := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.lt_of_lt_of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.lt_of_lt_of_le.h5 : ¬∀ {s : String} {p q r : s.Pos}, p < q → p < r := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.offset_slice, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.offset_slice.h4 : ¬∀ {s : String.Slice} {p₀ p₁ pos : s.Pos} {h₂ : pos ≤ p₁}, p₀ ≤ pos := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.offset_slice, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.offset_slice.h5 : ¬∀ {s : String.Slice} {p₀ p₁ pos : s.Pos} {h₁ : p₀ ≤ pos}, pos ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Pos.sliceFrom_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceFrom_inj.h4 : ¬∀ {s : String} {p₀ pos pos' : s.Pos} {h' : p₀ ≤ pos'}, p₀ ≤ pos := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.sliceFrom_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceFrom_inj.h5 : ¬∀ {s : String} {p₀ pos pos' : s.Pos} {h : p₀ ≤ pos}, p₀ ≤ pos' := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.ofSlice_slice, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSlice_slice.h4 : ¬∀ {s : String} {p₀ p₁ pos : s.Pos} {h₂ : pos ≤ p₁}, p₀ ≤ pos := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.ofSlice_slice, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSlice_slice.h5 : ¬∀ {s : String} {p₀ p₁ pos : s.Pos} {h₁ : p₀ ≤ pos}, pos ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.offset_toSetOfLE, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.offset_toSetOfLE.h5 : ¬∀ {s : String} {q p : s.Pos} {c : Char} {hp : p ≠ s.endPos}, q ≤ p := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ('a') (by
  decide)) (by
  decide)

-- String.Slice.Pos.get_eq_of_revSkipWhile_le_char, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.get_eq_of_revSkipWhile_le_char.h4 : ¬∀ {c : Char} {s : String.Slice} {pos pos' : s.Pos}, pos.revSkipWhile c ≤ pos' → pos' < pos := fun hc_h => absurd (@hc_h ('a') ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) (by
  simp)) (by
  decide)

-- String.Slice.Pos.get_eq_of_revSkipWhile_le_char, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.get_eq_of_revSkipWhile_le_char.h5 : ¬∀ {c : Char} {s : String.Slice} {pos pos' : s.Pos} (h₁ : pos' < pos),
        pos'.get (String.Slice.Pos.ne_endPos_of_lt h₁) = c := fun hc_h => absurd (fun hc_k0 => @hc_h ('0') ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) hc_k0) (by
  decide)

-- String.Slice.Pos.apply_eq_true_of_revSkipWhile_le_bool, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.apply_eq_true_of_revSkipWhile_le_bool.h4 : ¬∀ {p : Char → Bool} {s : String.Slice} {pos pos' : s.Pos}, pos.revSkipWhile p ≤ pos' → pos' < pos := fun hc_h => absurd (@hc_h (fun (a : Char) => Bool.false) ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) (by
  simp)) (by
  decide)

-- String.Slice.Pos.apply_eq_true_of_revSkipWhile_le_bool, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.apply_eq_true_of_revSkipWhile_le_bool.h5 : ¬∀ {p : Char → Bool} {s : String.Slice} {pos pos' : s.Pos} (h₁ : pos' < pos),
        p (pos'.get (String.Slice.Pos.ne_endPos_of_lt h₁)) = Bool.true := fun hc_h => absurd (fun hc_k0 => @hc_h (fun (a : Char) => Bool.false) ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) hc_k0) (by
  decide)

-- String.Pos.apply_eq_true_of_revSkipWhile_le_bool, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.apply_eq_true_of_revSkipWhile_le_bool.h4 : ¬∀ {p : Char → Bool} {s : String} {pos pos' : s.Pos}, pos.revSkipWhile p ≤ pos' → pos' < pos := fun hc_h => absurd (@hc_h (fun (a : Char) => Bool.false) ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) (by
  simp)) (by
  decide)

-- String.Pos.apply_eq_true_of_revSkipWhile_le_bool, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.apply_eq_true_of_revSkipWhile_le_bool.h5 : ¬∀ {p : Char → Bool} {s : String} {pos pos' : s.Pos} (h₁ : pos' < pos),
        p (pos'.get (String.Pos.ne_endPos_of_lt h₁)) = Bool.true := fun hc_h => absurd (fun hc_k0 => @hc_h (fun (a : Char) => Bool.false) ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) hc_k0) (by
  decide)

-- String.Slice.ext, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.ext.h2 : ¬∀ {s t : String.Slice}, s.str = t.str := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice)) (by
  decide)

-- String.Slice.Pattern.Model.ForwardSliceSearcher.le_of_matchesAt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.le_of_matchesAt.h4 : ¬∀ {pat s : String.Slice} {pos : s.Pos}, pat.isEmpty = Bool.false → pos.offset.increaseBy pat.utf8ByteSize ≤ s.rawEndPos := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.ofSlice_le_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSlice_le_iff.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos} {q : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.le_ofSlice_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.le_ofSlice_iff.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos} {q : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.posLT_eq_prev, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posLT_eq_prev.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, String.Pos.Raw.IsValidForSlice s p → 0 < p := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw }) (by
  decide)) (by
  decide)

-- String.Slice.posLT_eq_prev, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posLT_eq_prev.h3 : ¬∀ {s : String.Slice} {p : String.Pos.Raw} {h : 0 < p}, String.Pos.Raw.IsValidForSlice s p := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw }) (by
  decide)) (by
  decide)

-- String.Pos.Splits.nextn, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.nextn.h4 : ¬∀ {s t₁ t₂ : String} {p : s.Pos} (i : Nat),
        (p.nextn i).Splits (t₁ ++ String.ofList (List.take i t₂.toList)) (String.ofList (List.drop i t₂.toList)) := fun hc_h => absurd (@hc_h ("") ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) (0)) (by
  simp)

-- String.Slice.Pos.Splits.splits_rotateLeft, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.splits_rotateLeft.h5 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ t₂ t₃ : String}, p.Splits (t₁ ++ t₂) t₃ := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("") ("a")) (by
  simp)

-- String.Slice.Pos.Splits.prev, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.prev.h5 : ¬∀ {t₁ : String} {c : Char} {t₂ : String} {s : String.Slice} {p : s.Pos}, p.Splits (t₁ ++ String.singleton c) t₂ := fun hc_h => absurd (@hc_h ("") ('a') ("") ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  simp)

-- String.Pos.lt_next_next, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.lt_next_next.h3 : ¬∀ {s : String} {p : s.Pos} {h : p ≠ s.endPos}, p.next h ≠ s.endPos := fun hc_h => absurd (fun hc_k0 => @hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) hc_k0) (by
  decide)

-- String.Pos.le_sliceTo_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.le_sliceTo_iff.h4 : ¬∀ {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos}, q ≤ p₀ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("a".sliceTo
          { offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }).Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.lt_sliceFrom_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.lt_sliceFrom_iff.h4 : ¬∀ {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("a".sliceFrom
          { offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "a".Pos }).Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.sliceTo_le_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceTo_le_iff.h4 : ¬∀ {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos}, q ≤ p₀ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("a".sliceTo
          { offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }).Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.Splits.eq_append, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.eq_append.h4 : ¬∀ {s : String} {p : s.Pos} {t₁ t₂ : String}, s = t₁ ++ t₂ := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("a")) (by
  decide)

-- String.Pos.Splits.copy_sliceFrom_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.copy_sliceFrom_eq.h4 : ¬∀ {t₁ : String} {t₂ s : String} {p : s.Pos}, (s.sliceFrom p).copy = t₂ := fun hc_h => absurd (@hc_h ("") ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.Splits.eq_startPos_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.eq_startPos_iff.h4 : ¬∀ {t₁ : String} {t₂ : String} {s : String.Slice} {p : s.Pos}, p = s.startPos ↔ t₁ = "" := fun hc_h => absurd (@hc_h ("a") ("") ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Pos.Splits.toByteArray_eq_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.toByteArray_eq_left.h4 : ¬∀ {s : String} {p : s.Pos} {t₁ : String} {t₂ : String}, t₁.toByteArray = s.toByteArray.extract 0 p.offset.byteIdx := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("a") ("")) (by
  decide)

-- String.Slice.Pos.Splits.offset_eq_rawEndPos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.offset_eq_rawEndPos.h4 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ : String} {t₂ : String}, p.offset = t₁.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("a") ("")) (by
  decide)

-- String.Slice.Pos.Splits.eq_endPos_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.eq_endPos_iff.h4 : ¬∀ {t₁ : String} {t₂ : String} {s : String.Slice} {p : s.Pos}, p = s.endPos ↔ t₂ = "" := fun hc_h => absurd (@hc_h ("") ("") ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.ofSlice_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSlice_le.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.cast_lt_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.cast_lt_iff.h4 : ¬∀ {s t : String} {pos : s.Pos} {pos' : t.Pos}, s = t := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.slice_ofSlice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.slice_ofSlice.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.lt_cast_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.lt_cast_iff.h4 : ¬∀ {s t : String.Slice} {pos : t.Pos} {pos' : s.Pos}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.cast_le_cast_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.cast_le_cast_iff.h4 : ¬∀ {s t : String.Slice} {pos pos' : s.Pos}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.le_cast_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.le_cast_iff.h4 : ¬∀ {s t : String.Slice} {pos : t.Pos} {pos' : s.Pos}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.sliceTo_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.sliceTo_slice.h3 : ¬∀ {s : String.Slice} {p₁ p₂ : s.Pos}, p₁ ≤ p₂ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.toByteArray_copy_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.toByteArray_copy_slice.h3 : ¬∀ {s : String.Slice} {p₁ p₂ : s.Pos}, p₁ ≤ p₂ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.copy_eq_copy_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.copy_eq_copy_slice.h3 : ¬∀ {s : String.Slice} {pos₁ pos₂ : s.Pos}, pos₁ ≤ pos₂ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.ofSliceTo_ne_endPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSliceTo_ne_endPos.h3 : ¬∀ {s : String.Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos}, String.Slice.Pos.ofSliceTo p ≠ s.endPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("".toSlice.sliceTo
          { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "".toSlice.Pos }).Pos })) (by
  decide)

-- String.Pos.ofSliceFrom_ne_startPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSliceFrom_ne_startPos.h3 : ¬∀ {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos}, String.Pos.ofSliceFrom p ≠ s.startPos := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("".sliceFrom
          { offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }).Pos })) (by
  decide)

-- String.Slice.Pos.prev_ofSliceTo, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.prev_ofSliceTo.h3 : ¬∀ {s : String.Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos}, String.Slice.Pos.ofSliceTo p ≠ s.startPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("".toSlice.sliceTo
          { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "".toSlice.Pos }).Pos })) (by
  decide)

-- String.Slice.posGT_eq_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posGT_eq_iff.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw} {q : s.Pos}, p < s.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.posLT_eq_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.posLT_eq_iff.h2 : ¬∀ {s : String} {p : String.Pos.Raw} {q : s.Pos}, 0 < p := fun hc_h => absurd (@hc_h ("") ({ : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.lt_posGE_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.lt_posGE_iff.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw} {q : s.Pos}, p ≤ s.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.isEmpty_eq_false_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.isEmpty_eq_false_of_lt.h3 : ¬∀ {s : String.Slice} {p q : s.Pos}, s.isEmpty = Bool.false := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.isEmpty_slice_eq_false_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.isEmpty_slice_eq_false_iff.h3 : ¬∀ {s : String} {p₁ p₂ : s.Pos}, p₁ ≤ p₂ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.eq_next_of_next?_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.eq_next_of_next?_eq_some.h3 : ¬∀ {s : String.Slice} {p q : s.Pos}, p.next? = Option.some q := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.Subslice.endExclusive_extendLeft, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Subslice.endExclusive_extendLeft.h3 : ¬∀ {s : String.Slice} {sl : s.Subslice} {newStart : s.Pos}, newStart ≤ sl.startInclusive := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({
      startInclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      endExclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      startInclusive_le_endExclusive := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Subslice }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.endExclusive_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.endExclusive_slice.h3 : ¬∀ {s : String.Slice} {newStart newEnd : s.Pos}, newStart ≤ newEnd := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.ofSliceFrom_sliceFrom, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSliceFrom_sliceFrom.h3 : ¬∀ {s : String.Slice} {p₀ p : s.Pos}, p₀ ≤ p := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.ofSlice_startPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSlice_startPos.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.endExclusive_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.endExclusive_slice.h3 : ¬∀ {s : String} {startInclusive endExclusive : s.Pos}, startInclusive ≤ endExclusive := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.skipPrefix?_slice_of_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.skipPrefix?_slice_of_isEmpty.h2 : ¬∀ {pat : String.Slice} {s : String}, s.skipPrefix? pat = Option.some s.startPos := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ("")) (by
  decide)

