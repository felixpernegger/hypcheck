import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- String.Slice.Pos.slice_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.slice_inj.h5 : ¬∀ {s : String.Slice} {p₀ p₁ pos pos' : s.Pos} {h₁' : p₀ ≤ pos'} {h₂ : pos ≤ p₁} {h₂' : pos' ≤ p₁}, p₀ ≤ pos := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.slice_inj, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.slice_inj.h6 : ¬∀ {s : String.Slice} {p₀ p₁ pos pos' : s.Pos} {h₁ : p₀ ≤ pos} {h₂ : pos ≤ p₁} {h₂' : pos' ≤ p₁}, p₀ ≤ pos' := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.slice_inj, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.slice_inj.h7 : ¬∀ {s : String.Slice} {p₀ p₁ pos pos' : s.Pos} {h₁ : p₀ ≤ pos} {h₁' : p₀ ≤ pos'} {h₂' : pos' ≤ p₁}, pos ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.slice_inj, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.slice_inj.h8 : ¬∀ {s : String.Slice} {p₀ p₁ pos pos' : s.Pos} {h₁ : p₀ ≤ pos} {h₁' : p₀ ≤ pos'} {h₂ : pos ≤ p₁}, pos' ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.Splits.of_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.of_eq.h6 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ t₂ t₃ t₄ : String}, t₁ = t₃ → t₂ = t₄ → p.Splits t₃ t₄ := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("a") ("") ("a") rfl rfl) (by
  simp)

-- String.Slice.Pos.Splits.of_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.of_eq.h7 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ t₂ t₃ t₄ : String}, p.Splits t₁ t₂ → t₂ = t₄ → p.Splits t₃ t₄ := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("") ("a") ("") ((@String.Slice.Pos.Splits.mk ("".toSlice) (@String.Slice.Pos.mk "".toSlice { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide))) rfl) (by
  simp)

-- String.Slice.Pos.Splits.of_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.of_eq.h8 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ t₂ t₃ t₄ : String}, p.Splits t₁ t₂ → t₁ = t₃ → p.Splits t₃ t₄ := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("") ("") ("a") ((@String.Slice.Pos.Splits.mk ("".toSlice) (@String.Slice.Pos.mk "".toSlice { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide))) rfl) (by
  simp)

-- String.Pos.Splits.le_iff_exists_eq_append, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.le_iff_exists_eq_append.h7 : ¬∀ {s : String} {p₁ p₂ : s.Pos} {t₁ t₂ t₃ t₄ : String},
        p₂.Splits t₃ t₄ → (p₁ ≤ p₂ ↔ ∃ (t₅ : String), t₃ = t₁ ++ t₅ ∧ t₂ = t₅ ++ t₄) := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("a") ("") ("") ((@String.Pos.Splits.mk ("") (@String.Pos.mk "" { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
        (@String.instDecidableIsValid "" { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
              (@String.instDecidableIsValid "" { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  simp)

-- String.Pos.Splits.le_iff_exists_eq_append, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.le_iff_exists_eq_append.h8 : ¬∀ {s : String} {p₁ p₂ : s.Pos} {t₁ t₂ t₃ t₄ : String},
        p₁.Splits t₁ t₂ → (p₁ ≤ p₂ ↔ ∃ (t₅ : String), t₃ = t₁ ++ t₅ ∧ t₂ = t₅ ++ t₄) := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("") ("") ("a") ((@String.Pos.Splits.mk ("") (@String.Pos.mk "" { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
        (@String.instDecidableIsValid "" { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
              (@String.instDecidableIsValid "" { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  simp)

-- String.Pos.Raw.IsValid.set_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.IsValid.set_of_le.h3 : ¬∀ {s : String} {p : s.Pos} {c : Char} {q : String.Pos.Raw}, String.Pos.Raw.IsValid s q → q ≤ p.offset → p ≠ s.endPos := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ('a') ({ : String.Pos.Raw }) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide)

-- String.Pos.Raw.IsValid.set_of_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.IsValid.set_of_le.h6 : ¬∀ {s : String} {p : s.Pos} {c : Char} {hp : p ≠ s.endPos} {q : String.Pos.Raw},
        String.Pos.Raw.IsValid s q → String.Pos.Raw.IsValid (p.set c hp) q := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h ("é") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "é".Pos }) ('a') hc_k0 ({ byteIdx := 2 : String.Pos.Raw }) hc_k1) (by
  decide)

-- String.Slice.Pos.Splits.pos_eq_of_eq_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.pos_eq_of_eq_right.h6 : ¬∀ {s : String.Slice} {p q : s.Pos} {s_1 : String} {s' t : String}, q.Splits s' t → p = q := fun hc_h => absurd (@hc_h ("a".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "a".toSlice.Pos }) ("") ("a") ("") ((@String.Slice.Pos.Splits.mk ("a".toSlice) (@String.Slice.Pos.mk "a".toSlice { byteIdx := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : String.Pos.Raw }
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

-- String.Slice.Pos.Splits.pos_eq_of_eq_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.pos_eq_of_eq_right.h7 : ¬∀ {s : String.Slice} {p q : s.Pos} {s_1 : String} {s' : String} {t : String}, p.Splits s_1 t → p = q := fun hc_h => absurd (@hc_h ("a".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "a".toSlice.Pos }) ("") ("") ("a") ((@String.Slice.Pos.Splits.mk ("a".toSlice) (@String.Slice.Pos.mk "a".toSlice { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValidForSlice "a".toSlice { : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "a".toSlice { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValidForSlice "a".toSlice { : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "a".toSlice { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("a") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Pos.Splits.pos_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.pos_eq.h6 : ¬∀ {s : String} {p q : s.Pos} {s_1 : String} {t : String} {t' : String}, q.Splits s_1 t' → p = q := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ("a") ("") ("") ((@String.Pos.Splits.mk ("a") (@String.Pos.mk "a" { byteIdx := @OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)) : String.Pos.Raw }
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

-- String.Pos.Splits.pos_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.pos_eq.h7 : ¬∀ {s : String} {p q : s.Pos} {s_1 t : String} {t' : String}, p.Splits s_1 t → p = q := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ("") ("a") ("") ((@String.Pos.Splits.mk ("a") (@String.Pos.mk "a" { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValid "a" { : String.Pos.Raw })
        (@String.instDecidableIsValid "a" { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValid "a" { : String.Pos.Raw })
              (@String.instDecidableIsValid "a" { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("a") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Pos.Splits.eq_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.eq_right.h6 : ¬∀ {s : String} {p : s.Pos} {t₁ : String} {t₂ t₃ t₄ : String}, p.Splits t₃ t₄ → t₂ = t₄ := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("a") ("") ("") ((@String.Pos.Splits.mk ("") (@String.Pos.mk "" { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
        (@String.instDecidableIsValid "" { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
              (@String.instDecidableIsValid "" { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Pos.Splits.eq_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.eq_right.h7 : ¬∀ {s : String} {p : s.Pos} {t₁ t₂ : String} {t₃ : String} {t₄ : String}, p.Splits t₁ t₂ → t₂ = t₄ := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("") ("") ("a") ((@String.Pos.Splits.mk ("") (@String.Pos.mk "" { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
        (@String.instDecidableIsValid "" { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValid "" { : String.Pos.Raw })
              (@String.instDecidableIsValid "" { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Slice.Pattern.Internal.memcmpSlice_eq_true_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.Internal.memcmpSlice_eq_true_iff.h5 : ¬∀ {lhs rhs : String.Slice} {lstart rstart : String.Pos.Raw} {len : Nat} {h₂ : rstart.increaseBy len ≤ rhs.rawEndPos},
        lstart.increaseBy len ≤ lhs.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw }) ({ : String.Pos.Raw }) (0) (by
  decide)) (by
  decide)

-- String.Slice.Pattern.Internal.memcmpSlice_eq_true_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.Internal.memcmpSlice_eq_true_iff.h6 : ¬∀ {lhs rhs : String.Slice} {lstart rstart : String.Pos.Raw} {len : Nat} {h₁ : lstart.increaseBy len ≤ lhs.rawEndPos},
        rstart.increaseBy len ≤ rhs.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("".toSlice : String.Slice) ({ : String.Pos.Raw }) ({ byteIdx := 1 : String.Pos.Raw }) (0) (by
  decide)) (by
  decide)

-- String.Slice.Pos.lt_trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.lt_trans.h4 : ¬∀ {s : String.Slice} {p q r : s.Pos}, q < r → p < r := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.lt_trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.lt_trans.h5 : ¬∀ {s : String.Slice} {p q r : s.Pos}, p < q → p < r := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.ofSlice_next, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSlice_next.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pattern.Model.ForwardSliceSearcher.offset_of_isLongestMatchAt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.offset_of_isLongestMatchAt.h5 : ¬∀ {pat s : String.Slice} {pos₁ pos₂ : s.Pos},
        pat.isEmpty = Bool.false → pos₂.offset = pos₁.offset.increaseBy pat.utf8ByteSize := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.next_le_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.next_le_of_lt.h4 : ¬∀ {s : String.Slice} {p q : s.Pos} {h : p ≠ s.endPos}, p.next h ≤ q := fun hc_h => absurd (fun hc_k0 => @hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) hc_k0) (by
  decide)

-- String.Slice.Pos.ne_endPos_of_sliceTo_ne_endPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ne_endPos_of_sliceTo_ne_endPos.h3 : ¬∀ {s : String.Slice} {p p₀ : s.Pos}, p ≤ p₀ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.ne_startPos_of_sliceFrom_ne_startPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ne_startPos_of_sliceFrom_ne_startPos.h3 : ¬∀ {s : String.Slice} {p p₀ : s.Pos}, p₀ ≤ p := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.ne_startPos_of_sliceFrom_ne_startPos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ne_startPos_of_sliceFrom_ne_startPos.h4 : ¬∀ {s : String.Slice} {p p₀ : s.Pos} {h₀ : p₀ ≤ p}, p ≠ s.startPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Subslice.ext, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Subslice.ext.h3 : ¬∀ {s : String.Slice} {x y : s.Subslice}, x.endExclusive = y.endExclusive → x = y := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({
      startInclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      endExclusive :=
        { offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      startInclusive_le_endExclusive := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Subslice }) ({
      startInclusive :=
        { offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      endExclusive :=
        { offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      startInclusive_le_endExclusive := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Subslice }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  (simp <;> decide))

-- String.Slice.Subslice.ext, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Subslice.ext.h4 : ¬∀ {s : String.Slice} {x y : s.Subslice}, x.startInclusive = y.startInclusive → x = y := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({
      startInclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      endExclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      startInclusive_le_endExclusive := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Subslice }) ({
      startInclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      endExclusive :=
        { offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      startInclusive_le_endExclusive := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Subslice }) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  (simp <;> decide))

-- String.toList_mapAux, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.toList_mapAux.h5 : ¬∀ {t₁ t₂ : String} {f : Char → Char} {s : String} {p : s.Pos},
        (String.mapAux f s p).toList = t₁.toList ++ List.map f t₂.toList := fun hc_h => absurd (@hc_h ("") ("") (fun (a : Char) => 'a') ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide +kernel)

-- String.Pos.lt_ofSlice_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.lt_ofSlice_iff.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos} {q : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.posGT_eq_next, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.posGT_eq_next.h3 : ¬∀ {s : String} {p : String.Pos.Raw} {h : p < s.rawEndPos}, String.Pos.Raw.IsValid s p := fun hc_h => absurd (@hc_h ("é") ({ byteIdx := 1 : String.Pos.Raw }) (by
  decide)) (by
  decide)

-- String.Pos.Splits.prevn, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.prevn.h4 : ¬∀ {s t₁ t₂ : String} {p : s.Pos} (n : Nat),
        (p.prevn n).Splits (String.ofList (List.take (t₁.toList.length - n) t₁.toList))
          (String.ofList (List.drop (t₁.toList.length - n) t₁.toList) ++ t₂) := fun hc_h => absurd (@hc_h ("") ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) (0)) (by
  simp)

-- String.Pos.Splits.splits_rotateLeft, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.splits_rotateLeft.h5 : ¬∀ {s : String} {p : s.Pos} {t₁ t₂ t₃ : String}, p.Splits (t₁ ++ t₂) t₃ := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("") ("a")) (by
  simp)

-- String.Slice.Pos.le_sliceTo_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.le_sliceTo_iff.h4 : ¬∀ {s : String.Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos}, q ≤ p₀ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("ab".toSlice.sliceTo
          { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "ab".toSlice.Pos }).Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.le_sliceFrom_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.le_sliceFrom_iff.h4 : ¬∀ {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("a".sliceFrom
          { offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "a".Pos }).Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.Splits.toByteArray_eq_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.toByteArray_eq_right.h4 : ¬∀ {s : String} {p : s.Pos} {t₁ : String} {t₂ : String},
        t₂.toByteArray = s.toByteArray.extract p.offset.byteIdx s.toByteArray.size := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("a")) (by
  decide)

-- String.Pos.Splits.eq_startPos_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.eq_startPos_iff.h4 : ¬∀ {t₁ : String} {t₂ : String} {s : String} {p : s.Pos}, p = s.startPos ↔ t₁ = "" := fun hc_h => absurd (@hc_h ("a") ("") ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.Pos.Splits.copy, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.copy.h4 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ t₂ : String}, p.copy.Splits t₁ t₂ := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("a")) (by
  simp)

-- String.Slice.Pos.Splits.eq_append, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.eq_append.h4 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ t₂ : String}, s.copy = t₁ ++ t₂ := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("a")) (by
  decide)

-- String.Slice.Pos.Splits.toByteArray_eq_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.toByteArray_eq_right.h4 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ : String} {t₂ : String},
        t₂.toByteArray = s.copy.toByteArray.extract p.offset.byteIdx s.copy.toByteArray.size := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("a")) (by
  decide)

-- String.Slice.endExclusive_subslice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.endExclusive_subslice.h3 : ¬∀ {s : String.Slice} {newStart newEnd : s.Pos}, newStart ≤ newEnd := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.offset_cast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.offset_cast.h3 : ¬∀ {s t : String} {pos : s.Pos}, s = t := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.startInclusive_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.startInclusive_slice.h3 : ¬∀ {s : String} {startInclusive endExclusive : s.Pos}, startInclusive ≤ endExclusive := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.offset_sliceTo, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.offset_sliceTo.h3 : ¬∀ {s : String} {p₀ pos : s.Pos}, pos ≤ p₀ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.extract_eq_copy_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.extract_eq_copy_slice.h3 : ¬∀ {s : String} (p₀ p₁ : s.Pos), p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.cast_eq_startPos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.cast_eq_startPos.h2 : ¬∀ {s t : String} {p : s.Pos}, s = t := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.utf8ByteSize_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.utf8ByteSize_slice.h3 : ¬∀ {s : String} {p₁ p₂ : s.Pos}, p₁ ≤ p₂ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.skipSuffix?_slice_of_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.skipSuffix?_slice_of_isEmpty.h2 : ¬∀ {pat s : String.Slice}, s.skipSuffix? pat = Option.some s.endPos := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ("".toSlice : String.Slice)) (by
  decide)

-- String.Slice.startsWith_slice_of_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.startsWith_slice_of_isEmpty.h2 : ¬∀ {pat s : String.Slice}, s.startsWith pat = Bool.true := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ("".toSlice : String.Slice)) (by
  decide)

-- String.Slice.Pattern.ForwardSliceSearcher.getElem_buildTable_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.ForwardSliceSearcher.getElem_buildTable_le.h2 : ¬∀ (pat : String.Slice) (i : Nat), i < pat.utf8ByteSize := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) (0)) (by
  decide)

-- String.Pos.get?_eq_none, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.get?_eq_none.h2 : ¬∀ {s : String} {p : s.Pos}, p.get? = Option.none := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.posLE_eq_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posLE_eq_pos.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, String.Pos.Raw.IsValidForSlice s p := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw })) (by
  decide)

-- String.Slice.posGE_eq_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posGE_eq_pos.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, String.Pos.Raw.IsValidForSlice s p := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw })) (by
  decide)

-- String.Slice.le_offset_posGE, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.le_offset_posGE.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, p ≤ s.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw })) (by
  decide)

-- String.Slice.getUTF8Byte_eq_getUTF8Byte_copy, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.getUTF8Byte_eq_getUTF8Byte_copy.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, p < s.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw })) (by
  decide)

-- String.Slice.posLE_dec, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posLE_dec.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, 0 < p := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw })) (by
  decide)

-- String.Slice.Pos.cast_startPos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.cast_startPos.h2 : ¬∀ {s t : String.Slice}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice)) (by
  decide)

-- String.Pos.Raw.isValidForSlice_prevAuxGo, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.isValidForSlice_prevAuxGo.h2 : ¬∀ {s : String.Slice} (off : Nat), off < s.utf8ByteSize := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) (0)) (by
  decide)

-- String.Slice.Pattern.BackwardSliceSearcher.skipSuffix?_of_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.BackwardSliceSearcher.skipSuffix?_of_isEmpty.h2 : ¬∀ {pat s : String.Slice}, String.Slice.Pattern.BackwardPattern.skipSuffix? pat s = Option.some s.endPos := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ("".toSlice : String.Slice)) (by
  decide)

-- String.Slice.Pattern.ForwardSliceSearcher.skipPrefix?_of_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.ForwardSliceSearcher.skipPrefix?_of_isEmpty.h2 : ¬∀ {pat s : String.Slice}, String.Slice.Pattern.ForwardPattern.skipPrefix? pat s = Option.some s.startPos := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ("".toSlice : String.Slice)) (by
  decide)

-- String.Pos.Raw.IsValid.isValidUTF8_extract_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.IsValid.isValidUTF8_extract_zero.h2 : ¬∀ {s : String} {off : String.Pos.Raw}, (s.toByteArray.extract 0 off.byteIdx).IsValidUTF8 := fun hc_h => absurd (@hc_h ("é") ({ byteIdx := 1 : String.Pos.Raw })) (by
  decide)

-- String.Slice.startPos_ne_endPos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.startPos_ne_endPos.h1 : ¬∀ {s : String.Slice}, s.startPos ≠ s.endPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice)) (by
  decide)

