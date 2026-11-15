import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- String.Slice.Pos.slice_lt_slice_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.slice_lt_slice_iff.h5 : ¬∀ {s : String.Slice} {p₀ p₁ q r : s.Pos} {h₁' : p₀ ≤ r} {h₂ : q ≤ p₁} {h₂' : r ≤ p₁}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.slice_lt_slice_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.slice_lt_slice_iff.h6 : ¬∀ {s : String.Slice} {p₀ p₁ q r : s.Pos} {h₁ : p₀ ≤ q} {h₂ : q ≤ p₁} {h₂' : r ≤ p₁}, p₀ ≤ r := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.slice_lt_slice_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.slice_lt_slice_iff.h7 : ¬∀ {s : String.Slice} {p₀ p₁ q r : s.Pos} {h₁ : p₀ ≤ q} {h₁' : p₀ ≤ r} {h₂' : r ≤ p₁}, q ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.slice_lt_slice_iff, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.slice_lt_slice_iff.h8 : ¬∀ {s : String.Slice} {p₀ p₁ q r : s.Pos} {h₁ : p₀ ≤ q} {h₁' : p₀ ≤ r} {h₂ : q ≤ p₁}, r ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.cast_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.cast_pos.h4 : ¬∀ {s t : String.Slice} {p : String.Pos.Raw} {h : String.Pos.Raw.IsValidForSlice s p}
        {h'' : String.Pos.Raw.IsValidForSlice t p}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ : String.Pos.Raw }) (by
  decide) (by
  decide)) (by
  decide)

-- String.Slice.Pos.Splits.exists_eq_append_singleton_of_ne_startPos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.exists_eq_append_singleton_of_ne_startPos.h4 : ¬∀ {t₁ t₂ : String} {s : String.Slice} {p : s.Pos}, p.Splits t₁ t₂ → p ≠ s.startPos := fun hc_h => absurd (@hc_h ("") ("") ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ((@String.Slice.Pos.Splits.mk ("".toSlice) (@String.Slice.Pos.mk "".toSlice { : String.Pos.Raw }
      (@of_decide_eq_true (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
        (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw })
        (@id
          (@Eq Bool
            (@Decidable.decide (String.Pos.Raw.IsValidForSlice "".toSlice { : String.Pos.Raw })
              (@String.instDecidableIsValidForSlice "".toSlice { : String.Pos.Raw }))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) ("") ("") (by (try dsimp only);   decide) (by (try dsimp only);   decide)))) (by
  decide)

-- String.Slice.Pos.Splits.exists_eq_append_singleton_of_ne_startPos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.exists_eq_append_singleton_of_ne_startPos.h5 : ¬∀ {t₁ : String} {t₂ : String} {s : String.Slice} {p : s.Pos} (hp : p ≠ s.startPos),
        ∃ (t₁' : String),
          t₁ =
            t₁' ++
              String.singleton
                ((p.prev hp).get
                  ((fun {s : String.Slice} (p : s.Pos) (hp : p ≠ s.startPos) =>
                      of_eq_true (Eq.trans (congrArg Not String.Slice.Pos.prev_ne_endPos._simp_1) not_false_eq_true))
                    p hp)) := fun hc_h => absurd (fun hc_k0 => @hc_h ("") ("") ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) hc_k0) (by
  (simp <;> decide))

-- String.Pos.sliceFrom_cast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceFrom_cast.h2 : ¬∀ {s t : String} (p q : s.Pos), s = t := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Pos.sliceFrom_cast, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceFrom_cast.h5 : ¬∀ {s t : String} {hst : s = t} (p q : s.Pos), p.cast hst ≤ q.cast hst := fun hc_h => absurd (@hc_h ("a") ("a") rfl ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.sliceTo_cast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceTo_cast.h2 : ¬∀ {s t : String} (p q : s.Pos), s = t := fun hc_h => absurd (@hc_h ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Pos.sliceTo_cast, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceTo_cast.h5 : ¬∀ {s t : String} {hst : s = t} (p q : s.Pos), q.cast hst ≤ p.cast hst := fun hc_h => absurd (@hc_h ("a") ("a") rfl ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.sliceFrom_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceFrom_inj.h4 : ¬∀ {s : String.Slice} {p₀ pos pos' : s.Pos} {h' : p₀ ≤ pos'}, p₀ ≤ pos := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.sliceFrom_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceFrom_inj.h5 : ¬∀ {s : String.Slice} {p₀ pos pos' : s.Pos} {h : p₀ ≤ pos}, p₀ ≤ pos' := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.cast_cast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.cast_cast.h3 : ¬∀ {s t u : String.Slice} {htu : t.copy = u.copy} {pos : s.Pos}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ("".toSlice : String.Slice) ("".toSlice : String.Slice) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.cast_cast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.cast_cast.h4 : ¬∀ {s t u : String.Slice} {hst : s.copy = t.copy} {pos : s.Pos}, t.copy = u.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Pos.sliceTo_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceTo_inj.h4 : ¬∀ {s : String} {p₀ pos pos' : s.Pos} {h' : pos' ≤ p₀}, pos ≤ p₀ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Pos.sliceTo_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceTo_inj.h5 : ¬∀ {s : String} {p₀ pos pos' : s.Pos} {h : pos ≤ p₀}, pos' ≤ p₀ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.le_trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.le_trans.h4 : ¬∀ {s : String.Slice} {p q r : s.Pos}, q ≤ r → p ≤ r := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Pos.le_trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.le_trans.h5 : ¬∀ {s : String.Slice} {p q r : s.Pos}, p ≤ q → p ≤ r := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) (by
  decide)) (by
  decide)

-- String.Slice.Subslice.extendLeft_extendLeft, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Subslice.extendLeft_extendLeft.h4 : ¬∀ {s : String.Slice} {sl : s.Subslice} (p₁ p₂ : s.Pos), p₂ ≤ sl.startInclusive := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({
      startInclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      endExclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      startInclusive_le_endExclusive := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Subslice }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Subslice.extendLeft_extendLeft, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Subslice.extendLeft_extendLeft.h5 : ¬∀ {s : String.Slice} {sl : s.Subslice} (p₁ p₂ : s.Pos) (h₂ : p₂ ≤ sl.startInclusive),
        p₁ ≤ (sl.extendLeft p₂ h₂).startInclusive := fun hc_h => absurd (fun hc_k0 => @hc_h ("ab".toSlice : String.Slice) ({
      startInclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      endExclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      startInclusive_le_endExclusive := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Subslice }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) hc_k0) (by
  decide)

-- String.Pos.ne_endPos_of_sliceTo_ne_endPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ne_endPos_of_sliceTo_ne_endPos.h3 : ¬∀ {s : String} {p p₀ : s.Pos}, p ≤ p₀ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.get_sliceTo, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.get_sliceTo.h3 : ¬∀ {s : String.Slice} {p₀ p : s.Pos}, p ≤ p₀ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.get_sliceTo, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.get_sliceTo.h4 : ¬∀ {s : String.Slice} {p₀ p : s.Pos} {h : p ≤ p₀}, p₀.sliceTo p h ≠ (s.sliceTo p₀).endPos := fun hc_h => absurd (fun hc_k0 => @hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) hc_k0) (by
  decide)

-- String.Pos.get_sliceTo, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.get_sliceTo.h3 : ¬∀ {s : String} {p₀ p : s.Pos}, p ≤ p₀ := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.get_sliceTo, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.get_sliceTo.h4 : ¬∀ {s : String} {p₀ p : s.Pos} {h : p ≤ p₀}, p₀.sliceTo p h ≠ (s.sliceTo p₀).endPos := fun hc_h => absurd (fun hc_k0 => @hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) hc_k0) (by
  decide)

-- String.Pos.ne_startPos_of_sliceFrom_ne_startPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ne_startPos_of_sliceFrom_ne_startPos.h3 : ¬∀ {s : String} {p p₀ : s.Pos}, p₀ ≤ p := fun hc_h => absurd (@hc_h ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.ne_startPos_of_sliceFrom_ne_startPos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ne_startPos_of_sliceFrom_ne_startPos.h4 : ¬∀ {s : String} {p p₀ : s.Pos} {h₀ : p₀ ≤ p}, p ≠ s.startPos := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) (by
  decide)) (by
  decide)

-- String.Slice.apply_eq_true_of_skipSuffixWhile_le_bool, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.apply_eq_true_of_skipSuffixWhile_le_bool.h3 : ¬∀ {p : Char → Bool} {s : String.Slice} {pos : s.Pos} (h' : pos < s.endPos),
        p (pos.get (String.Slice.Pos.ne_endPos_of_lt h')) = Bool.true := fun hc_h => absurd (fun hc_k0 => @hc_h (fun (a : Char) => Bool.false) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) hc_k0) (by
  decide)

-- String.Pos.Splits.pastSet, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.pastSet.h6 : ¬∀ {s : String} {p : s.Pos} {t₁ t₂ : String} {c : Char} {d : Char}, p.Splits t₁ (String.singleton c ++ t₂) := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("") ('a') ('a')) (by
  simp)

-- String.Pos.ofSlice_lt_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSlice_lt_iff.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos} {q : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.ofSlice_le_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSlice_le_iff.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos} {q : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.Splits.prev, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.prev.h5 : ¬∀ {t₁ : String} {c : Char} {t₂ s : String} {p : s.Pos}, p.Splits (t₁ ++ String.singleton c) t₂ := fun hc_h => absurd (@hc_h ("") ('a') ("") ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  simp)

-- String.Slice.Pos.Splits.splits_rotateRight, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.splits_rotateRight.h5 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ t₂ t₃ : String}, p.Splits t₁ (t₂ ++ t₃) := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("") ("a")) (by
  simp)

-- String.Slice.Pos.Splits.nextn, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.nextn.h4 : ¬∀ {s : String.Slice} {t₁ t₂ : String} {p : s.Pos} (n : Nat),
        (p.nextn n).Splits (t₁ ++ String.ofList (List.take n t₂.toList)) (String.ofList (List.drop n t₂.toList)) := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("") ("a") ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) (0)) (by
  simp)

-- String.Slice.Pos.prev_prev_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.prev_prev_lt.h3 : ¬∀ {s : String.Slice} {p : s.Pos} {h : p ≠ s.startPos}, p.prev h ≠ s.startPos := fun hc_h => absurd (fun hc_k0 => @hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) hc_k0) (by
  decide +kernel)

-- String.Slice.Pos.sliceTo_le_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.sliceTo_le_iff.h4 : ¬∀ {s : String.Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos}, q ≤ p₀ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("ab".toSlice.sliceTo
          { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "ab".toSlice.Pos }).Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.sliceFrom_le_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.sliceFrom_le_iff.h4 : ¬∀ {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos}, p₀ ≤ q := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("a".sliceFrom
          { offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "a".Pos }).Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.Splits.eq_endPos_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.eq_endPos_iff.h4 : ¬∀ {t₁ : String} {t₂ s : String} {p : s.Pos}, p = s.endPos ↔ t₂ = "" := fun hc_h => absurd (@hc_h ("") ("") ("a") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.Pos.Splits.offset_eq_decreaseBy, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.offset_eq_decreaseBy.h4 : ¬∀ {t₁ : String} {t₂ : String} {s : String.Slice} {p : s.Pos}, p.offset = s.rawEndPos.decreaseBy t₂.utf8ByteSize := fun hc_h => absurd (@hc_h ("") ("") ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.Splits.toByteArray_right_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.toByteArray_right_eq.h4 : ¬∀ {s : String} {p : s.Pos} {t₁ : String} {t₂ : String},
        t₂.toByteArray = s.toByteArray.extract p.offset.byteIdx s.utf8ByteSize := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("a")) (by
  decide)

-- String.Slice.Pos.Splits.copy_sliceFrom_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.copy_sliceFrom_eq.h4 : ¬∀ {t₁ : String} {t₂ : String} {s : String.Slice} {p : s.Pos}, (s.sliceFrom p).copy = t₂ := fun hc_h => absurd (@hc_h ("") ("") ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.splits_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.splits_slice.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.Splits.remainingBytes_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Splits.remainingBytes_eq.h4 : ¬∀ {s : String} {p : s.Pos} {t₁ : String} {t₂ : String}, p.remainingBytes = t₂.utf8ByteSize := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ("") ("a")) (by
  decide)

-- String.Slice.Pos.Splits.remainingBytes_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.Splits.remainingBytes_eq.h4 : ¬∀ {s : String.Slice} {p : s.Pos} {t₁ : String} {t₂ : String}, p.remainingBytes = t₂.utf8ByteSize := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ("") ("a")) (by
  decide)

-- String.Pos.Raw.isValidForSlice_stringSlice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.isValidForSlice_stringSlice.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos} (pos : String.Pos.Raw), p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ : String.Pos.Raw })) (by
  decide)

-- String.Slice.sliceFrom_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.sliceFrom_slice.h3 : ¬∀ {s : String.Slice} {p₁ p₂ : s.Pos}, p₁ ≤ p₂ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.lt_sliceTo_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.lt_sliceTo_iff.h4 : ¬∀ {s : String.Slice} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos} {q : s.Pos}, q ≤ p₀ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("ab".toSlice.sliceTo
          { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
            "ab".toSlice.Pos }).Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos })) (by
  decide)

-- String.slice_eq_toSlice_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.slice_eq_toSlice_iff.h3 : ¬∀ {s : String} {p₁ p₂ : s.Pos}, p₁ ≤ p₂ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.toByteArray_copy_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.toByteArray_copy_slice.h3 : ¬∀ {s : String} {p₁ p₂ : s.Pos}, p₁ ≤ p₂ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.ofSliceTo_ne_endPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSliceTo_ne_endPos.h3 : ¬∀ {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos}, String.Pos.ofSliceTo p ≠ s.endPos := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("".sliceTo { offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }).Pos })) (by
  decide)

-- String.Slice.Pattern.Internal.offsetBy_increaseBy_le_rawEndPos_str, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pattern.Internal.offsetBy_increaseBy_le_rawEndPos_str.h3 : ¬∀ {s : String.Slice} {p : String.Pos.Raw} {len : Nat},
        (p.offsetBy s.startInclusive.offset).increaseBy len ≤ s.str.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw }) (1)) (by
  decide)

-- String.Pos.prev_ofSliceTo, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.prev_ofSliceTo.h3 : ¬∀ {s : String} {p₀ : s.Pos} {p : (s.sliceTo p₀).Pos}, String.Pos.ofSliceTo p ≠ s.startPos := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      ("".sliceTo { offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos }).Pos })) (by
  decide)

-- String.Slice.posGE_le_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posGE_le_iff.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw} {q : s.Pos}, p ≤ s.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.lt_posGT_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.lt_posGT_iff.h2 : ¬∀ {s : String} {p : String.Pos.Raw} {q : s.Pos}, p < s.rawEndPos := fun hc_h => absurd (@hc_h ("") ({ : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

-- String.Slice.le_posLT_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.le_posLT_iff.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw} {q : s.Pos}, 0 < p := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.posGE_eq_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.posGE_eq_iff.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw} {q : s.Pos}, p ≤ s.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.isEmpty_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.isEmpty_slice.h3 : ¬∀ {s : String.Slice} {p₁ p₂ : s.Pos}, p₁ ≤ p₂ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.copy_sliceTo_cast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.copy_sliceTo_cast.h2 : ¬∀ {s t : String.Slice} {pos : s.Pos}, s.copy = t.copy := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.copy_slice_eq_append_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.copy_slice_eq_append_of_lt.h3 : ¬∀ {s : String.Slice} {p q : s.Pos}, p < q := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.eq_prev_of_prev?_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.eq_prev_of_prev?_eq_some.h3 : ¬∀ {s : String.Slice} {p q : s.Pos}, p.prev? = Option.some q := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "".toSlice.Pos })) (by
  decide)

-- String.Slice.toSlice_subslice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.toSlice_subslice.h3 : ¬∀ {s : String.Slice} {newStart newEnd : s.Pos}, newStart ≤ newEnd := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Subslice.startInclusive_extendLeft, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Subslice.startInclusive_extendLeft.h3 : ¬∀ {s : String.Slice} {sl : s.Subslice} {newStart : s.Pos}, newStart ≤ sl.startInclusive := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({
      startInclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      endExclusive :=
        { offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
          "ab".toSlice.Pos },
      startInclusive_le_endExclusive := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Subslice }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.slice_eq_slice!, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.slice_eq_slice!.h3 : ¬∀ {s : String.Slice} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos }) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.ofSliceTo_sliceTo, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.ofSliceTo_sliceTo.h3 : ¬∀ {s : String.Slice} {p₀ p : s.Pos}, p ≤ p₀ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.Pos.offset_sliceTo, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.offset_sliceTo.h3 : ¬∀ {s : String.Slice} {p₀ pos : s.Pos}, pos ≤ p₀ := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos }) ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) :
      "ab".toSlice.Pos })) (by
  decide)

-- String.Pos.offset_add_slice, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.offset_add_slice.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.ofSlice_endPos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.ofSlice_endPos.h3 : ¬∀ {s : String} {p₀ p₁ : s.Pos}, p₀ ≤ p₁ := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Pos.le_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.le_of_lt.h3 : ¬∀ {s : String} {p q : s.Pos}, p ≤ q := fun hc_h => absurd (@hc_h ("a") ({ offset := { byteIdx := 1 : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos }) ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "a".Pos })) (by
  decide)

-- String.Slice.eq_append_of_dropSuffix?_bool_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.eq_append_of_dropSuffix?_bool_eq_some.h3 : ¬∀ {p : Char → Bool} {s res : String.Slice}, ∃ (c : Char), s.copy = res.copy ++ String.singleton c ∧ p c = Bool.true := fun hc_h => absurd (@hc_h (fun (a : Char) => Bool.false) ("".toSlice : String.Slice) ("".toSlice : String.Slice)) (by
  simp)

-- String.Slice.eq_append_of_dropPrefix?_bool_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.eq_append_of_dropPrefix?_bool_eq_some.h3 : ¬∀ {p : Char → Bool} {s res : String.Slice}, ∃ (c : Char), s.copy = String.singleton c ++ res.copy ∧ p c = Bool.true := fun hc_h => absurd (@hc_h (fun (a : Char) => Bool.false) ("".toSlice : String.Slice) ("".toSlice : String.Slice)) (by
  simp)

-- String.eq_append_of_dropPrefix?_bool_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.eq_append_of_dropPrefix?_bool_eq_some.h3 : ¬∀ {p : Char → Bool} {s : String} {res : String.Slice},
        ∃ (c : Char), s = String.singleton c ++ res.copy ∧ p c = Bool.true := fun hc_h => absurd (@hc_h (fun (a : Char) => Bool.false) ("") ("".toSlice : String.Slice)) (by
  simp)

-- String.startsWith_slice_of_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.startsWith_slice_of_isEmpty.h2 : ¬∀ {pat : String.Slice} {s : String}, s.startsWith pat = Bool.true := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ("")) (by
  decide)

-- String.Slice.endsWith_slice_of_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.endsWith_slice_of_isEmpty.h2 : ¬∀ {pat s : String.Slice}, s.endsWith pat = Bool.true := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ("".toSlice : String.Slice)) (by
  decide)

-- String.Slice.skipPrefix?_slice_of_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.skipPrefix?_slice_of_isEmpty.h2 : ¬∀ {pat s : String.Slice}, s.skipPrefix? pat = Option.some s.startPos := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ("".toSlice : String.Slice)) (by
  decide)

-- String.Slice.Pos.get?_eq_none, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.get?_eq_none.h2 : ¬∀ {s : String.Slice} {p : s.Pos}, p.get? = Option.none := fun hc_h => absurd (@hc_h ("ab".toSlice : String.Slice) ({ offset := { : String.Pos.Raw }, isValidForSlice := of_decide_eq_true (id (Eq.refl Bool.true)) : "ab".toSlice.Pos })) (by
  decide)

-- String.Slice.pos!_eq_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.pos!_eq_pos.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, String.Pos.Raw.IsValidForSlice s p := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ byteIdx := 1 : String.Pos.Raw })) (by
  decide)

-- String.Slice.getUTF8Byte_copy, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.getUTF8Byte_copy.h2 : ¬∀ {s : String.Slice} {p : String.Pos.Raw}, p < s.copy.rawEndPos := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) ({ : String.Pos.Raw })) (by
  decide)

-- String.Slice.Pos.prevAuxGo_le_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Slice.Pos.prevAuxGo_le_self.h2 : ¬∀ {s : String.Slice} {p : Nat}, p < s.utf8ByteSize := fun hc_h => absurd (@hc_h ("".toSlice : String.Slice) (0)) (by
  decide)

-- String.Pos.posLT_offset, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.posLT_offset.h2 : ¬∀ {s : String} {p : s.Pos}, 0 < p.offset := fun hc_h => absurd (@hc_h ("") ({ offset := { : String.Pos.Raw }, isValid := of_decide_eq_true (id (Eq.refl Bool.true)) : "".Pos })) (by
  decide)

