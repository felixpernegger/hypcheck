import Init

noncomputable instance HypCheckDec.ppolyNonNeg (p : Lean.Grind.CommRing.PPoly) : Decidable p.NonNeg :=
  Lean.Grind.CommRing.PPoly.rec (motive := fun p => Decidable p.NonNeg)
    (fun k => (inferInstance : Decidable (0 ≤ k)))
    (fun k _ _ _ ih => @instDecidableAnd (0 ≤ k) _ inferInstance ih) p
noncomputable instance HypCheckDec.ppolyDeg (B D : Nat) (p : Lean.Grind.CommRing.PPoly) : Decidable (p.Deg B D) :=
  Lean.Grind.CommRing.PPoly.rec (motive := fun p => Decidable (p.Deg B D))
    (fun _ => isTrue trivial)
    (fun _ _ v _ ih => @instDecidableAnd (Lean.Grind.CommRing.PPoly.dsum B v ≤ D) _ (Nat.decLe _ _) ih) p
noncomputable instance HypCheckDec.polyNonnegCoeffs (p : Lean.Grind.CommRing.Poly) : Decidable p.NonnegCoeffs :=
  Lean.Grind.CommRing.Poly.rec (motive := fun p => Decidable p.NonnegCoeffs)
    (fun c => if h : c ≥ 0 then isTrue (.num c h) else isFalse (fun hc => by cases hc; contradiction))
    (fun a m p ih => if h : a ≥ 0 then
        (match ih with
         | isTrue hp => isTrue (.add a m p h hp)
         | isFalse hp => isFalse (fun hc => by cases hc; contradiction))
      else isFalse (fun hc => by cases hc; contradiction)) p
noncomputable instance HypCheckDec.polyNonnegList (ps : List Lean.Grind.CommRing.Poly) : Decidable (Lean.Grind.CommRing.Poly.NonnegList ps) :=
  List.rec (motive := fun ps => Decidable (Lean.Grind.CommRing.Poly.NonnegList ps)) (isTrue trivial)
    (fun p _ ih => @instDecidableAnd p.NonnegCoeffs _ inferInstance ih) ps
noncomputable instance HypCheckDec.klistAllZero {α : Type} [Lean.Grind.Ring α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (ls : Lean.Grind.CommRing.KList) : Decidable (ls.AllZero ctx) :=
  Lean.Grind.CommRing.KList.rec (motive := fun ls => Decidable (ls.AllZero ctx)) (isTrue trivial)
    (fun _ _ q _ ih => @instDecidableAnd (q.denote ctx = 0) _ inferInstance ih) ls
noncomputable instance HypCheckDec.mlistAllZero {α : Type} [Lean.Grind.Ring α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (ls : Lean.Grind.CommRing.MList) : Decidable (ls.AllZero ctx) :=
  Lean.Grind.CommRing.MList.rec (motive := fun ls => Decidable (ls.AllZero ctx)) (isTrue trivial)
    (fun _ q _ ih => @instDecidableAnd (q.denote ctx = 0) _ inferInstance ih) ls
noncomputable instance HypCheckDec.invAtomsOk {α : Type} [Lean.Grind.Ring α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (l : Lean.Grind.CommRing.InvAtoms) : Decidable (Lean.Grind.CommRing.InvAtoms.ok ctx l) :=
  List.rec (motive := fun l => Decidable (Lean.Grind.CommRing.InvAtoms.ok ctx l)) (isTrue trivial)
    (fun yx _ ih => @instDecidableAnd (yx.2.denote ctx * yx.1.denote ctx = 1) _ inferInstance ih) l
noncomputable instance HypCheckDec.invVarsOk {α : Type} [Lean.Grind.Field α] [DecidableEq α]
    (ctx : Lean.Grind.CommRing.Context α) (invs : Lean.Grind.CommRing.InvVars) : Decidable (invs.ok ctx) :=
  (inferInstance : Decidable (invs.denoteVars ctx = invs.denoteInvs))
noncomputable instance HypCheckDec.ppolyDegList (B D : Nat) (ps : List Lean.Grind.CommRing.PPoly) : Decidable (Lean.Grind.CommRing.PPoly.DegList B D ps) :=
  (inferInstance : Decidable (∀ p ∈ ps, p.Deg B D))


/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/
-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.partialMatch_of_le, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.partialMatch_of_le.h4 : ¬∀ {pat s : ByteArray} {stackPos needlePos : Nat} (newStackPos : Nat),
        newStackPos ≤ stackPos →
          stackPos - newStackPos ≤ needlePos →
            String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch pat s (needlePos - (stackPos - newStackPos))
              newStackPos := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) ({ data := #[] : ByteArray }) (0) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.partialMatch_of_le, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.partialMatch_of_le.h6 : ¬∀ {pat s : ByteArray} {stackPos needlePos : Nat},
        String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch pat s needlePos stackPos →
          ∀ (newStackPos : Nat),
            stackPos - newStackPos ≤ needlePos →
              String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch pat s (needlePos - (stackPos - newStackPos))
                newStackPos := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) ({ data := #[] : ByteArray }) (0) (0) (by
  decide) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence_eq_prefixFunction, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence_eq_prefixFunction.h2 : ¬∀ {pat : ByteArray} {stackPos guess : Nat} {hg : guess < stackPos},
        String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch pat pat guess stackPos → stackPos < pat.size := fun hc_h => absurd (@hc_h ({ data := #[UInt8.ofNat 0] : ByteArray }) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence_eq_prefixFunction, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunctionRecurrence_eq_prefixFunction.h4 : ¬∀ {pat : ByteArray} {stackPos : Nat} {hst : stackPos < pat.size} {guess : Nat},
        String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction pat stackPos hst ≤ guess + 1 →
          String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch pat pat guess stackPos → guess < stackPos := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h ({ data := #[UInt8.ofNat 0] : ByteArray }) (0) hc_k0 (0) hc_k1 hc_k2) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.getElem_eq, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.getElem_eq.h4 : ¬∀ {pat s : ByteArray} {needlePos stackPos : Nat} (j : Nat),
        j < needlePos → String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch pat s needlePos stackPos := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) ({ data := #[] : ByteArray }) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.getElem_eq, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.getElem_eq.h6 : ¬∀ {pat s : ByteArray} {needlePos stackPos : Nat},
        String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch pat s needlePos stackPos → ∀ (j : Nat), j < needlePos := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) ({ data := #[] : ByteArray }) (0) (0) (by
  decide) (0)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.le_prefixFunction, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.le_prefixFunction.h3 : ¬∀ {pat : ByteArray} {stackPos needlePos : Nat},
        0 < stackPos →
          needlePos ≤ stackPos - 1 → String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch pat pat needlePos stackPos := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.le_prefixFunction, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.le_prefixFunction.h4 : ¬∀ {pat : ByteArray} {stackPos needlePos : Nat},
        String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch pat pat needlePos stackPos →
          needlePos ≤ stackPos - 1 → 0 < stackPos := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.le_prefixFunction, hypothesis 5: necessary
/- FAILED: 12:92: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (Lean.Omega.Constraint.isImpossible ?m.60 = true) = true
in the application
  id (Eq.refl true) | 102:25: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (40000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 5:208: `grind` has failed, use `+verbose` to obtain diagnostic information | 10:118: `grind` has failed, use `+verbose` to obtain diagnostic information | 15:92: Application type mismatch: The argument
  Eq.refl true
has type
  true = true
but is expected to have type
  decide (Lean.Omega.Constraint.isImpossible ?m.86 = true) = true
in the application
  id (Eq.refl true) | 132:25: (deterministic) timeout at `whnf`, maximum number of heartbeats (2000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 12:208: `grind` has failed, use `+verbose` to obtain diagnostic information | 40:118: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.le_prefixFunction.h5 : ¬∀ {pat : ByteArray} {stackPos needlePos : Nat}
        (h : String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch pat pat needlePos stackPos) (h₀ : 0 < stackPos),
        needlePos ≤
          String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction pat (stackPos - 1)
            (have this := String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.stackPos_le_size h;
            Decidable.byContradiction fun (a : ¬stackPos - 1 < pat.size) =>
              (fun {pat : ByteArray} {stackPos needlePos : Nat} (h₀ : 0 < stackPos) (this : stackPos ≤ pat.size)
                    (a : ¬stackPos - 1 < pat.size) =>
                  Or.elim Lean.Omega.Int.ofNat_sub_dichotomy
                    (fun (h₁ : 1 ≤ stackPos ∧ ↑(stackPos - 1) = ↑stackPos - ↑1) =>
                      Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                        (Lean.Omega.Constraint.combine_sat'
                          (Lean.Omega.Constraint.addInequality_sat
                            (le_of_le_of_eq (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le (Nat.le_of_not_lt a)))
                              (Eq.trans
                                (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_1)
                                  (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3))
                                (Eq.symm
                                  (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                    { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList [↑stackPos, ↑(stackPos - 1), ↑needlePos, ↑pat.size]))))))
                          (Lean.Omega.combo_sat'
                            { lowerBound := Option.some 1, upperBound := Option.some 1 : Lean.Omega.Constraint }
                            { lowerBound := Option.none, upperBound := Option.some 0 : Lean.Omega.Constraint } (-1) [1, -1]
                            1 [1, 0, 0, -1] (Lean.Omega.Coeffs.ofList [↑stackPos, ↑(stackPos - 1), ↑needlePos, ↑pat.size])
                            (Lean.Omega.tidy_sat
                              (Lean.Omega.Constraint.addEquality_sat
                                (Eq.trans
                                  (Eq.symm
                                    (Eq.trans
                                      (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_1)
                                        (Eq.trans
                                          (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                            (id (Eq.refl ↑1)))
                                          (Eq.symm
                                            (Lean.Omega.LinearCombo.sub_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                              { const := 1 : Lean.Omega.LinearCombo }
                                              (Lean.Omega.Coeffs.ofList
                                                [↑stackPos, ↑(stackPos - 1), ↑needlePos, ↑pat.size])))))
                                      (Eq.symm
                                        (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 1] : Lean.Omega.LinearCombo }
                                          { const := -1, coeffs := [1] : Lean.Omega.LinearCombo }
                                          (Lean.Omega.Coeffs.ofList [↑stackPos, ↑(stackPos - 1), ↑needlePos, ↑pat.size])))))
                                  (Int.sub_eq_zero_of_eq h₁.right))))
                            (Lean.Omega.tidy_sat
                              (Lean.Omega.Constraint.addInequality_sat
                                (le_of_le_of_eq (Int.sub_nonneg_of_le (Lean.Omega.Int.ofNat_le_of_le this))
                                  (Eq.trans
                                    (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_3)
                                      (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0))
                                    (Eq.symm
                                      (Lean.Omega.LinearCombo.sub_eval { coeffs := [0, 0, 0, 1] : Lean.Omega.LinearCombo }
                                        { coeffs := [1] : Lean.Omega.LinearCombo }
                                        (Lean.Omega.Coeffs.ofList
                                          [↑stackPos, ↑(stackPos - 1), ↑needlePos, ↑pat.size]))))))))))
                    fun (h₂ : stackPos < 1 ∧ ↑(stackPos - 1) = 0) =>
                    Lean.Omega.Constraint.not_sat'_of_isImpossible (of_decide_eq_true (id (Eq.refl Bool.true)))
                      (Lean.Omega.Constraint.combine_sat'
                        (Lean.Omega.tidy_sat
                          (Lean.Omega.Constraint.addInequality_sat
                            (le_of_le_of_eq
                              (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt h₂.left)))
                              (Eq.trans
                                (Lean.Omega.Int.sub_congr (id (Eq.refl ↑1))
                                  (Eq.trans
                                    (Lean.Omega.Int.add_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                      (id (Eq.refl 1)))
                                    (Eq.symm
                                      (Lean.Omega.LinearCombo.add_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                        { const := 1 : Lean.Omega.LinearCombo }
                                        (Lean.Omega.Coeffs.ofList [↑stackPos, ↑(stackPos - 1), ↑needlePos, ↑pat.size])))))
                                (Eq.symm
                                  (Lean.Omega.LinearCombo.sub_eval { const := 1 : Lean.Omega.LinearCombo }
                                    { const := 1, coeffs := [1] : Lean.Omega.LinearCombo }
                                    (Lean.Omega.Coeffs.ofList [↑stackPos, ↑(stackPos - 1), ↑needlePos, ↑pat.size])))))))
                        (Lean.Omega.Constraint.addInequality_sat
                          (le_of_le_of_eq (Int.sub_nonneg_of_le (Int.add_one_le_of_lt (Lean.Omega.Int.ofNat_lt_of_lt h₀)))
                            (Eq.trans
                              (Lean.Omega.Int.sub_congr (Eq.symm Lean.Omega.LinearCombo.coordinate_eval_0)
                                (id (Eq.refl (↑0 + 1))))
                              (Eq.symm
                                (Lean.Omega.LinearCombo.sub_eval { coeffs := [1] : Lean.Omega.LinearCombo }
                                  { const := 1 : Lean.Omega.LinearCombo }
                                  (Lean.Omega.Coeffs.ofList [↑stackPos, ↑(stackPos - 1), ↑needlePos, ↑pat.size]))))))))
                h₀ this a) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h ({ data := #[UInt8.ofNat 0] : ByteArray }) (1) (1) hc_k0 hc_k1) (by
  decide +kernel)
-/

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.eq_prefixFunction, hypothesis 4: necessary
/- FAILED: 3:226: unexpected identifier after decimal point; consider parenthesizing the number | 5:263: unexpected identifier after decimal point; consider parenthesizing the number | 3:226: unexpected identifier after decimal point; consider parenthesizing the number | 5:263: unexpected identifier after decimal point; consider parenthesizing the number | 2:111: don't know how to synthesize implicit argument `α`
  @Array.size ?m.5 #[]
context:
⊢ Type ?u.7

Note: All parameter types and holes (e.g., `_`) in the header of a theorem are resolved before the proof is processed; information from the proof cannot be used to infer what these values should be | 8:111: unexpected identifier after decimal point; consider parenthesizing the number | 2:111: don't know how to synthesize implicit argument `α`
  @Array.size ?m.5 #[]
context:
⊢ Type ?u.7

Note: All parameter types and holes (e.g., `_`) in the header of a theorem are resolved before the proof is processed; information from the proof cannot be used to infer what these values should be | 8:111: unexpected identifier after decimal point; consider parenthesizing the number
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.eq_prefixFunction.h4 : ¬∀ {b : ByteArray} {v : Array Nat},
        String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable b v → ∀ (i : Nat), i < v.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (#[]) ((@_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.mk ({ data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }) (@List.toArray Nat (@List.nil Nat)) (by (try dsimp only);   decide) (by (try dsimp only);   decide))) (0)) (by
  decide +kernel)
-/

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le_prefixFunction_sub_one_add_one, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le_prefixFunction_sub_one_add_one.h2 : ¬∀ {pat : ByteArray} {stackPos : Nat}, 0 < stackPos → stackPos < pat.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le_prefixFunction_sub_one_add_one, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le_prefixFunction_sub_one_add_one.h3 : ¬∀ {pat : ByteArray} {stackPos : Nat} {hst : stackPos < pat.size}, 0 < stackPos := fun hc_h => absurd (@hc_h ({ data := #[UInt8.ofNat 0] : ByteArray }) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.partialMatch_prefixFunction_sub_one, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.partialMatch_prefixFunction_sub_one.h2 : ¬∀ {pat : ByteArray} {stackPos : Nat}, 0 < stackPos → stackPos - 1 < pat.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.partialMatch_prefixFunction_sub_one, hypothesis 3: removable
/- FAILED: 11:104: unexpected identifier after decimal point; consider parenthesizing the number | 29:104: unexpected identifier after decimal point; consider parenthesizing the number | 11:104: unexpected identifier after decimal point; consider parenthesizing the number | 29:104: unexpected identifier after decimal point; consider parenthesizing the number
set_option maxHeartbeats 1000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.partialMatch_prefixFunction_sub_one.h3.gneg : ∀ {pat : ByteArray} {stackPos : Nat} {hst : stackPos - 1 < pat.size},
      ¬0 < stackPos →
        String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch pat pat
          (String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction pat (stackPos - 1) hst) stackPos := by
  (intros; simp_all; done)
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.partialMatch_prefixFunction_sub_one.h3 : ∀ {pat : ByteArray} {stackPos : Nat} {hst : stackPos - 1 < pat.size},
      String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch pat pat
        (String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction pat (stackPos - 1) hst) stackPos := by
  intro hc_x0 hc_x1 hc_x2
  exact Classical.byCases (fun hc_h => @_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.partialMatch_prefixFunction_sub_one hc_x0 hc_x1 hc_x2 hc_h) (fun hc_hn => @HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.partialMatch_prefixFunction_sub_one.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn)
-/

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_sub_one_lt, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_sub_one_lt.h2 : ¬∀ {pat : ByteArray} {stackPos : Nat}, 0 < stackPos → stackPos - 1 < pat.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (1) (by
  decide)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_sub_one_lt, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_sub_one_lt.h3 : ¬∀ {pat : ByteArray} {stackPos : Nat} {hst : stackPos - 1 < pat.size},
        String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction pat (stackPos - 1) hst < stackPos := fun hc_h => absurd (fun hc_k0 => @hc_h ({ data := #[UInt8.ofNat 0] : ByteArray }) (0) hc_k0) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.partialMatch_iff, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.partialMatch_iff.h4 : ¬∀ {pat s : ByteArray} {stackPos needlePos needlePos' : Nat},
        String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch pat pat needlePos' needlePos ↔
          needlePos' ≤ needlePos ∧ String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch pat s needlePos' stackPos := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) ({ data := #[] : ByteArray }) (0) (1) (0)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.needlePos_le_size, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.needlePos_le_size.h4 : ¬∀ {pat : ByteArray} {s : ByteArray} {needlePos : Nat} {stackPos : Nat}, needlePos ≤ pat.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) ({ data := #[] : ByteArray }) (1) (0)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction.le_go_iff, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction.le_go_iff.h2 : ¬∀ {pat : ByteArray} {stackPos : Nat} {k k' : Nat}, stackPos < pat.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (0) (0) (0)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.needlePos_le_stackPos, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.needlePos_le_stackPos.h4 : ¬∀ {pat s : ByteArray} {needlePos stackPos : Nat}, needlePos ≤ stackPos := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) ({ data := #[] : ByteArray }) (1) (0)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.le_prefixFunction_iff.h3 : ¬∀ {k : Nat} {pat : ByteArray} {stackPos : Nat}, stackPos < pat.size := fun hc_h => absurd (@hc_h (0) ({ data := #[] : ByteArray }) (0)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le_iff, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le_iff.h3 : ¬∀ {k : Nat} {pat : ByteArray} {stackPos : Nat}, stackPos < pat.size := fun hc_h => absurd (@hc_h (0) ({ data := #[] : ByteArray }) (0)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.partialMatch_zero, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.partialMatch_zero.h3 : ¬∀ {pat s : ByteArray} {stackPos : Nat}, String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch pat s 0 stackPos := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) ({ data := #[] : ByteArray }) (1)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.size_le, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.size_le.h2 : ¬∀ {b : ByteArray} {v : Array Nat}, v.size ≤ b.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (#[0])) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.partialMatch_prefixFunction, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.partialMatch_prefixFunction.h2 : ¬∀ (pat : ByteArray) (stackPos : Nat), stackPos < pat.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (0)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_le.h2 : ¬∀ {pat : ByteArray} {stackPos : Nat}, stackPos < pat.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (0)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.of_prefixFunction_eq, hypothesis 5: removable
/- FAILED: 20:104: unexpected identifier after decimal point; consider parenthesizing the number | 37:104: unexpected identifier after decimal point; consider parenthesizing the number | 20:104: unexpected identifier after decimal point; consider parenthesizing the number | 37:104: unexpected identifier after decimal point; consider parenthesizing the number
set_option maxHeartbeats 1000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.of_prefixFunction_eq.h5.gneg : ∀ {pat s : String.Slice} {stackPos needlePos : String.Pos.Raw},
      String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants pat s needlePos stackPos →
        ¬needlePos ≠ 0 →
          ∀ {k : Nat} {hki : needlePos.byteIdx - 1 < pat.copy.toByteArray.size},
            String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction pat.copy.toByteArray (needlePos.byteIdx - 1)
                  hki =
                k →
              0 < k →
                String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants pat s { byteIdx := k : String.Pos.Raw } stackPos := by
  (intros; simp_all; done)
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.of_prefixFunction_eq.h5 : ∀ {pat s : String.Slice} {stackPos needlePos : String.Pos.Raw},
      String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants pat s needlePos stackPos →
        ∀ {k : Nat} {hki : needlePos.byteIdx - 1 < pat.copy.toByteArray.size},
          String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction pat.copy.toByteArray (needlePos.byteIdx - 1) hki =
              k →
            0 < k →
              String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants pat s { byteIdx := k : String.Pos.Raw } stackPos := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x6 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.of_prefixFunction_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_h hc_x6 hc_x7 hc_x8 hc_x9) (fun hc_hn => @HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.Invariants.of_prefixFunction_eq.h5.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_hn hc_x6 hc_x7 hc_x8 hc_x9)
-/

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.push, hypothesis 4: necessary
/- FAILED: 3:235: unexpected identifier after decimal point; consider parenthesizing the number | 9:218: unexpected identifier after decimal point; consider parenthesizing the number | 3:235: unexpected identifier after decimal point; consider parenthesizing the number | 9:218: unexpected identifier after decimal point; consider parenthesizing the number | 2:94: don't know how to synthesize implicit argument `α`
  @Array.size ?m.3 #[]
context:
⊢ Type ?u.8

Note: All parameter types and holes (e.g., `_`) in the header of a theorem are resolved before the proof is processed; information from the proof cannot be used to infer what these values should be | 10:111: unexpected identifier after decimal point; consider parenthesizing the number | 2:94: don't know how to synthesize implicit argument `α`
  @Array.size ?m.3 #[]
context:
⊢ Type ?u.8

Note: All parameter types and holes (e.g., `_`) in the header of a theorem are resolved before the proof is processed; information from the proof cannot be used to infer what these values should be | 10:111: unexpected identifier after decimal point; consider parenthesizing the number
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.push.h4 : ¬∀ {b : ByteArray} {v : Array Nat},
        String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable b v → ∀ {d : Nat}, v.size + 1 ≤ b.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (#[]) ((@_private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.IsTable.mk ({ data := @List.toArray UInt8 (@List.nil UInt8) : ByteArray }) (@List.toArray Nat (@List.nil Nat)) (by (try dsimp only);   decide) (by (try dsimp only);   decide))) (0)) (by
  decide +kernel)
-/

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.stackPos_le_size, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.PartialMatch.stackPos_le_size.h4 : ¬∀ {pat : ByteArray} {s : ByteArray} {needlePos : Nat} {stackPos : Nat}, stackPos ≤ s.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) ({ data := #[] : ByteArray }) (0) (1)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_eq_iff, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_eq_iff.h3 : ¬∀ {k : Nat} {pat : ByteArray} {stackPos : Nat}, stackPos < pat.size := fun hc_h => absurd (@hc_h (0) ({ data := #[] : ByteArray }) (0)) (by
  decide +kernel)

-- _private.Init.Data.String.Lemmas.Pattern.String.ForwardSearcher.0.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_zero, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.String.Slice.Pattern.Model.ForwardSliceSearcher.prefixFunction_zero.h1 : ¬∀ {b : ByteArray}, 0 < b.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray })) (by
  decide +kernel)

