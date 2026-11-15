import HCImportsM

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- PartialEquiv.coe_symm_mk, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.coe_symm_mk.h6 : ¬∀ {α β : Type} (f : α → β) (g : β → α) (s : Set α) (t : Set β),
        (∀ ⦃x : β⦄, x ∈ t → g x ∈ s) →
          (∀ ⦃x : α⦄, x ∈ s → g (f x) = x) → (∀ ⦃x : β⦄, x ∈ t → f (g x) = x) → ∀ ⦃x : α⦄, x ∈ s → f x ∈ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- sign_sum, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.sign_sum.h7.inst : ¬SignType.sign
          (∑ i ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }, (fun (a : ℕ) => 0) i) =
        SignType.neg := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.sign_sum.h7.prem0 : ∀ i ∈ { val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ },
      SignType.sign ((fun (a : ℕ) => 0) i) = SignType.neg := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.sign_sum.h7 : ¬∀ {α : Type} [inst : AddCommGroup α] [inst_1 : LinearOrder α] [inst_2 : IsOrderedAddMonoid α] {ι : Type} {s : Finset ι}
        {f : ι → α} (t : SignType), (∀ i ∈ s, SignType.sign (f i) = t) → SignType.sign (∑ i ∈ s, f i) = t := fun hc_h => HypCheckProof.sign_sum.h7.inst (@hc_h (ℤ) (Int.instAddCommGroup) (Int.instLinearOrder) _ (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (a : ℕ) => 0) (SignType.neg) HypCheckProof.sign_sum.h7.prem0)

-- ENNReal.le_ofReal_iff_toReal_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_ofReal_iff_toReal_le.h3 : ¬∀ {a : ENNReal} {b : ℝ}, a ≠ ⊤ → (a ≤ ENNReal.ofReal b ↔ a.toReal ≤ b) := fun hc_h => absurd (@hc_h ((0 : ENNReal) : ENNReal) ((-1 : Real) : ℝ) (by
  decide)) (by
  simp)

-- ENNReal.ofReal_lt_iff_lt_toReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_lt_iff_lt_toReal.h2 : ¬∀ {a : ℝ} {b : ENNReal}, b ≠ ⊤ → (ENNReal.ofReal a < b ↔ a < b.toReal) := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ) ((0 : ENNReal) : ENNReal) (by
  decide)) (by
  simp)

-- ENNReal.ofReal_lt_iff_lt_toReal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_lt_iff_lt_toReal.h3 : ¬∀ {a : ℝ} {b : ENNReal}, 0 ≤ a → (ENNReal.ofReal a < b ↔ a < b.toReal) := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ) ((⊤ : ENNReal) : ENNReal) (by
  rfl)) (by
  simp)

-- Real.HolderTriple.one_div_pos', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.one_div_pos'.h3 : ¬∀ {p q : ℝ} {r : ℝ}, 0 < 1 / r := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ }) ((0 : Real) : ℝ)) (by
  simp)

-- Real.HolderTriple.one_div_ne_zero', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.one_div_ne_zero'.h3 : ¬∀ {p q : ℝ} {r : ℝ}, 1 / r ≠ 0 := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ }) ((0 : Real) : ℝ)) (by
  simp)

-- Real.HolderTriple.inv_ne_zero', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.inv_ne_zero'.h3 : ¬∀ {p q : ℝ} {r : ℝ}, r⁻¹ ≠ 0 := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ }) ((0 : Real) : ℝ)) (by
  simp)

-- Real.HolderTriple.inv_nonneg', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.inv_nonneg'.h3 : ¬∀ {p q : ℝ} {r : ℝ}, 0 ≤ r⁻¹ := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ }) ((-1 : Real) : ℝ)) (by
  simp)

-- Real.HolderTriple.one_div_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.one_div_pos.h3 : ¬∀ {p : ℝ} {q r : ℝ}, 0 < 1 / p := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ) ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ })) (by
  simp)

-- Real.HolderTriple.inv_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.inv_eq.h3 : ¬∀ {p q r : ℝ}, r⁻¹ = p⁻¹ + q⁻¹ := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ((0 : Real) : ℝ) ({ cauchy := 1 : ℝ })) (by
  simp)

-- Real.HolderTriple.nonneg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.nonneg.h3 : ¬∀ {p : ℝ} {q r : ℝ}, 0 ≤ p := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ) ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ })) (by
  simp)

-- Real.HolderTriple.inv_sub_inv_eq_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.inv_sub_inv_eq_inv.h3 : ¬∀ {p q r : ℝ}, r⁻¹ - q⁻¹ = p⁻¹ := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ((0 : Real) : ℝ) ({ cauchy := 1 : ℝ })) (by
  simp)

-- Real.HolderTriple.inv_add_inv_eq_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.inv_add_inv_eq_inv.h3 : ¬∀ {p q r : ℝ}, p⁻¹ + q⁻¹ = r⁻¹ := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ((0 : Real) : ℝ) ({ cauchy := 1 : ℝ })) (by
  simp)

-- Real.HolderTriple.one_div_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.one_div_eq.h3 : ¬∀ {p q r : ℝ}, 1 / r = 1 / p + 1 / q := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ((0 : Real) : ℝ) ({ cauchy := 1 : ℝ })) (by
  simp)

-- Real.HolderTriple.nonneg', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.nonneg'.h3 : ¬∀ {p q : ℝ} {r : ℝ}, 0 ≤ r := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ }) ((-1 : Real) : ℝ)) (by
  simp)

-- Real.HolderTriple.inv_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.inv_pos.h3 : ¬∀ {p : ℝ} {q r : ℝ}, 0 < p⁻¹ := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ) ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ })) (by
  simp)

-- Real.toNNReal_le_toNNReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toNNReal_le_toNNReal.h2 : ¬∀ {r p : ℝ}, r.toNNReal ≤ p.toNNReal := fun hc_h => absurd (@hc_h ((1 : Real) : ℝ) ((0 : Real) : ℝ)) (by
  simp)

-- Real.le_toNNReal_iff_coe_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.le_toNNReal_iff_coe_le.h2 : ¬∀ {r : NNReal} {p : ℝ}, r ≤ p.toNNReal ↔ ↑r ≤ p := fun hc_h => absurd (@hc_h ((0 : NNReal) : NNReal) ((-1 : Real) : ℝ)) (by
  simp)

-- Real.le_toNNReal_iff_coe_le', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.le_toNNReal_iff_coe_le'.h2 : ¬∀ {r : NNReal} {p : ℝ}, r ≤ p.toNNReal ↔ ↑r ≤ p := fun hc_h => absurd (@hc_h ((0 : NNReal) : NNReal) ((-1 : Real) : ℝ)) (by
  simp)

-- NNReal.le_toNNReal_of_coe_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.le_toNNReal_of_coe_le.h2 : ¬∀ {x : NNReal} {y : ℝ}, x ≤ y.toNNReal := fun hc_h => absurd (@hc_h ((1 : NNReal) : NNReal) ((0 : Real) : ℝ)) (by
  simp)

-- Real.HolderConjugate.div_conj_eq_sub_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderConjugate.div_conj_eq_sub_one.h2 : ¬∀ {p q : ℝ}, p / q = p - 1 := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ) ({ cauchy := 0 : ℝ })) (by
  simp)

-- Real.HolderConjugate.inv_add_inv_eq_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderConjugate.inv_add_inv_eq_one.h2 : ¬∀ {p q : ℝ}, p⁻¹ + q⁻¹ = 1 := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ) ((0 : Real) : ℝ)) (by
  simp)

-- Real.HolderConjugate.mul_eq_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderConjugate.mul_eq_add.h2 : ¬∀ {p q : ℝ}, p * q = p + q := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ((1 : Real) : ℝ)) (by
  simp)

-- Real.toNNReal_eq_natCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toNNReal_eq_natCast.h2 : ¬∀ {r : ℝ} {n : ℕ}, r.toNNReal = ↑n ↔ r = ↑n := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ) (0)) (by
  simp)

-- ENNReal.ofReal_lt_coe_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_lt_coe_iff.h2 : ¬∀ {a : ℝ} {b : NNReal}, ENNReal.ofReal a < ↑b ↔ a < ↑b := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ) ((0 : NNReal) : NNReal)) (by
  simp)

-- ENNReal.ofReal_inv_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_inv_of_pos.h1 : ¬∀ {x : ℝ}, ENNReal.ofReal x⁻¹ = (ENNReal.ofReal x)⁻¹ := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ)) (by
  simp)

-- NNReal.inv_mk, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.inv_mk.h1 : ¬∀ {r : ℝ}, 0 ≤ r := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ)) (by
  simp)

-- Real.toNNReal_of_nonneg, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toNNReal_of_nonneg.h1 : ¬∀ {r : ℝ}, 0 ≤ r := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ)) (by
  simp)

-- Real.sign_apply_eq_of_ne_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.sign_apply_eq_of_ne_zero.h1 : ¬∀ (r : ℝ), r.sign = -1 ∨ r.sign = 1 := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ)) (by
  simp)

-- ENNReal.toReal_ofReal, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_ofReal.h1 : ¬∀ {r : ℝ}, (ENNReal.ofReal r).toReal = r := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ)) (by
  (simp <;> omega))

-- NNReal.coe_mk, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.coe_mk.h1 : ¬∀ (a : ℝ), 0 ≤ a := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ)) (by
  simp)

-- Real.toNNReal_of_nonpos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toNNReal_of_nonpos.h1 : ¬∀ {r : ℝ}, r.toNNReal = 0 := fun hc_h => absurd (@hc_h ((1 : Real) : ℝ)) (by
  simp)

