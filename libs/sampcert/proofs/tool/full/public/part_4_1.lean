import SampCert

/-! Proofs emitted by HypCheck.lean (Lean 4.34.1). -/

-- SLang.sv5_sv6_loop_base_case, hypothesis 10: removable
set_option maxHeartbeats 200000 in
theorem HypCheckProof.SLang.sv5_sv6_loop_base_case.h10.gneg : ∀ {sv_T : Type} (qs : SLang.sv_query sv_T) (T τ : ℤ) (l : List sv_T) (point eval : ℕ) (past future : List ℤ) (pres : ℤ),
      ¬future = [] →
        future.length = eval →
          (past ++ [pres] ++ future).length = point + 1 →
            SLang.sv6_loop qs T τ l point ((past, pres), future) point =
              SLang.sv5_loop qs T τ l eval ((past, pres), future) point := by
  (intros; exact?)
theorem HypCheckProof.SLang.sv5_sv6_loop_base_case.h10 : ∀ {sv_T : Type} (qs : SLang.sv_query sv_T) (T τ : ℤ) (l : List sv_T) (point eval : ℕ) (past future : List ℤ) (pres : ℤ),
      future.length = eval →
        (past ++ [pres] ++ future).length = point + 1 →
          SLang.sv6_loop qs T τ l point ((past, pres), future) point =
            SLang.sv5_loop qs T τ l eval ((past, pres), future) point := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x11 hc_x12
  exact Classical.byCases (fun hc_h => @SLang.sv5_sv6_loop_base_case hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_h hc_x11 hc_x12) (fun hc_hn => @HypCheckProof.SLang.sv5_sv6_loop_base_case.h10.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_hn hc_x11 hc_x12)

-- SLang.BernoulliExpNegSampleUnitAux_preservation', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_preservation'.h4 : ¬∀ (num : ℕ) (den : ℕ+) (n m : ℕ), m > 1 → n ≥ m → num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) (2) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- SLang.BernoulliExpNegSampleUnitAux_preservation', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_preservation'.h5 : ¬∀ (num : ℕ) (den : ℕ+) (n m : ℕ), num ≤ ↑den → n ≥ m → m > 1 := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- ENNReal.ereal_smul_le_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ereal_smul_le_left.h3 : ¬∀ {w z : EReal}, ∀ s < ⊤, s * w ≤ s * z → w ≤ z := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide) (by
  simp)) (by
  simp)

-- ENNReal.ereal_smul_le_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ereal_smul_le_left.h4 : ¬∀ {w z : EReal} (s : EReal), 0 < s → s * w ≤ s * z → w ≤ z := fun hc_h => absurd (@hc_h (2) (1) (⊤) (by
  decide) (by
  simp)) (by
  simp)

-- ENNReal.ereal_smul_le_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ereal_smul_le_left.h5 : ¬∀ {w z : EReal} (s : EReal), 0 < s → s < ⊤ → w ≤ z := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  simp) (by
  decide)) (by
  simp)

-- RenyiDivergenceExpectation'_pointwise, hypothesis 4: removable
set_option maxHeartbeats 200000 in
theorem HypCheckProof.RenyiDivergenceExpectation'_pointwise.h4.gneg : ∀ (a b : ENNReal) {α : ℝ}, 1 < α → ¬a ≠ 0 → a ≠ ⊤ → a ^ α * b ^ (1 - α) = (a / b) ^ (α - 1) * a := by
  (intros; simp_all <;> grind)
theorem HypCheckProof.RenyiDivergenceExpectation'_pointwise.h4 : ∀ (a b : ENNReal) {α : ℝ}, 1 < α → a ≠ ⊤ → a ^ α * b ^ (1 - α) = (a / b) ^ (α - 1) * a := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x5
  exact Classical.byCases (fun hc_h => @RenyiDivergenceExpectation'_pointwise hc_x0 hc_x1 hc_x2 hc_x3 hc_h hc_x5) (fun hc_hn => @HypCheckProof.RenyiDivergenceExpectation'_pointwise.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn hc_x5)

-- SLang.probBind_norm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.probBind_norm.h5 : ¬∀ {α β : Type} (p : SLang α) (q : α → SLang β), ∑' (s : α), p s = 1 → ∑' (s : β), p.probBind q s = 1 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => if a = 0 then 1 else 0) (fun (a a_1 : ℕ) => 0) (by
  simp)) (by
  simp)

-- SLang.BernoulliExpNegSampleUnitAux_progress', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_progress'.h3 : ¬∀ (num : ℕ) (den : ℕ+), ∀ n > 1, num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) (2) (by
  decide)) (by
  decide +kernel)

-- SLang.BernoulliExpNegSampleUnitAux_progress', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_progress'.h4 : ¬∀ (num : ℕ) (den : ℕ+) (n : ℕ), num ≤ ↑den → n > 1 := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- SLang.ofDP_bound_SC2, hypothesis 1: removable
set_option maxHeartbeats 200000 in
theorem HypCheckProof.SLang.ofDP_bound_SC2.h1.gneg : ∀ (ε : NNReal),
      ¬0 < ε →
        ∀ (α : ℝ),
          0 ≤ α →
            ENNReal.ofReal (Real.exp ↑ε) ^ α *
                ((1 - ENNReal.ofReal (Real.exp (-↑ε))) / (ENNReal.ofReal (Real.exp ↑ε) - ENNReal.ofReal (Real.exp (-↑ε)))) ≠
              ⊤ := by
  (intros; simp_all; done)
theorem HypCheckProof.SLang.ofDP_bound_SC2.h1 : ∀ (ε : NNReal) (α : ℝ),
      0 ≤ α →
        ENNReal.ofReal (Real.exp ↑ε) ^ α *
            ((1 - ENNReal.ofReal (Real.exp (-↑ε))) / (ENNReal.ofReal (Real.exp ↑ε) - ENNReal.ofReal (Real.exp (-↑ε)))) ≠
          ⊤ := by
  intro hc_x0 hc_x2 hc_x3
  exact Classical.byCases (fun hc_h => @SLang.ofDP_bound_SC2 hc_x0 hc_h hc_x2 hc_x3) (fun hc_hn => @HypCheckProof.SLang.ofDP_bound_SC2.h1.gneg hc_x0 hc_hn hc_x2 hc_x3)

-- ENNReal.ofEReal_plus_nonneg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofEReal_plus_nonneg.h2 : ¬∀ {w z : EReal}, 0 ≤ z → ENNReal.ofEReal (w + z) = ENNReal.ofEReal w + ENNReal.ofEReal z := fun hc_h => absurd (@hc_h (⊥) (⊤) (by
  decide)) (by
  decide +kernel)

-- ENNReal.ofEReal_plus_nonneg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofEReal_plus_nonneg.h3 : ¬∀ {w z : EReal}, 0 ≤ w → ENNReal.ofEReal (w + z) = ENNReal.ofEReal w + ENNReal.ofEReal z := fun hc_h => absurd (@hc_h (⊤) (⊥) (by
  decide)) (by
  decide +kernel)

-- SLang.ofDP_bound_SC1, hypothesis 1: removable
set_option maxHeartbeats 200000 in
theorem HypCheckProof.SLang.ofDP_bound_SC1.h1.gneg : ∀ (ε : NNReal),
      ¬0 < ε →
        ∀ (α : ℝ),
          0 ≤ α →
            ENNReal.ofReal (Real.exp (-↑ε)) ^ α *
                ((ENNReal.ofReal (Real.exp ↑ε) - 1) / (ENNReal.ofReal (Real.exp ↑ε) - ENNReal.ofReal (Real.exp (-↑ε)))) ≠
              ⊤ := by
  (intros; simp_all; done)
theorem HypCheckProof.SLang.ofDP_bound_SC1.h1 : ∀ (ε : NNReal) (α : ℝ),
      0 ≤ α →
        ENNReal.ofReal (Real.exp (-↑ε)) ^ α *
            ((ENNReal.ofReal (Real.exp ↑ε) - 1) / (ENNReal.ofReal (Real.exp ↑ε) - ENNReal.ofReal (Real.exp (-↑ε)))) ≠
          ⊤ := by
  intro hc_x0 hc_x2 hc_x3
  exact Classical.byCases (fun hc_h => @SLang.ofDP_bound_SC1 hc_x0 hc_h hc_x2 hc_x3) (fun hc_hn => @HypCheckProof.SLang.ofDP_bound_SC1.h1.gneg hc_x0 hc_hn hc_x2 hc_x3)

-- ENNReal.ereal_smul_inv_cancel_1, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ereal_smul_inv_cancel_1.h1 : ¬∀ {s : EReal}, s < ⊤ → ∀ (x : EReal), s * ↑(ENNReal.ofEReal s)⁻¹ * x = x := fun hc_h => absurd (@hc_h (0) (by
  decide) (1)) (by
  simp)

-- ENNReal.ereal_smul_inv_cancel_1, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ereal_smul_inv_cancel_1.h2 : ¬∀ {s : EReal}, 0 < s → ∀ (x : EReal), s * ↑(ENNReal.ofEReal s)⁻¹ * x = x := fun hc_h => absurd (@hc_h (⊤) (by
  decide) (1)) (by
  simp)

-- SLang.BernoulliExpNegSampleUnitAux_succ_true, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_succ_true.h5 : ¬∀ (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+), num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) (0) ((Bool.false, 1)) (1)) (by
  decide +kernel)

-- ENNReal.ereal_smul_inv_cancel_2, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ereal_smul_inv_cancel_2.h1 : ¬∀ {s : EReal}, s < ⊤ → ∀ (x : EReal), ↑(ENNReal.ofEReal s)⁻¹ * s * x = x := fun hc_h => absurd (@hc_h (0) (by
  decide) (1)) (by
  simp)

-- ENNReal.ereal_smul_inv_cancel_2, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ereal_smul_inv_cancel_2.h2 : ¬∀ {s : EReal}, 0 < s → ∀ (x : EReal), ↑(ENNReal.ofEReal s)⁻¹ * s * x = x := fun hc_h => absurd (@hc_h (⊤) (by
  decide) (1)) (by
  simp)

-- SLang.witness, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.witness.h4 : ¬∀ {U V : Type} {f : U → V} {i : V}, ∃ (x : U), i = f x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  simp)

-- SLang.BernoulliExpNegSampleUnitAux_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_zero.h4 : ¬∀ (num : ℕ) (den : ℕ+) (st st' : Bool × ℕ+), num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) ((Bool.false, 1)) ((Bool.false, 1))) (by
  decide +kernel)

-- nat_div_eq_le_lt_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.nat_div_eq_le_lt_iff.h3 : ¬∀ {a b c : ℕ}, a = b / c ↔ a * c ≤ b ∧ b < (a + 1) * c := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- SLang.BernoulliSample_normalizes, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliSample_normalizes.h2 : ¬∀ (num : ℕ) (den : ℕ+), num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- SLang.BernoulliExpNegSampleUnitAux_at_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_at_zero.h2 : ¬∀ (num : ℕ) (den : ℕ+), num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- ENNReal.elog_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.elog_injective.h2 : ¬∀ {x y : ENNReal}, x = y := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- SLang.trial_sum_ne_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.trial_sum_ne_top.h1 : ¬∀ (trial : SLang Bool), ∑' (n : ℕ), trial Bool.true ^ n ≠ ⊤ := fun hc_h => absurd (@hc_h (fun (a : Bool) => 1)) (by
  simp)

-- SLang.getLastI_eq_getLast, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.getLastI_eq_getLast.h1 : ¬∀ (L : List ℤ), L ≠ [] := fun hc_h => absurd (@hc_h ([])) (by
  decide +kernel)

