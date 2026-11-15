import SampCert

/-! Proofs emitted by HypCheck.lean (Lean 4.34.1). -/

-- euclidean_division_uniquness, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.euclidean_division_uniquness.h5.gneg : ∀ (r1 r2 q1 q2 : ℕ) {D : ℕ}, ¬0 < D → r1 < D → r2 < D → (r1 + D * q1 = r2 + D * q2 ↔ r1 = r2 ∧ q1 = q2) := by
  (intros; lia)
theorem HypCheckProof.euclidean_division_uniquness.h5 : ∀ (r1 r2 q1 q2 : ℕ) {D : ℕ}, r1 < D → r2 < D → (r1 + D * q1 = r2 + D * q2 ↔ r1 = r2 ∧ q1 = q2) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x6 hc_x7
  exact Classical.byCases (fun hc_h => @euclidean_division_uniquness hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_h hc_x6 hc_x7) (fun hc_hn => @HypCheckProof.euclidean_division_uniquness.h5.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_hn hc_x6 hc_x7)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.euclidean_division_uniquness.h5.derivable : ∀ (r1 r2 q1 q2 : ℕ) {D : ℕ}, r1 < D → r2 < D → 0 < D := by
  (intros; lia)

-- euclidean_division_uniquness, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.euclidean_division_uniquness.h6 : ¬∀ (r1 r2 q1 q2 : ℕ) {D : ℕ}, 0 < D → r2 < D → (r1 + D * q1 = r2 + D * q2 ↔ r1 = r2 ∧ q1 = q2) := fun hc_h => absurd (@hc_h (1) (0) (0) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- euclidean_division_uniquness, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.euclidean_division_uniquness.h7 : ¬∀ (r1 r2 q1 q2 : ℕ) {D : ℕ}, 0 < D → r1 < D → (r1 + D * q1 = r2 + D * q2 ↔ r1 = r2 ∧ q1 = q2) := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- SLang.δpmf_conv, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.δpmf_conv.h6 : ¬∀ {U V : Type} {f : U → V} (nq : SLang U) (a : V) (x : ↑{n : U | a = f n}),
        ∑' (i : ↑{n : U | a = f n}), nq ↑i ≠ ⊤ → ∑' (i : ↑{n : U | a = f n}), nq ↑i ≠ 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun (a : ℕ) => 0) (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | 1 = (fun (n : ℕ) => n + 1) n} })) (by
  simp)) (by
  simp)

-- SLang.B_eval_false_closed_form, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.SLang.B_eval_false_closed_form.h3.gneg : ∀ (ε : NNReal),
      0 < ε →
        ∀ (Bval : ENNReal),
          ¬Bval ≠ ⊤ →
            Bval ≤ 1 →
              ENNReal.ofReal (Real.exp (-↑ε)) * Bval + ENNReal.ofReal (Real.exp ↑ε) * (1 - Bval) = 1 →
                Bval = (ENNReal.ofReal (Real.exp ↑ε) - 1) / (ENNReal.ofReal (Real.exp ↑ε) - ENNReal.ofReal (Real.exp (-↑ε))) := by
  (intros; simp_all; done)
theorem HypCheckProof.SLang.B_eval_false_closed_form.h3 : ∀ (ε : NNReal),
      0 < ε →
        ∀ Bval ≤ 1,
          ENNReal.ofReal (Real.exp (-↑ε)) * Bval + ENNReal.ofReal (Real.exp ↑ε) * (1 - Bval) = 1 →
            Bval = (ENNReal.ofReal (Real.exp ↑ε) - 1) / (ENNReal.ofReal (Real.exp ↑ε) - ENNReal.ofReal (Real.exp (-↑ε))) := by
  intro hc_x0 hc_x1 hc_x2 hc_x4 hc_x5
  exact Classical.byCases (fun hc_h => @SLang.B_eval_false_closed_form hc_x0 hc_x1 hc_x2 hc_h hc_x4 hc_x5) (fun hc_hn => @HypCheckProof.SLang.B_eval_false_closed_form.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4 hc_x5)

-- ENNReal.ereal_smul_eq_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ereal_smul_eq_left.h3 : ¬∀ {w z : EReal}, ∀ s < ⊤, s * w = s * z → w = z := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide) (by
  simp)) (by
  simp)

-- ENNReal.ereal_smul_eq_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ereal_smul_eq_left.h4 : ¬∀ {w z : EReal} (s : EReal), 0 < s → s * w = s * z → w = z := fun hc_h => absurd (@hc_h (1) (⊤) (⊤) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- ENNReal.ereal_smul_eq_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ereal_smul_eq_left.h5 : ¬∀ {w z : EReal} (s : EReal), 0 < s → s < ⊤ → w = z := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  simp) (by
  decide)) (by
  simp)

-- SLang.δpmf_conv', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.δpmf_conv'.h5 : ¬∀ {U V : Type} (nq : SLang U) (f : U → V) (a : V),
        ∑' (i : ↑{n : U | a = f n}), nq ↑i ≠ ⊤ → ∑' (i : ↑{n : U | a = f n}), nq ↑i ≠ 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => 0) (fun n => n + 1 : ℕ → ℕ) (1) (by
  simp)) (by
  simp)

-- ENNReal.ereal_le_smul_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ereal_le_smul_left.h5 : ¬∀ {w z : EReal} (s : EReal), 0 < s → s < ⊤ → s * w ≤ s * z := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  simp) (by
  decide)) (by
  simp)

-- SLang.if_ge_2, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.if_ge_2.h4 : ¬∀ {γ : ENNReal} (x num : ℕ) (den : ℕ+), γ = ↑num / ↑↑den → num ≤ ↑den := fun hc_h => absurd (@hc_h _ (0) (2) (1) rfl) (by
  decide +kernel)

-- reducedPMF_pos, hypothesis 2: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.reducedPMF_pos.h2.der : ∀ {T : Type} {q : PMF T} (a : T), ¬q a = 0 → AbsCts ⇑q ⇑q := by
  (intros; solve_by_elim)
theorem HypCheckProof.reducedPMF_pos.h2 : ∀ {T : Type} {q : PMF T} (a : T) (Ha : ¬q a = 0),
      (reducedPMF (HypCheckProof.reducedPMF_pos.h2.der a Ha)) (⟨a, Ha⟩ : { t : T // ¬q t = 0 }) ≠ 0 := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @reducedPMF_pos hc_x0 hc_x1 (@HypCheckProof.reducedPMF_pos.h2.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x2 hc_x3

-- SLang.series_step_1, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.series_step_1.h2 : ¬∀ (num : ℕ) (den : ℕ+) (γ : ENNReal), γ = ↑num / ↑↑den → num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) _ rfl) (by
  decide +kernel)

-- SLang.BernoulliExpNegSampleUnit_apply_true, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnit_apply_true.h2 : ¬∀ (num : ℕ) (den : ℕ+) (γ : ENNReal), γ = ↑num / ↑↑den → num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) _ rfl) (by
  decide +kernel)

-- SLang.BernoulliExpNegSampleUnit_apply_true, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnit_apply_true.h4 : ¬∀ (num : ℕ) (den : ℕ+) (wf : num ≤ ↑den) (γ : ENNReal),
        SLang.BernoulliExpNegSampleUnit num den wf Bool.true = ENNReal.ofReal (Real.exp (-γ.toReal)) := fun hc_h => absurd (fun hc_k0 => @hc_h (1) (1) hc_k0 (0)) (by
  simp)

-- ENNReal.ofEReal_nonneg_inj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofEReal_nonneg_inj.h2 : ¬∀ {w z : EReal}, 0 ≤ z → (w = z ↔ ENNReal.ofEReal w = ENNReal.ofEReal z) := fun hc_h => absurd (@hc_h (⊥) (0) (by
  rfl)) (by
  simp)

-- ENNReal.ofEReal_nonneg_inj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofEReal_nonneg_inj.h3 : ¬∀ {w z : EReal}, 0 ≤ w → (w = z ↔ ENNReal.ofEReal w = ENNReal.ofEReal z) := fun hc_h => absurd (@hc_h (0) (⊥) (by
  rfl)) (by
  simp)

-- SLang.BernoulliExpNegSampleUnitAux_returns_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_returns_false.h5 : ¬∀ (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+), num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) (0) ((Bool.false, 1)) (1)) (by
  decide +kernel)

-- SLang.avoid_double_counting_algebra, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.avoid_double_counting_algebra.h2 : ¬∀ (r c : ENNReal), 1 - r ≠ ⊤ → ∑' (n : ℕ), r ^ n * (1 - r) * c + ∑' (n : ℕ), r ^ (n + 1) * (1 - r) * c = c * (1 + r) := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  norm_num)

-- SLang.avoid_double_counting_algebra, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.SLang.avoid_double_counting_algebra.h3.gneg : ∀ (r c : ENNReal),
      1 - r ≠ 0 → ¬1 - r ≠ ⊤ → ∑' (n : ℕ), r ^ n * (1 - r) * c + ∑' (n : ℕ), r ^ (n + 1) * (1 - r) * c = c * (1 + r) := by
  (intros; simp_all; done)
theorem HypCheckProof.SLang.avoid_double_counting_algebra.h3 : ∀ (r c : ENNReal), 1 - r ≠ 0 → ∑' (n : ℕ), r ^ n * (1 - r) * c + ∑' (n : ℕ), r ^ (n + 1) * (1 - r) * c = c * (1 + r) := by
  intro hc_x0 hc_x1 hc_x2
  exact Classical.byCases (fun hc_h => @SLang.avoid_double_counting_algebra hc_x0 hc_x1 hc_x2 hc_h) (fun hc_hn => @HypCheckProof.SLang.avoid_double_counting_algebra.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.SLang.avoid_double_counting_algebra.h3.derivable : ∀ (r c : ENNReal), 1 - r ≠ 0 → 1 - r ≠ ⊤ := by
  (intros; simp; done)

-- SLang.probUntil_apply_norm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.probUntil_apply_norm.h4 : ¬∀ {T : Type} (body : SLang T) (cond : T → Bool) (x : T),
        body.probUntil cond x =
          (if cond x = Bool.true then body x else 0) * (∑' (x : T), if cond x = Bool.true then body x else 0)⁻¹ := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => 1) (fun _ => true : ℕ → Bool) (0)) (by
  simp)

-- SLang.BernoulliExpNegSampleUnitAux_progress, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_progress.h4 : ¬∀ (num : ℕ) (den : ℕ+) (fuel k : ℕ), num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) (0) (0)) (by
  decide +kernel)

-- SLang.probUntil_apply_unsat, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.probUntil_apply_unsat.h4 : ¬∀ {T : Type} (body : SLang T) (cond : T → Bool) (x : T), body.probUntil cond x = 0 := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => 1) (not : Bool → Bool) (Bool.false)) (by
  simp)

-- SLang.pure_apply_of_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.pure_apply_of_ne.h3 : ¬∀ {α : Type} (a a' : α), SLang.probPure a a' = 0 := fun hc_h => absurd (@hc_h (ℕ) (0) (0)) (by
  simp)

-- SLang.BernoulliSample_apply, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliSample_apply.h2 : ¬∀ (num : ℕ) (den : ℕ+) (b : Bool), num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) (Bool.false)) (by
  decide +kernel)

-- SLang.ENNReal.tsum_pos_int, hypothesis 1: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.SLang.ENNReal.tsum_pos_int.h1.gneg : ∀ {f : ℤ → ENNReal}, ¬∑' (x : ℤ), f x ≠ ⊤ → (∀ (x : ℤ), f x ≠ 0) → 0 < ∑' (x : ℤ), f x := by
  (intros; simp_all; done)
theorem HypCheckProof.SLang.ENNReal.tsum_pos_int.h1 : ∀ {f : ℤ → ENNReal}, (∀ (x : ℤ), f x ≠ 0) → 0 < ∑' (x : ℤ), f x := by
  intro hc_x0 hc_x2
  exact Classical.byCases (fun hc_h => @SLang.ENNReal.tsum_pos_int hc_x0 hc_h hc_x2) (fun hc_hn => @HypCheckProof.SLang.ENNReal.tsum_pos_int.h1.gneg hc_x0 hc_hn hc_x2)

-- SLang.ENNReal.tsum_pos_int, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.ENNReal.tsum_pos_int.h2 : ¬∀ {f : ℤ → ENNReal}, ∑' (x : ℤ), f x ≠ ⊤ → 0 < ∑' (x : ℤ), f x := fun hc_h => absurd (@hc_h (fun (a : ℤ) => 0) (by
  simp)) (by
  simp)

-- SLang.BernoulliExpNegSampleUnitAux_sup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_sup.h3 : ¬∀ (num : ℕ) (den n : ℕ+), num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) (1)) (by
  decide +kernel)

-- SLang.probGeometric_normalizes, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.probGeometric_normalizes.h1 : ¬∀ (trial : SLang Bool), trial Bool.true < 1 → ∑' (n : ℕ), trial.probGeometric n = 1 := fun hc_h => absurd (@hc_h (fun (a : Bool) => 0) (by
  simp)) (by
  simp)

-- SLang.probGeometric_normalizes, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.probGeometric_normalizes.h2 : ¬∀ (trial : SLang Bool), trial Bool.false + trial Bool.true = 1 → ∑' (n : ℕ), trial.probGeometric n = 1 := fun hc_h => absurd (@hc_h (fun (a : Bool) => if a = Bool.false then 0 else 1) (by
  simp)) (by
  simp)

-- SLang.ofDP_bound_SC0, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.ofDP_bound_SC0.h1 : ¬∀ (ε : NNReal), ENNReal.ofReal (Real.exp ↑ε) - ENNReal.ofReal (Real.exp (-↑ε)) ≠ 0 := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- SLang.adhoc, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.adhoc.h1 : ¬∀ (n : ℕ), n - 2 + 1 = n - 1 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

