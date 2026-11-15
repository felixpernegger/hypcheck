import SampCert

/-! Proofs emitted by HypCheck.lean (Lean 4.34.1). -/

-- SLang.privNoisedHistogramAux_DP, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.privNoisedHistogramAux_DP.h10 : ¬∀ {T : Type} (numBins : ℕ+) (B : Bins T ↑numBins) [dps : SLang.DPSystem T] [dpn : SLang.DPNoise dps] (ε₁ ε₂ : ℕ+)
        (ε : NNReal), SLang.DPNoise.noise_priv dps ε₁ (ε₂ * numBins) (ε / ↑↑numBins) → ∀ (n : ℕ), n < ↑numBins := fun hc_h => absurd (@hc_h (ℕ) (1) ({ bin := fun (a : ℕ) => 0 : Bins ℕ ↑1 }) (SLang.PureDPSystem) (SLang.laplace_pureDPSystem) (2) (1) (2) (by
  rfl) (1)) (by
  decide +kernel)

-- SLang.BernoulliExpNegSampleUnitAux_monotone_counter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_monotone_counter.h5 : ¬∀ (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (n : ℕ+), st ≠ (Bool.false, n) → st.2 ≥ n → num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) (0) ((Bool.false, 2)) (1) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- SLang.BernoulliExpNegSampleUnitAux_monotone_counter, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_monotone_counter.h6 : ¬∀ (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (n : ℕ+) (wf : num ≤ ↑den),
        st.2 ≥ n →
          SLang.probWhileCut (fun (state : Bool × ℕ+) => state.1) (SLang.BernoulliExpNegSampleUnitLoop num den wf) fuel st
              (Bool.false, n) =
            0 := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (0) (1) (1) ((Bool.false, 1)) (1) hc_k0 hc_k1) (by
  simp)

-- SLang.BernoulliExpNegSampleUnitAux_preservation, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_preservation.h5 : ¬∀ (num : ℕ) (den : ℕ+) (fuel fuel' k : ℕ), fuel ≥ fuel' → num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- SLang.geometric_monotone_counter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.geometric_monotone_counter.h4 : ¬∀ (trial : SLang Bool) (fuel n : ℕ) (st : Bool × ℕ),
        st.2 ≥ n → SLang.probWhileCut SLang.geoLoopCond trial.geoLoopBody fuel st (Bool.false, n) = 0 := fun hc_h => absurd (@hc_h (fun (a : Bool) => 0) (1) (0) ((Bool.false, 0)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- SLang.BernoulliExpNegSampleUnitAux_characterization, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_characterization.h4 : ¬∀ (num : ℕ) (den : ℕ+) (n extra : ℕ), n > 1 → num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) (2) (0) (by
  decide)) (by
  decide +kernel)

-- SLang.BernoulliExpNegSampleUnitAux_characterization, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_characterization.h5 : ¬∀ (num : ℕ) (den : ℕ+) (n extra : ℕ), num ≤ ↑den → n > 1 := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- reducedPMF_tsum_mul_eq, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.reducedPMF_tsum_mul_eq.h4.der : ∀ {T : Type} (p q : PMF T), AbsCts ⇑p ⇑q → ∀ (f : ENNReal → ENNReal → ENNReal), AbsCts ⇑q ⇑q := by
  (intros; solve_by_elim)
theorem HypCheckProof.reducedPMF_tsum_mul_eq.h4 : ∀ {T : Type} (p q : PMF T) (H : AbsCts ⇑p ⇑q) (f : ENNReal → ENNReal → ENNReal),
      ∑' (x : T), f (p x) (q x) * q x =
        ∑' (x : { t : T // ¬q t = 0 }),
          f ((reducedPMF H) x) ((reducedPMF (HypCheckProof.reducedPMF_tsum_mul_eq.h4.der p q H f)) x) *
            (reducedPMF (HypCheckProof.reducedPMF_tsum_mul_eq.h4.der p q H f)) x := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @reducedPMF_tsum_mul_eq hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.reducedPMF_tsum_mul_eq.h4.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4) hc_x4

-- SLang.ENNReal.tsum_pos, hypothesis 2: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.SLang.ENNReal.tsum_pos.h2.gneg : ∀ {T : Type} {f : T → ENNReal}, ¬∑' (x : T), f x ≠ ⊤ → (∀ (x : T), f x ≠ 0) → ∀ (i : T), 0 < ∑' (x : T), f x := by
  (intros; simp_all; done)
theorem HypCheckProof.SLang.ENNReal.tsum_pos.h2 : ∀ {T : Type} {f : T → ENNReal}, (∀ (x : T), f x ≠ 0) → ∀ (i : T), 0 < ∑' (x : T), f x := by
  intro hc_x0 hc_x1 hc_x3 hc_x4
  exact Classical.byCases (fun hc_h => @SLang.ENNReal.tsum_pos hc_x0 hc_x1 hc_h hc_x3 hc_x4) (fun hc_hn => @HypCheckProof.SLang.ENNReal.tsum_pos.h2.gneg hc_x0 hc_x1 hc_hn hc_x3 hc_x4)

-- SLang.ENNReal.tsum_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.ENNReal.tsum_pos.h3 : ¬∀ {T : Type} {f : T → ENNReal}, ∑' (x : T), f x ≠ ⊤ → ∀ (i : T), 0 < ∑' (x : T), f x := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => 0) (by
  simp) (0)) (by
  simp)

-- SLang.BernoulliExpNegSampleUnit_apply_false, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnit_apply_false.h2 : ¬∀ (num : ℕ) (den : ℕ+) (γ : ENNReal), γ = ↑num / ↑↑den → num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) _ rfl) (by
  decide +kernel)

-- SLang.ite_mono_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.ite_mono_left.h5 : ¬∀ {P : Prop} {D : Decidable P} {a b c : ENNReal}, (if P then a else b) ≤ if P then c else b := fun hc_h => absurd (@hc_h (True) (instDecidableTrue) (1) (0) (0)) (by
  simp)

-- ENNReal.mul_mul_inv_eq_mul_cancel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_mul_inv_eq_mul_cancel.h2 : ¬∀ {x y : ENNReal}, ¬(x ≠ 0 ∧ y = ⊤) → x * y⁻¹ * y = x := fun hc_h => absurd (@hc_h (1) (0) (by
  simp)) (by
  simp)

-- ENNReal.mul_mul_inv_eq_mul_cancel, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_mul_inv_eq_mul_cancel.h3 : ¬∀ {x y : ENNReal}, (y = 0 → x = 0) → x * y⁻¹ * y = x := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- SLang.ENNReal.tsum_lb_single, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.ENNReal.tsum_lb_single.h4 : ¬∀ {T : Type} (x : T) (f : T → ENNReal) (l : ENNReal), l ≤ ∑' (a : T), f a := fun hc_h => absurd (@hc_h (ℕ) (0) (fun (a : ℕ) => 0) (1)) (by
  simp)

-- SLang.ENNReal.tsum_lb_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.ENNReal.tsum_lb_subset.h4 : ¬∀ {T : Type} (P : T → Prop) (f : T → ENNReal) (l : ENNReal), l ≤ ∑' (a : T), f a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => 0) (1)) (by
  simp)

-- SLang.ite_simpl_5, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.ite_simpl_5.h3 : Not
      (∀ (n c : Nat) (a : ENNReal),
        @Eq ENNReal
          (@ite ENNReal
            (@Eq Int (@Neg.neg Int Int.instNegInt (@Nat.cast Int instNatCastInt n)) (@Nat.cast Int instNatCastInt c))
            ((@Neg.neg Int Int.instNegInt (@Nat.cast Int instNatCastInt n)).instDecidableEq
              (@Nat.cast Int instNatCastInt c))
            a (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)))
          (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat ENNReal (nat_lit 1) (@One.toOfNat1 ENNReal ENNReal.instOne))) (by
  simp)

-- SLang.halve_wf, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.halve_wf.h3 : ¬∀ (num : ℕ) (den st : ℕ+), num ≤ ↑(st * den) := fun hc_h => absurd (@hc_h (2) (1) (1)) (by
  decide +kernel)

-- SLang.geometric_characterization, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.geometric_characterization.h3 : ¬∀ (trial : SLang Bool) (n extra : ℕ),
        SLang.probWhileCut SLang.geoLoopCond trial.geoLoopBody (extra + (n + 1)) (Bool.true, 0) (Bool.false, n) =
          trial Bool.true ^ (n - 1) * trial Bool.false := fun hc_h => absurd (@hc_h (fun (a : Bool) => 1) (0) (0)) (by
  simp)

-- SLang.BernoulliExpNegSampleUnitAux_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_apply.h3 : ¬∀ (num : ℕ) (den n : ℕ+), num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) (1)) (by
  decide +kernel)

-- SLang.BernoulliExpNegSampleUnitAux_at_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_at_one.h2 : ¬∀ (num : ℕ) (den : ℕ+), num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- SLang.geometric_progress', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.geometric_progress'.h2 : ¬∀ (trial : SLang Bool) (n : ℕ),
        SLang.probWhileCut SLang.geoLoopCond trial.geoLoopBody (n + 1) (Bool.true, 0) (Bool.false, n) =
          trial Bool.true ^ (n - 1) * trial Bool.false := fun hc_h => absurd (@hc_h (fun (a : Bool) => 1) (0)) (by
  simp)

-- SLang.trial_le_1, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.trial_le_1.h1 : ¬∀ (trial : SLang Bool) (i : ℕ), trial Bool.true ^ i ≤ 1 := fun hc_h => absurd (@hc_h (fun (a : Bool) => 2) (1)) (by
  simp)

-- SLang.UniformPowerOfTwoSample_apply, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.UniformPowerOfTwoSample_apply.h2 : ¬∀ (n : ℕ+) (x : ℕ), SLang.UniformPowerOfTwoSample n x = 1 / 2 ^ Nat.log 2 ↑n := fun hc_h => absurd (@hc_h (1) (1)) (by
  simp)

-- SLang.BernoulliSample_normalizes', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliSample_normalizes'.h2 : ¬∀ (num : ℕ) (den : ℕ+), num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- SLang.geo_cdf_rec, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.geo_cdf_rec.h1 : ¬∀ (β : ENNReal) (n : ℕ), SLang.geo_cdf β (n + 1) = β + (1 - β) * SLang.geo_cdf β n := fun hc_h => absurd (@hc_h (⊤) (0)) (by
  decide +kernel)

-- SLang.Nat_eq_to_ENNReal_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.Nat_eq_to_ENNReal_eq.h2 : Not
      (∀ (a b : Nat),
        @Eq ENNReal
          (@Nat.cast ENNReal
            (@AddMonoidWithOne.toNatCast ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
            a)
          (@Nat.cast ENNReal
            (@AddMonoidWithOne.toNatCast ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
            b)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  simp)

-- SLang.ENNReal_eq_to_Real_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.ENNReal_eq_to_Real_eq.h2 : ¬∀ (a b : ENNReal), a.toReal = b.toReal := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- euclidean_division, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.euclidean_division.h2 : ¬∀ (n : ℕ) {D : ℕ}, ∃ (q : ℕ), ∃ r < D, n = r + D * q := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- SLang.BernoulliExpNegSampleAux_split, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleAux_split.h2 : ¬∀ (num : ℕ) (den : ℕ+), num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- UInt32.toNa_of_non_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.UInt32.toNa_of_non_zero.h1 : ¬∀ {n : UInt32}, 0 < n.toNat := fun hc_h => absurd (@hc_h (UInt32.ofNat 0)) (by
  decide +kernel)

-- SLang.trial_sum_ne_top', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.trial_sum_ne_top'.h1 : ¬∀ (trial : SLang Bool), ∑' (n : ℕ), trial Bool.true ^ n * trial Bool.true ≠ ⊤ := fun hc_h => absurd (@hc_h (fun (a : Bool) => 1)) (by
  simp)

-- SLang.nm2p2, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.nm2p2.h1 : ¬∀ (n : ℕ), n - 2 + 2 = n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

