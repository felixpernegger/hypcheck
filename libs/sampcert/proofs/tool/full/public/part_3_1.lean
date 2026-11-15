import SampCert

/-! Proofs emitted by HypCheck.lean (Lean 4.34.1). -/

-- SLang.ApproximateDP_of_zCDP_pos_lt_one, hypothesis 10: removable
set_option maxHeartbeats 200000 in
theorem HypCheckProof.SLang.ApproximateDP_of_zCDP_pos_lt_one.h10.gneg : ∀ {T U : Type} [inst : Countable U] (m : SLang.Mechanism T U) (ε : Real),
      @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) ε →
        @SLang.zCDPBound T U m
            (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
              (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                (@OfNat.ofNat Real (nat_lit 2)
                  (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
              (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) ε
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
          @SLang.ACNeighbour T U m →
            ∀ (δ : NNReal),
              @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) ↑δ →
                Not (@LT.lt Real Real.instLT (↑δ) (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))) →
                  @SLang.DP' T U m
                    (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                      (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                        (@HPow.hPow Real Nat Real
                          (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) ε
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@OfNat.ofNat Real (nat_lit 2)
                          (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) ε
                        (@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow)
                          (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                            (@OfNat.ofNat Real (nat_lit 2)
                              (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (Real.log
                              (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) ↑δ)))
                          (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                            (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                            (@OfNat.ofNat Real (nat_lit 2)
                              (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))))
                    δ := by
  (intros; exact?)
theorem HypCheckProof.SLang.ApproximateDP_of_zCDP_pos_lt_one.h10 : ∀ {T U : Type} [inst : Countable U] (m : SLang.Mechanism T U) (ε : Real),
      @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) ε →
        @SLang.zCDPBound T U m
            (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
              (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                (@OfNat.ofNat Real (nat_lit 2)
                  (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
              (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) ε
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
          @SLang.ACNeighbour T U m →
            ∀ (δ : NNReal),
              @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) ↑δ →
                @SLang.DP' T U m
                  (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd)
                    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                      (@HPow.hPow Real Nat Real
                        (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) ε
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@OfNat.ofNat Real (nat_lit 2)
                        (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                    (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) ε
                      (@HPow.hPow Real Real Real (@instHPow Real Real Real.instPow)
                        (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                          (@OfNat.ofNat Real (nat_lit 2)
                            (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (Real.log
                            (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                              (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) ↑δ)))
                        (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                          (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                          (@OfNat.ofNat Real (nat_lit 2)
                            (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))))
                  δ := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @SLang.ApproximateDP_of_zCDP_pos_lt_one hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_h) (fun hc_hn => @HypCheckProof.SLang.ApproximateDP_of_zCDP_pos_lt_one.h10.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_hn)

-- SLang.BernoulliExpNegSampleUnitAux_apply', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_apply'.h3 : ¬∀ (num : ℕ) (den : ℕ+), ∀ n > 1, ∀ (γ : ENNReal), γ = ↑num / ↑↑den → num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) (2) (by
  decide) _ rfl) (by
  decide +kernel)

-- ENNReal.ereal_smul_lt_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ereal_smul_lt_left.h3 : ¬∀ {w z : EReal}, ∀ s < ⊤, s * w < s * z → w < z := fun hc_h => absurd (@hc_h (1) (0) (⊥) (by
  decide) (by
  simp)) (by
  simp)

-- ENNReal.ereal_smul_lt_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ereal_smul_lt_left.h5 : ¬∀ {w z : EReal} (s : EReal), 0 < s → s < ⊤ → w < z := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  simp) (by
  decide)) (by
  simp)

-- ENNReal.ofEReal_le_mono_conv_nonneg, hypothesis 2: removable
set_option maxHeartbeats 200000 in
theorem HypCheckProof.ENNReal.ofEReal_le_mono_conv_nonneg.h2.gneg : ∀ {w z : EReal}, ¬0 ≤ w → 0 ≤ z → ENNReal.ofEReal w ≤ ENNReal.ofEReal z → w ≤ z := by
  (intros; grind)
theorem HypCheckProof.ENNReal.ofEReal_le_mono_conv_nonneg.h2 : ∀ {w z : EReal}, 0 ≤ z → ENNReal.ofEReal w ≤ ENNReal.ofEReal z → w ≤ z := by
  intro hc_x0 hc_x1 hc_x3 hc_x4
  exact Classical.byCases (fun hc_h => @ENNReal.ofEReal_le_mono_conv_nonneg hc_x0 hc_x1 hc_h hc_x3 hc_x4) (fun hc_hn => @HypCheckProof.ENNReal.ofEReal_le_mono_conv_nonneg.h2.gneg hc_x0 hc_x1 hc_hn hc_x3 hc_x4)

-- ENNReal.ofEReal_le_mono_conv_nonneg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofEReal_le_mono_conv_nonneg.h3 : ¬∀ {w z : EReal}, 0 ≤ w → ENNReal.ofEReal w ≤ ENNReal.ofEReal z → w ≤ z := fun hc_h => absurd (@hc_h (0) (⊥) (by
  rfl) (by
  simp)) (by
  decide +kernel)

-- ENNReal.ofEReal_le_mono_conv_nonneg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofEReal_le_mono_conv_nonneg.h4 : ¬∀ {w z : EReal}, 0 ≤ w → 0 ≤ z → w ≤ z := fun hc_h => absurd (@hc_h (1) (0) (by
  simp) (by
  rfl)) (by
  simp)

-- SLang.geometric_preservation', hypothesis 3: removable
set_option maxHeartbeats 200000 in
theorem HypCheckProof.SLang.geometric_preservation'.h3.gneg : ∀ (trial : SLang Bool) (n m : ℕ),
      ¬¬m = 0 →
        n ≥ m →
          SLang.probWhileCut SLang.geoLoopCond trial.geoLoopBody (n + 2) (Bool.true, 0) (Bool.false, m) =
            SLang.probWhileCut SLang.geoLoopCond trial.geoLoopBody (n + 1) (Bool.true, 0) (Bool.false, m) := by
  (intros; simp_all; done)
theorem HypCheckProof.SLang.geometric_preservation'.h3 : ∀ (trial : SLang Bool) (n m : ℕ),
      n ≥ m →
        SLang.probWhileCut SLang.geoLoopCond trial.geoLoopBody (n + 2) (Bool.true, 0) (Bool.false, m) =
          SLang.probWhileCut SLang.geoLoopCond trial.geoLoopBody (n + 1) (Bool.true, 0) (Bool.false, m) := by
  intro hc_x0 hc_x1 hc_x2 hc_x4
  exact Classical.byCases (fun hc_h => @SLang.geometric_preservation' hc_x0 hc_x1 hc_x2 hc_h hc_x4) (fun hc_hn => @HypCheckProof.SLang.geometric_preservation'.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4)

-- SLang.BernoulliExpNegSampleUnit_normalizes, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnit_normalizes.h2 : ¬∀ (num : ℕ) (den : ℕ+) (γ : ENNReal), γ = ↑num / ↑↑den → num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) _ rfl) (by
  decide +kernel)

-- SLang.BernoulliExpNegSampleUnit_normalizes, hypothesis 4: removable
set_option maxHeartbeats 200000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnit_normalizes.h4.gneg : ∀ (num : ℕ) (den : ℕ+) (wf : num ≤ ↑den) (γ : ENNReal),
      ¬γ = ↑num / ↑↑den → ∑' (b : Bool), SLang.BernoulliExpNegSampleUnit num den wf b = 1 := by
  (intros; exact?)
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnit_normalizes.h4 : ∀ (num : ℕ) (den : ℕ+) (wf : num ≤ ↑den) (γ : ENNReal), ∑' (b : Bool), SLang.BernoulliExpNegSampleUnit num den wf b = 1 := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact Classical.byCases (fun hc_h => @SLang.BernoulliExpNegSampleUnit_normalizes hc_x0 hc_x1 hc_x2 hc_x3 hc_h) (fun hc_hn => @HypCheckProof.SLang.BernoulliExpNegSampleUnit_normalizes.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn)

-- SLang.gamma_extract', hypothesis 4: removable
set_option maxHeartbeats 200000 in
theorem HypCheckProof.SLang.gamma_extract'.h4.gneg : ∀ (num : Nat) (den : PNat) (x : ENNReal),
      @Ne ENNReal x (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) →
        Not (@Ne ENNReal x (@Top.top ENNReal ENNReal.instTop)) →
          @Eq ENNReal
            (@HDiv.hDiv ENNReal ENNReal ENNReal (@instHDiv ENNReal (@DivInvMonoid.toDiv ENNReal ENNReal.instDivInvMonoid))
              (@Nat.cast ENNReal
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                num)
              (@HMul.hMul ENNReal ENNReal ENNReal
                (@instHMul ENNReal
                  (@Distrib.toMul ENNReal
                    (@instDistribOfSemiring ENNReal (@CommSemiring.toSemiring ENNReal ENNReal.instCommSemiring))))
                x
                (@Nat.cast ENNReal
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  ↑den)))
            (@HMul.hMul ENNReal ENNReal ENNReal
              (@instHMul ENNReal
                (@Distrib.toMul ENNReal
                  (@instDistribOfSemiring ENNReal (@CommSemiring.toSemiring ENNReal ENNReal.instCommSemiring))))
              (@HDiv.hDiv ENNReal ENNReal ENNReal (@instHDiv ENNReal (@DivInvMonoid.toDiv ENNReal ENNReal.instDivInvMonoid))
                (@Nat.cast ENNReal
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  num)
                (@Nat.cast ENNReal
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  ↑den))
              (@Inv.inv ENNReal ENNReal.instInv x)) := by
  (intros; simp_all; done)
theorem HypCheckProof.SLang.gamma_extract'.h4 : ∀ (num : Nat) (den : PNat) (x : ENNReal),
      @Ne ENNReal x (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) →
        @Eq ENNReal
          (@HDiv.hDiv ENNReal ENNReal ENNReal (@instHDiv ENNReal (@DivInvMonoid.toDiv ENNReal ENNReal.instDivInvMonoid))
            (@Nat.cast ENNReal
              (@AddMonoidWithOne.toNatCast ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
              num)
            (@HMul.hMul ENNReal ENNReal ENNReal
              (@instHMul ENNReal
                (@Distrib.toMul ENNReal
                  (@instDistribOfSemiring ENNReal (@CommSemiring.toSemiring ENNReal ENNReal.instCommSemiring))))
              x
              (@Nat.cast ENNReal
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                ↑den)))
          (@HMul.hMul ENNReal ENNReal ENNReal
            (@instHMul ENNReal
              (@Distrib.toMul ENNReal
                (@instDistribOfSemiring ENNReal (@CommSemiring.toSemiring ENNReal ENNReal.instCommSemiring))))
            (@HDiv.hDiv ENNReal ENNReal ENNReal (@instHDiv ENNReal (@DivInvMonoid.toDiv ENNReal ENNReal.instDivInvMonoid))
              (@Nat.cast ENNReal
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                num)
              (@Nat.cast ENNReal
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                ↑den))
            (@Inv.inv ENNReal ENNReal.instInv x)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact Classical.byCases (fun hc_h => @SLang.gamma_extract' hc_x0 hc_x1 hc_x2 hc_x3 hc_h) (fun hc_hn => @HypCheckProof.SLang.gamma_extract'.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn)

-- SLang.sv4_presample_split'', hypothesis 7: removable
set_option maxHeartbeats 200000 in
theorem HypCheckProof.SLang.sv4_presample_split''.h7.der : ∀ [dps : SLang.DPSystem ℕ] [dpn : SLang.DPNoise dps] (ε₁ ε₂ : ℕ+) (point : ℕ) (z : ℤ)
      (p : { l : List ℤ // l.length = point }), (↑p ++ [z]).length = point + 1 := by
  (intros; simp_all <;> lia)
theorem HypCheckProof.SLang.sv4_presample_split''.h7 : ∀ [dps : SLang.DPSystem ℕ] [dpn : SLang.DPNoise dps] (ε₁ ε₂ : ℕ+) (point : ℕ) (z : ℤ)
      (p : { l : List ℤ // l.length = point }),
      (SLang.privNoiseGuess ε₁ ε₂) z * SLang.sv4_presample ε₁ ε₂ point p =
        SLang.sv4_presample ε₁ ε₂ (point + 1)
          (⟨↑p ++ [z], HypCheckProof.SLang.sv4_presample_split''.h7.der ε₁ ε₂ point z p⟩ :
            { l : List ℤ // l.length = point + 1 }) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @SLang.sv4_presample_split'' hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.SLang.sv4_presample_split''.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6)

-- SLang.γ_le_1, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.γ_le_1.h3 : Not
      (∀ {γ : ENNReal} (num : Nat) (den : PNat),
        @Eq ENNReal γ
            (@HDiv.hDiv ENNReal ENNReal ENNReal (@instHDiv ENNReal (@DivInvMonoid.toDiv ENNReal ENNReal.instDivInvMonoid))
              (@Nat.cast ENNReal
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                num)
              (@Nat.cast ENNReal
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                ↑den)) →
          @LE.le ENNReal ENNReal.instLE γ (@OfNat.ofNat ENNReal (nat_lit 1) (@One.toOfNat1 ENNReal ENNReal.instOne))) := fun hc_h => absurd (@hc_h _ (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat PNat (nat_lit 1)
      (@instOfNatPNatOfNeZeroNat (nat_lit 1)
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) rfl) (by
  simp)

-- SLang.γ_le_1, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.γ_le_1.h4 : ¬∀ {γ : ENNReal} (num : ℕ) (den : ℕ+), num ≤ ↑den → γ ≤ 1 := fun hc_h => absurd (@hc_h (2) (0) (1) (by
  decide)) (by
  simp)

-- SLang.BernoulliExpNegSampleUnitAux_normalizes, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_normalizes.h3 : ¬∀ {γ : ENNReal} (num : ℕ) (den : ℕ+), γ = ↑num / ↑↑den → num ≤ ↑den := fun hc_h => absurd (@hc_h _ (2) (1) rfl) (by
  decide +kernel)

-- SLang.BernoulliExpNegSampleUnitAux_normalizes, hypothesis 4: removable
set_option maxHeartbeats 200000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_normalizes.h4.gneg : ∀ {γ : ENNReal} (num : ℕ) (den : ℕ+) (wf : num ≤ ↑den),
      ¬γ = ↑num / ↑↑den → ∑' (n : ℕ), SLang.BernoulliExpNegSampleUnitAux num den wf n = 1 := by
  (intros; exact?)
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_normalizes.h4 : ∀ {γ : ENNReal} (num : ℕ) (den : ℕ+) (wf : num ≤ ↑den), ∑' (n : ℕ), SLang.BernoulliExpNegSampleUnitAux num den wf n = 1 := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact Classical.byCases (fun hc_h => @SLang.BernoulliExpNegSampleUnitAux_normalizes hc_x0 hc_x1 hc_x2 hc_x3 hc_h) (fun hc_hn => @HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_normalizes.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn)

-- ENNReal.eexp_mul_nonneg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.eexp_mul_nonneg.h2 : ¬∀ {r w : EReal}, r ≠ ⊤ → ENNReal.eexp (r * w) = ENNReal.eexp w ^ r.toReal := fun hc_h => absurd (@hc_h (⊥) (1) (by
  decide)) (by
  simp)

-- ENNReal.eexp_mul_nonneg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.eexp_mul_nonneg.h3 : ¬∀ {r w : EReal}, 0 ≤ r → ENNReal.eexp (r * w) = ENNReal.eexp w ^ r.toReal := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- SLang.BernoulliExpNegSampleUnitAux_succ_false, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliExpNegSampleUnitAux_succ_false.h5 : ¬∀ (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+), num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1) (0) ((Bool.false, 1)) (1)) (by
  decide +kernel)

-- SLang.ite_conv_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.ite_conv_left.h5 : ¬∀ {P : Prop} {D : Decidable P} {a b c : ENNReal}, (if P then a else b) = if P then c else b := fun hc_h => absurd (@hc_h (True) (instDecidableTrue) (0) (0) (1)) (by
  simp)

-- SLang.probUntil_apply_sat, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.probUntil_apply_sat.h4 : ¬∀ {T : Type} (body : SLang T) (cond : T → Bool) (x : T),
        body.probUntil cond x = body x * (1 - ∑' (x : T), if cond x = Bool.true then 0 else body x)⁻¹ := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => 1) (not : Bool → Bool) (Bool.true)) (by
  simp)

-- SLang.series_step_4_pre, hypothesis 1: removable
set_option maxHeartbeats 200000 in
theorem HypCheckProof.SLang.series_step_4_pre.h1.gneg : ∀ (γ : ENNReal),
      ¬γ ≠ ⊤ →
        γ ≤ 1 →
          ∑' (n : ℕ), (SLang.mass' (2 * n) γ - SLang.mass' (2 * n + 1) γ) =
            ENNReal.ofReal (∑' (n : ℕ), SLang.mass'' n (-γ.toReal)) := by
  (intros; simp_all; done)
theorem HypCheckProof.SLang.series_step_4_pre.h1 : ∀ γ ≤ 1,
      ∑' (n : ℕ), (SLang.mass' (2 * n) γ - SLang.mass' (2 * n + 1) γ) =
        ENNReal.ofReal (∑' (n : ℕ), SLang.mass'' n (-γ.toReal)) := by
  intro hc_x0 hc_x2
  exact Classical.byCases (fun hc_h => @SLang.series_step_4_pre hc_x0 hc_h hc_x2) (fun hc_hn => @HypCheckProof.SLang.series_step_4_pre.h1.gneg hc_x0 hc_hn hc_x2)

-- SLang.tsum_pos_int, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.tsum_pos_int.h1 : ¬∀ {f : ℤ → ENNReal}, (∀ (x : ℤ), f x ≠ 0) → 0 < (∑' (x : ℤ), f x).toReal := fun hc_h => absurd (@hc_h (fun (a : ℤ) => 1) (by
  simp)) (by
  simp)

-- SLang.tsum_pos_int, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.tsum_pos_int.h2 : ¬∀ {f : ℤ → ENNReal}, ∑' (x : ℤ), f x ≠ ⊤ → 0 < (∑' (x : ℤ), f x).toReal := fun hc_h => absurd (@hc_h (fun (a : ℤ) => 0) (by
  simp)) (by
  simp)

-- SLang.tsum_ne_zero_of_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.tsum_ne_zero_of_ne_zero.h3 : ¬∀ {T : Type} [inst : Inhabited T] (f : T → ENNReal), ∑' (x : T), f x ≠ 0 := fun hc_h => absurd (@hc_h (ℕ) (instInhabitedNat) (fun (a : ℕ) => 0)) (by
  simp)

-- SLang.γ_ne_top, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.γ_ne_top.h3 : ¬∀ {γ : ENNReal} (num : ℕ) (den : ℕ+), γ ≠ ⊤ := fun hc_h => absurd (@hc_h (⊤) (0) (1)) (by
  decide +kernel)

-- SLang.series_step_4, hypothesis 1: removable
set_option maxHeartbeats 200000 in
theorem HypCheckProof.SLang.series_step_4.h1.gneg : ∀ (γ : ENNReal),
      ¬γ ≠ ⊤ →
        γ ≤ 1 → ∑' (n : ℕ), (SLang.mass' (2 * n) γ - SLang.mass' (2 * n + 1) γ) = ENNReal.ofReal (Real.exp (-γ.toReal)) := by
  (intros; simp_all; done)
theorem HypCheckProof.SLang.series_step_4.h1 : ∀ γ ≤ 1, ∑' (n : ℕ), (SLang.mass' (2 * n) γ - SLang.mass' (2 * n + 1) γ) = ENNReal.ofReal (Real.exp (-γ.toReal)) := by
  intro hc_x0 hc_x2
  exact Classical.byCases (fun hc_h => @SLang.series_step_4 hc_x0 hc_h hc_x2) (fun hc_hn => @HypCheckProof.SLang.series_step_4.h1.gneg hc_x0 hc_hn hc_x2)

-- SLang.mass'_series_converges'_sub, hypothesis 1: removable
set_option maxHeartbeats 200000 in
theorem HypCheckProof.SLang.mass'_series_converges'_sub.h1.gneg : ∀ (γ : ENNReal), ¬γ ≠ ⊤ → γ ≤ 1 → ∑' (n : ℕ), (SLang.mass' (2 * n) γ - SLang.mass' (2 * n + 1) γ) ≠ ⊤ := by
  (intros; simp_all; done)
theorem HypCheckProof.SLang.mass'_series_converges'_sub.h1 : ∀ γ ≤ 1, ∑' (n : ℕ), (SLang.mass' (2 * n) γ - SLang.mass' (2 * n + 1) γ) ≠ ⊤ := by
  intro hc_x0 hc_x2
  exact Classical.byCases (fun hc_h => @SLang.mass'_series_converges'_sub hc_x0 hc_h hc_x2) (fun hc_hn => @HypCheckProof.SLang.mass'_series_converges'_sub.h1.gneg hc_x0 hc_hn hc_x2)

-- SLang.BernoulliSample_apply_true, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliSample_apply_true.h2 : ¬∀ (num : ℕ) (den : ℕ+), num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- ENNReal.ofEReal_le_mono, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofEReal_le_mono.h2 : ¬∀ {w z : EReal}, ENNReal.ofEReal w ≤ ENNReal.ofEReal z := fun hc_h => absurd (@hc_h (⊤) (0)) (by
  decide +kernel)

-- ENNReal.eexp_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.eexp_injective.h2 : ¬∀ {w z : EReal}, w = z := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- SLang.double_large_enough, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.double_large_enough.h2 : ¬∀ (n : ℕ+) (x : ℕ), x < 2 ^ Nat.log 2 ↑(2 * n) := fun hc_h => absurd (@hc_h (1) (2)) (by
  decide +kernel)

-- SLang.UniformPowerOfTwoSample_apply', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.UniformPowerOfTwoSample_apply'.h2 : ¬∀ (n : ℕ+) (x : ℕ), SLang.UniformPowerOfTwoSample n x = 0 := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- SLang.BernoulliSample_apply_false, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.BernoulliSample_apply_false.h2 : ¬∀ (num : ℕ) (den : ℕ+), num ≤ ↑den := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- SLang.dropLast_append_getLastI, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.dropLast_append_getLastI.h1 : ¬∀ (L : List ℤ), L.dropLast ++ [L.getLastI] = L := fun hc_h => absurd (@hc_h ([])) (by
  decide +kernel)

-- SLang.cons_headI_tail, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.cons_headI_tail.h1 : ¬∀ {L : List ℤ}, L.headI :: L.tail = L := fun hc_h => absurd (@hc_h ([])) (by
  decide +kernel)

-- SLang.norm_simplify, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.norm_simplify.h1 : ¬∀ (x : ENNReal), ↑‖x.toReal‖₊ = x := fun hc_h => absurd (@hc_h (⊤)) (by
  decide +kernel)

-- ENNReal.toEReal_ofENNReal_nonneg, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toEReal_ofENNReal_nonneg.h1 : ¬∀ {w : EReal}, ↑(ENNReal.ofEReal w) = w := fun hc_h => absurd (@hc_h (⊥)) (by
  decide +kernel)

-- SLang.trial_one_minus, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.trial_one_minus.h1 : ¬∀ (trial : SLang Bool), trial Bool.false = 1 - trial Bool.true := fun hc_h => absurd (@hc_h (fun (a : Bool) => 0)) (by
  simp)

-- SLang.adhoc', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SLang.adhoc'.h1 : Not
      (∀ (n : Nat),
        @Eq ENNReal
          (@HAdd.hAdd ENNReal ENNReal ENNReal (@instHAdd ENNReal ENNReal.instAdd)
            (@HSub.hSub ENNReal ENNReal ENNReal (@instHSub ENNReal ENNReal.instSub)
              (@Nat.cast ENNReal
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                n)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            (@OfNat.ofNat ENNReal (nat_lit 1) (@One.toOfNat1 ENNReal ENNReal.instOne)))
          (@HSub.hSub ENNReal ENNReal ENNReal (@instHSub ENNReal ENNReal.instSub)
            (@Nat.cast ENNReal
              (@AddMonoidWithOne.toNatCast ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
              n)
            (@OfNat.ofNat ENNReal (nat_lit 1) (@One.toOfNat1 ENNReal ENNReal.instOne)))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  simp)

