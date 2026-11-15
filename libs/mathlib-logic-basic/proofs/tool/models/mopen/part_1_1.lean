import HCImportsM

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Real.exists_lt_of_strictMono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.exists_lt_of_strictMono.h4 : ¬∀ {Γ₀ : Type} [inst : LinearOrderedCommGroupWithZero Γ₀] [h : Nontrivial Γ₀ˣ] {f : Γ₀ →*₀ NNReal} {r : ℝ},
        0 < r → ∃ (d : Γ₀ˣ), ↑(f ↑d) < r := fun hc_h => absurd (@hc_h (ℚ≥0) (NNRat.instLinearOrderedCommGroupWithZero) _ (1) ((1 : Real) : ℝ) (by
  simp)) (by
  simp)

-- Function.update_comp_eq_of_injective, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.update_comp_eq_of_injective.h7 : ¬∀ {α α' : Type} [inst : DecidableEq α] [inst_1 : DecidableEq α'] {β : Type} (g : α' → β) {f : α → α'} (i : α) (a : β),
        Function.update g (f i) a ∘ f = Function.update (g ∘ f) i a := fun hc_h => absurd (@hc_h (Bool) (ℕ) (instDecidableEqBool) (instDecidableEqNat) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : Bool → ℕ) (Bool.false) (0)) (by
  decide +kernel)

-- SetRel.comm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.comm.h4 : ¬∀ {α : Type} (R : SetRel α α) {a b : α}, (a, b) ∈ R ↔ (b, a) ∈ R := fun hc_h => absurd (@hc_h (ℕ) (({(0, 1)} : SetRel Nat Nat) : SetRel ℕ ℕ) (0) (1)) (by
  decide +kernel)

-- Equiv.Perm.exists_map_finset_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Perm.exists_map_finset_eq.h3 : Not
      (∀ {β : Type} (s t : Finset β), ∃ (σ : Equiv.Perm β), @Eq (Finset β) (@Finset.map β β (@Equiv.toEmbedding β β σ) s) t) := fun hc_h => absurd (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Finset.mk Nat
      (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@of_decide_eq_true
        (@Multiset.Nodup Nat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Multiset.nodupDecidable Nat instDecidableEqNat
          (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Multiset.Nodup Nat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (@Multiset.nodupDecidable Nat instDecidableEqNat
                (@Singleton.singleton Nat (Multiset Nat) (@Multiset.instSingleton Nat)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  (simp <;> decide))

-- Real.HolderTriple.all_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.all_pos.h3 : ¬∀ {p q r : ℝ}, 0 < p ∧ 0 < q ∧ 0 < r := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ }) ((0 : Real) : ℝ)) (by
  simp)

-- Real.HolderTriple.inv_inv_add_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.inv_inv_add_inv.h3 : ¬∀ {p q r : ℝ}, (p⁻¹ + q⁻¹)⁻¹ = r := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ((0 : Real) : ℝ) ({ cauchy := 1 : ℝ })) (by
  simp)

-- Real.HolderTriple.one_div_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.one_div_ne_zero.h3 : ¬∀ {p : ℝ} {q r : ℝ}, 1 / p ≠ 0 := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ) ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ })) (by
  simp)

-- Real.HolderTriple.inv_pos', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.inv_pos'.h3 : ¬∀ {p q : ℝ} {r : ℝ}, 0 < r⁻¹ := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ }) ((0 : Real) : ℝ)) (by
  simp)

-- Real.HolderTriple.inv_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.inv_ne_zero.h3 : ¬∀ {p : ℝ} {q r : ℝ}, p⁻¹ ≠ 0 := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ) ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ })) (by
  simp)

-- Function.Embedding.uncountable, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.uncountable.h2 : ¬∀ {α β : Type} (f : α ↪ β), Uncountable β := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ((Function.Embedding.refl Nat) : ℕ ↪ ℕ)) (by
  simp)

-- ENNReal.ofReal_le_ofReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_le_ofReal.h2 : ¬∀ {p q : ℝ}, ENNReal.ofReal p ≤ ENNReal.ofReal q := fun hc_h => absurd (@hc_h ((1 : Real) : ℝ) ((0 : Real) : ℝ)) (by
  simp)

-- Real.toNNReal_mono, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toNNReal_mono.h2 : ¬∀ {r₁ r₂ : ℝ}, r₁.toNNReal ≤ r₂.toNNReal := fun hc_h => absurd (@hc_h ((1 : Real) : ℝ) ((0 : Real) : ℝ)) (by
  simp)

-- ENNReal.ofReal_le_ofReal_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_le_ofReal_iff.h2 : ¬∀ {p q : ℝ}, ENNReal.ofReal p ≤ ENNReal.ofReal q ↔ p ≤ q := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ) ((-1 : Real) : ℝ)) (by
  simp)

-- Real.toNNReal_lt_iff_lt_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toNNReal_lt_iff_lt_coe.h2 : ¬∀ {r : ℝ} {p : NNReal}, r.toNNReal < p ↔ r < ↑p := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ) ((0 : NNReal) : NNReal)) (by
  simp)

-- ENNReal.ofReal_sub, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_sub.h2 : ¬∀ (p : ℝ) {q : ℝ}, ENNReal.ofReal (p - q) = ENNReal.ofReal p - ENNReal.ofReal q := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ) ((-1 : Real) : ℝ)) (by
  simp)

-- ENNReal.ofReal_lt_natCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_lt_natCast.h2 : ¬∀ {p : ℝ} {n : ℕ}, ENNReal.ofReal p < ↑n ↔ p < ↑n := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ) (0)) (by
  simp)

-- Real.HolderConjugate.conjugate_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderConjugate.conjugate_eq.h2 : ¬∀ {p q : ℝ}, q = p / (p - 1) := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ) ((1 : Real) : ℝ)) (by
  simp)

-- Real.HolderConjugate.inv_add_inv_ennreal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderConjugate.inv_add_inv_ennreal.h2 : ¬∀ {p q : ℝ}, (ENNReal.ofReal p)⁻¹ + (ENNReal.ofReal q)⁻¹ = 1 := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ((0 : Real) : ℝ)) (by
  simp)

-- Real.HolderConjugate.sub_one_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderConjugate.sub_one_ne_zero.h2 : ¬∀ {p : ℝ} {q : ℝ}, p - 1 ≠ 0 := fun hc_h => absurd (@hc_h ((1 : Real) : ℝ) ({ cauchy := 0 : ℝ })) (by
  simp)

-- ENNReal.toReal_ofReal_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_ofReal_mul.h2 : ¬∀ (c : ℝ) (a : ENNReal), (ENNReal.ofReal c * a).toReal = c * a.toReal := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ) ((1 : ENNReal) : ENNReal)) (by
  (simp <;> omega))

-- ENNReal.ofReal_of_nonpos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_of_nonpos.h1 : ¬∀ {p : ℝ}, ENNReal.ofReal p = 0 := fun hc_h => absurd (@hc_h ((1 : Real) : ℝ)) (by
  simp)

-- ENNReal.ofReal_eq_coe_nnreal, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_eq_coe_nnreal.h1 : ¬∀ {x : ℝ}, 0 ≤ x := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ)) (by
  simp)

-- Real.sign_of_neg, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.sign_of_neg.h1 : ¬∀ {r : ℝ}, r.sign = -1 := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ)) (by
  simp)

-- Real.coe_toNNReal, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.coe_toNNReal.h1 : ¬∀ (r : ℝ), ↑r.toNNReal = r := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ)) (by
  (simp <;> omega))

