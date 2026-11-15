import HCImportsM

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- num_smul_one_lt_den_smul_add, hypothesis 3: necessary
/- FAILED: 4:3: `simp` made no progress | 96:3: `simp` made no progress | 4:3: `simp` made no progress | 66:3: `simp` made no progress | 2:70: Invalid field `num`: The environment does not contain `Nat.num`, so it is not possible to project the field `num` from an expression
  0 + 0
of type `ℕ` | 139:3: `simp` made no progress | 2:70: Invalid field `num`: The environment does not contain `Nat.num`, so it is not possible to project the field `num` from an expression
  0 + 0
of type `ℕ` | 90:3: `simp` made no progress
set_option maxHeartbeats 6000 in
theorem HypCheckProof.num_smul_one_lt_den_smul_add.h3 : ¬∀ {M : Type} [inst : AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : One M] {u v : ℚ} {x y : M},
        u.num • 1 < u.den • x → v.num • 1 < v.den • y → (u + v).num • 1 < (u + v).den • (x + y) := fun hc_h => absurd (@hc_h (Fin 2) (Fin.addCommGroup 2) (Fin.instLinearOrder) ((Fin.instCommMonoid 2).toMulOneClass.toMulOne.toOne) (0) (0) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)
-/

-- num_smul_one_lt_den_smul_add, hypothesis 9: necessary
/- FAILED: 4:3: `simp` made no progress | 47:3: `simp` made no progress | 4:3: `simp` made no progress | 47:3: `simp` made no progress | 2:62: (deterministic) timeout at `«synthesize pending MVars»`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 60:3: `simp` made no progress | 2:62: (deterministic) timeout at `«synthesize pending MVars»`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 60:3: `simp` made no progress
set_option maxHeartbeats 6000 in
theorem HypCheckProof.num_smul_one_lt_den_smul_add.h9 : ¬∀ {M : Type} [inst : AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] [inst_3 : One M]
        {u v : ℚ} {x y : M}, v.num • 1 < v.den • y → (u + v).num • 1 < (u + v).den • (x + y) := fun hc_h => absurd (@hc_h (ℤ) (Int.instAddCommGroup) (Int.instLinearOrder) _ (Int.instRing.toAddGroupWithOne.toOne) (1) (0) (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)
-/

-- num_smul_one_lt_den_smul_add, hypothesis 10: necessary
/- FAILED: 4:3: `simp` made no progress | 47:3: `simp` made no progress | 4:3: `simp` made no progress | 47:3: `simp` made no progress | 2:63: (deterministic) timeout at `«synthesize pending MVars»`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 60:3: `simp` made no progress | 2:63: (deterministic) timeout at `«synthesize pending MVars»`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 60:3: `simp` made no progress
set_option maxHeartbeats 6000 in
theorem HypCheckProof.num_smul_one_lt_den_smul_add.h10 : ¬∀ {M : Type} [inst : AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] [inst_3 : One M]
        {u v : ℚ} {x y : M}, u.num • 1 < u.den • x → (u + v).num • 1 < (u + v).den • (x + y) := fun hc_h => absurd (@hc_h (ℤ) (Int.instAddCommGroup) (Int.instLinearOrder) _ (Int.instRing.toAddGroupWithOne.toOne) (0) (1) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)
-/

-- ENNReal.exists_le_of_sum_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_le_of_sum_le.h2 : ¬∀ {α : Type} {s : Finset α} {f g : α → ENNReal}, ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i → ∃ i ∈ s, f i ≤ g i := fun hc_h => absurd (@hc_h (ℕ) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (fun (a : ℕ) => 0) (fun (a : ℕ) => 0) (by
  rfl)) (by
  decide +kernel)

-- ENNReal.sum_lt_sum_of_nonempty, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.ENNReal.sum_lt_sum_of_nonempty.h2.inst : Not
      (@LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder))
        (∑
          i ∈
            @Finset.mk Nat
              (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
                  (@Eq.refl Bool Bool.true))),
          (fun (a : Nat) => @OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) i)
        (∑
          i ∈
            @Finset.mk Nat
              (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
                  (@Eq.refl Bool Bool.true))),
          (fun (a : Nat) => @OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) i)) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.ENNReal.sum_lt_sum_of_nonempty.h2.prem0 : ∀ (i : Nat),
      @Membership.mem Nat (Finset Nat) (@SetLike.instMembership (Finset Nat) Nat (@Finset.instSetLike Nat))
          (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
                (@Eq.refl Bool Bool.true))))
          i →
        @LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder))
          ((fun (a : Nat) => @OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) i)
          ((fun (a : Nat) => @OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) i) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.ENNReal.sum_lt_sum_of_nonempty.h2 : Not
      (∀ {α : Type} {s : Finset α} {f g : α → ENNReal},
        (∀ (i : α),
            @Membership.mem α (Finset α) (@SetLike.instMembership (Finset α) α (@Finset.instSetLike α)) s i →
              @LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder)) (f i)
                (g i)) →
          @LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder)) (∑ i ∈ s, f i)
            (∑ i ∈ s, g i)) := fun hc_h => HypCheckProof.ENNReal.sum_lt_sum_of_nonempty.h2.inst (@hc_h (Nat) (@Finset.mk Nat (@OfNat.ofNat (Multiset Nat) (nat_lit 0) (@Zero.toOfNat0 (Multiset Nat) (@Multiset.instZero Nat)))
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
          (@Eq.refl Bool Bool.true)))) (fun (a : Nat) => @OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) (fun (a : Nat) => @OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) HypCheckProof.ENNReal.sum_lt_sum_of_nonempty.h2.prem0)

-- NNReal.HolderTriple.coe_ennreal, hypothesis 3: removable
/- FAILED: 2:115: invalid coercion notation, expected type is not known | 4:30: invalid coercion notation, expected type is not known | 2:115: invalid coercion notation, expected type is not known | 4:30: invalid coercion notation, expected type is not known
set_option maxHeartbeats 1000 in
theorem HypCheckProof.NNReal.HolderTriple.coe_ennreal.h3.gneg : ∀ {p q r : NNReal}, ¬r ≠ 0 → p.HolderTriple q r → (↑p).HolderTriple ↑q ↑r := by
  (intros; grind)
theorem HypCheckProof.NNReal.HolderTriple.coe_ennreal.h3 : ∀ {p q r : NNReal}, p.HolderTriple q r → (↑p).HolderTriple ↑q ↑r := by
  intro hc_x0 hc_x1 hc_x2 hc_x4
  exact Classical.byCases (fun hc_h => @NNReal.HolderTriple.coe_ennreal hc_x0 hc_x1 hc_x2 hc_h hc_x4) (fun hc_hn => @HypCheckProof.NNReal.HolderTriple.coe_ennreal.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4)
set_option maxHeartbeats 1000 in
theorem HypCheckProof.NNReal.HolderTriple.coe_ennreal.h3.derivable : ∀ {p q r : NNReal}, p.HolderTriple q r → r ≠ 0 := by
  (intros; grind)
-/

-- ENNReal.toReal_le_of_le_ofReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_le_of_le_ofReal.h2 : ¬∀ {a : ENNReal} {b : ℝ}, a ≤ ENNReal.ofReal b → a.toReal ≤ b := fun hc_h => absurd (@hc_h ((0 : ENNReal) : ENNReal) ((-1 : Real) : ℝ) (by
  rfl)) (by
  simp)

-- ENNReal.toReal_le_of_le_ofReal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_le_of_le_ofReal.h3 : ¬∀ {a : ENNReal} {b : ℝ}, 0 ≤ b → a.toReal ≤ b := fun hc_h => absurd (@hc_h ((1 : ENNReal) : ENNReal) ((0 : Real) : ℝ) (by
  rfl)) (by
  simp)

-- ENNReal.add_le_add_iff_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.add_le_add_iff_left.h3 : ¬∀ {a b c : ENNReal}, a + b ≤ a + c ↔ b ≤ c := fun hc_h => absurd (@hc_h ((⊤ : ENNReal) : ENNReal) ((1 : ENNReal) : ENNReal) ((0 : ENNReal) : ENNReal)) (by
  simp)

-- Real.HolderTriple.one_div_nonneg', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.one_div_nonneg'.h3 : ¬∀ {p q : ℝ} {r : ℝ}, 0 ≤ 1 / r := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ }) ((-1 : Real) : ℝ)) (by
  (simp <;> omega))

-- Real.HolderTriple.inv_nonneg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.inv_nonneg.h3 : ¬∀ {p : ℝ} {q r : ℝ}, 0 ≤ p⁻¹ := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ) ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ })) (by
  simp)

-- Real.HolderTriple.right_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.right_pos.h3 : ¬∀ {p : ℝ} {q : ℝ} {r : ℝ}, 0 < q := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ((0 : Real) : ℝ) ({ cauchy := 0 : ℝ })) (by
  simp)

-- Real.HolderTriple.one_div_nonneg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.one_div_nonneg.h3 : ¬∀ {p : ℝ} {q r : ℝ}, 0 ≤ 1 / p := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ) ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ })) (by
  (simp <;> omega))

-- ENNReal.ofReal_le_of_le_toReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_le_of_le_toReal.h2 : ¬∀ {a : ℝ} {b : ENNReal}, ENNReal.ofReal a ≤ b := fun hc_h => absurd (@hc_h ((1 : Real) : ℝ) ((0 : ENNReal) : ENNReal)) (by
  simp)

-- Real.toNNReal_lt_natCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toNNReal_lt_natCast.h2 : ¬∀ {r : ℝ} {n : ℕ}, r.toNNReal < ↑n ↔ r < ↑n := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ) (0)) (by
  simp)

-- ENNReal.natCast_le_ofReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.natCast_le_ofReal.h2 : ¬∀ {n : ℕ} {p : ℝ}, ↑n ≤ ENNReal.ofReal p ↔ ↑n ≤ p := fun hc_h => absurd (@hc_h (0) ((-1 : Real) : ℝ)) (by
  simp)

-- ENNReal.lt_ofReal_iff_toReal_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.lt_ofReal_iff_toReal_lt.h2 : ¬∀ {a : ENNReal} {b : ℝ}, a < ENNReal.ofReal b ↔ a.toReal < b := fun hc_h => absurd (@hc_h ((⊤ : ENNReal) : ENNReal) ((1 : Real) : ℝ)) (by
  simp)

-- Real.toNNReal_eq_iff_eq_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toNNReal_eq_iff_eq_coe.h2 : ¬∀ {r : ℝ} {p : NNReal}, r.toNNReal = p ↔ r = ↑p := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ) ((0 : NNReal) : NNReal)) (by
  simp)

-- Real.natCast_le_toNNReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.natCast_le_toNNReal.h2 : ¬∀ {n : ℕ} {r : ℝ}, ↑n ≤ r.toNNReal ↔ ↑n ≤ r := fun hc_h => absurd (@hc_h (0) ((-1 : Real) : ℝ)) (by
  simp)

-- Real.toNNReal_le_toNNReal_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toNNReal_le_toNNReal_iff.h2 : ¬∀ {r p : ℝ}, r.toNNReal ≤ p.toNNReal ↔ r ≤ p := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ) ((-1 : Real) : ℝ)) (by
  simp)

-- ENNReal.ofReal_eq_natCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_eq_natCast.h2 : ¬∀ {r : ℝ} {n : ℕ}, ENNReal.ofReal r = ↑n ↔ r = ↑n := fun hc_h => absurd (@hc_h ((-1 : Real) : ℝ) (0)) (by
  simp)

-- Real.HolderConjugate.sub_one_mul_conj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderConjugate.sub_one_mul_conj.h2 : ¬∀ {p q : ℝ}, (p - 1) * q = p := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ((1 : Real) : ℝ)) (by
  simp)

-- Real.HolderConjugate.sub_one_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderConjugate.sub_one_pos.h2 : ¬∀ {p : ℝ} {q : ℝ}, 0 < p - 1 := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ) ({ cauchy := 0 : ℝ })) (by
  simp)

-- Real.HolderConjugate.inv_sub_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderConjugate.inv_sub_one.h2 : ¬∀ {p q : ℝ}, p⁻¹ - 1 = -q⁻¹ := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ) ((0 : Real) : ℝ)) (by
  simp)

-- Real.HolderConjugate.one_sub_inv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderConjugate.one_sub_inv.h2 : ¬∀ {p q : ℝ}, 1 - p⁻¹ = q⁻¹ := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ) ((0 : Real) : ℝ)) (by
  simp)

-- ENNReal.toReal_lt_of_lt_ofReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_lt_of_lt_ofReal.h2 : ¬∀ {a : ENNReal} {b : ℝ}, a.toReal < b := fun hc_h => absurd (@hc_h ((0 : ENNReal) : ENNReal) ((0 : Real) : ℝ)) (by
  simp)

-- Mathlib.Meta.Positivity.nnabs_pos_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Mathlib.Meta.Positivity.nnabs_pos_of_pos.h1 : ¬∀ {x : ℝ}, 0 < Real.nnabs x := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ)) (by
  simp)

-- Real.sign_mul_pos_of_ne_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.sign_mul_pos_of_ne_zero.h1 : ¬∀ (r : ℝ), 0 < r.sign * r := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ)) (by
  simp)

-- Real.sign_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.sign_of_pos.h1 : ¬∀ {r : ℝ}, r.sign = 1 := fun hc_h => absurd (@hc_h ((0 : Real) : ℝ)) (by
  simp)

