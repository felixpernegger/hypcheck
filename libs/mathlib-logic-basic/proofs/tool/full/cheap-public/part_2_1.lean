import HCImportsM

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- num_le_nat_mul_den, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.num_le_nat_mul_den.h3 : Not
      (∀ {M : Type} [inst : AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : One M]
        [inst_3 :
          @ZeroLEOneClass M
            (@NegZeroClass.toZero M
              (@SubNegZeroMonoid.toNegZeroClass M
                (@SubtractionMonoid.toSubNegZeroMonoid M
                  (@SubtractionCommMonoid.toSubtractionMonoid M (@AddCommGroup.toDivisionAddCommMonoid M inst)))))
            inst_2
            (@Preorder.toLE M
              (@PartialOrder.toPreorder M
                (@SemilatticeInf.toPartialOrder M
                  (@Lattice.toSemilatticeInf M
                    (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))))]
        [inst_4 :
          @NeZero M
            (@NegZeroClass.toZero M
              (@SubNegZeroMonoid.toNegZeroClass M
                (@SubtractionMonoid.toSubNegZeroMonoid M
                  (@SubtractionCommMonoid.toSubtractionMonoid M (@AddCommGroup.toDivisionAddCommMonoid M inst)))))
            (@OfNat.ofNat M (nat_lit 1) (@One.toOfNat1 M inst_2))]
        {num : Int} {den : Nat} {x : M},
        @LE.le M
            (@Preorder.toLE M
              (@PartialOrder.toPreorder M
                (@SemilatticeInf.toPartialOrder M
                  (@Lattice.toSemilatticeInf M (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))))
            (@HSMul.hSMul Int M M
              (@instHSMul Int M
                (@ZSMul.toSMul M (@SubNegMonoid.toZSMul M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst)))))
              num (@OfNat.ofNat M (nat_lit 1) (@One.toOfNat1 M inst_2)))
            (@HSMul.hSMul Nat M M
              (@instHSMul Nat M
                (@NSMul.toSMul M
                  (@AddMonoid.toNSMul M
                    (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst))))))
              den x) →
          ∀ {n : Int},
            @LE.le M
                (@Preorder.toLE M
                  (@PartialOrder.toPreorder M
                    (@SemilatticeInf.toPartialOrder M
                      (@Lattice.toSemilatticeInf M
                        (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))))
                x
                (@HSMul.hSMul Int M M
                  (@instHSMul Int M
                    (@ZSMul.toSMul M
                      (@SubNegMonoid.toZSMul M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst)))))
                  n (@OfNat.ofNat M (nat_lit 1) (@One.toOfNat1 M inst_2))) →
              @LE.le Int Int.instLEInt num
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) n (@Nat.cast Int instNatCastInt den))) := fun hc_h => absurd (@hc_h (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@Fin.addCommGroup (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Fin.instLinearOrder (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@MulOne.toOne (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@MulOneClass.toMulOne (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Monoid.toMulOneClass (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@CommMonoid.toMonoid (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Fin.instCommMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (by
  decide) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  decide)) (by
  decide +kernel)

-- num_le_nat_mul_den, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.num_le_nat_mul_den.h10 : Not
      (∀ {M : Type} [inst : AddCommGroup M] [inst_1 : LinearOrder M]
        [inst_2 :
          @IsOrderedAddMonoid M (@AddCommGroup.toAddCommMonoid M inst)
            (@PartialOrder.toPreorder M
              (@SemilatticeInf.toPartialOrder M
                (@Lattice.toSemilatticeInf M (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1)))))]
        [inst_3 : One M]
        [inst_4 :
          @ZeroLEOneClass M
            (@NegZeroClass.toZero M
              (@SubNegZeroMonoid.toNegZeroClass M
                (@SubtractionMonoid.toSubNegZeroMonoid M
                  (@SubtractionCommMonoid.toSubtractionMonoid M (@AddCommGroup.toDivisionAddCommMonoid M inst)))))
            inst_3
            (@Preorder.toLE M
              (@PartialOrder.toPreorder M
                (@SemilatticeInf.toPartialOrder M
                  (@Lattice.toSemilatticeInf M
                    (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))))]
        [inst_5 :
          @NeZero M
            (@NegZeroClass.toZero M
              (@SubNegZeroMonoid.toNegZeroClass M
                (@SubtractionMonoid.toSubNegZeroMonoid M
                  (@SubtractionCommMonoid.toSubtractionMonoid M (@AddCommGroup.toDivisionAddCommMonoid M inst)))))
            (@OfNat.ofNat M (nat_lit 1) (@One.toOfNat1 M inst_3))]
        {num : Int} {den : Nat} {x : M} {n : Int},
        @LE.le M
            (@Preorder.toLE M
              (@PartialOrder.toPreorder M
                (@SemilatticeInf.toPartialOrder M
                  (@Lattice.toSemilatticeInf M (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))))
            x
            (@HSMul.hSMul Int M M
              (@instHSMul Int M
                (@ZSMul.toSMul M (@SubNegMonoid.toZSMul M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst)))))
              n (@OfNat.ofNat M (nat_lit 1) (@One.toOfNat1 M inst_3))) →
          @LE.le Int Int.instLEInt num
            (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) n (@Nat.cast Int instNatCastInt den))) := fun hc_h => absurd (@hc_h (Int) (Int.instAddCommGroup) (Int.instLinearOrder) _ (@AddMonoidWithOne.toOne Int (@AddGroupWithOne.toAddMonoidWithOne Int (@Ring.toAddGroupWithOne Int Int.instRing))) _ _ (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- num_le_nat_mul_den, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.num_le_nat_mul_den.h12 : Not
      (∀ {M : Type} [inst : AddCommGroup M] [inst_1 : LinearOrder M]
        [inst_2 :
          @IsOrderedAddMonoid M (@AddCommGroup.toAddCommMonoid M inst)
            (@PartialOrder.toPreorder M
              (@SemilatticeInf.toPartialOrder M
                (@Lattice.toSemilatticeInf M (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1)))))]
        [inst_3 : One M]
        [inst_4 :
          @ZeroLEOneClass M
            (@NegZeroClass.toZero M
              (@SubNegZeroMonoid.toNegZeroClass M
                (@SubtractionMonoid.toSubNegZeroMonoid M
                  (@SubtractionCommMonoid.toSubtractionMonoid M (@AddCommGroup.toDivisionAddCommMonoid M inst)))))
            inst_3
            (@Preorder.toLE M
              (@PartialOrder.toPreorder M
                (@SemilatticeInf.toPartialOrder M
                  (@Lattice.toSemilatticeInf M
                    (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))))]
        [inst_5 :
          @NeZero M
            (@NegZeroClass.toZero M
              (@SubNegZeroMonoid.toNegZeroClass M
                (@SubtractionMonoid.toSubNegZeroMonoid M
                  (@SubtractionCommMonoid.toSubtractionMonoid M (@AddCommGroup.toDivisionAddCommMonoid M inst)))))
            (@OfNat.ofNat M (nat_lit 1) (@One.toOfNat1 M inst_3))]
        {num : Int} {den : Nat} {x : M},
        @LE.le M
            (@Preorder.toLE M
              (@PartialOrder.toPreorder M
                (@SemilatticeInf.toPartialOrder M
                  (@Lattice.toSemilatticeInf M (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))))
            (@HSMul.hSMul Int M M
              (@instHSMul Int M
                (@ZSMul.toSMul M (@SubNegMonoid.toZSMul M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst)))))
              num (@OfNat.ofNat M (nat_lit 1) (@One.toOfNat1 M inst_3)))
            (@HSMul.hSMul Nat M M
              (@instHSMul Nat M
                (@NSMul.toSMul M
                  (@AddMonoid.toNSMul M
                    (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst))))))
              den x) →
          ∀ {n : Int},
            @LE.le Int Int.instLEInt num
              (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) n (@Nat.cast Int instNatCastInt den))) := fun hc_h => absurd (@hc_h (Int) (Int.instAddCommGroup) (Int.instLinearOrder) _ (@AddMonoidWithOne.toOne Int (@AddGroupWithOne.toAddMonoidWithOne Int (@Ring.toAddGroupWithOne Int Int.instRing))) _ _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (by
  decide) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) (by
  decide +kernel)

-- Or.imp3, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Or.imp3.h6 : ¬∀ {a b d e c f : Prop}, (b → e) → (c → f) → a ∨ b ∨ c → d ∨ e ∨ f := fun hc_h => absurd (@hc_h (True) (False) (False) (False) (False) (False) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Or.imp3, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Or.imp3.h7 : ¬∀ {a b d e c f : Prop}, (a → d) → (c → f) → a ∨ b ∨ c → d ∨ e ∨ f := fun hc_h => absurd (@hc_h (False) (True) (False) (False) (False) (False) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Or.imp3, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Or.imp3.h8 : ¬∀ {a b d e c f : Prop}, (a → d) → (b → e) → a ∨ b ∨ c → d ∨ e ∨ f := fun hc_h => absurd (@hc_h (False) (False) (False) (False) (True) (False) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Or.imp3, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Or.imp3.h9 : ¬∀ {a b d e c f : Prop}, (a → d) → (b → e) → (c → f) → d ∨ e ∨ f := fun hc_h => absurd (@hc_h (False) (False) (False) (False) (False) (False) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

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

-- Set.Pairwise.forall₂, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Pairwise.forall₂.h3 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α}, s.Pairwise r → ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ s → r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ({n : ℕ | n = 0}) (by
  simp) (0) (by
  decide) (0) (by
  decide)) (by
  decide +kernel)

-- Set.Pairwise.forall₂, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Pairwise.forall₂.h4 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α} [inst : Std.Refl r] ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ s → r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ({n : ℕ | n % 2 = 0}) _ (2) (by
  decide) (0) (by
  decide)) (by
  decide +kernel)

-- Set.Pairwise.forall₂, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Pairwise.forall₂.h6 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α} [inst : Std.Refl r], s.Pairwise r → ∀ ⦃a b : α⦄, b ∈ s → r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ({n : ℕ | n = 0}) _ (by
  simp) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Set.Pairwise.forall₂, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Pairwise.forall₂.h8 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α} [inst : Std.Refl r], s.Pairwise r → ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) ({n : ℕ | n = 0}) _ (by
  simp) (0) (by
  decide) (1)) (by
  decide +kernel)

-- Set.Infinite.image2_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.image2_right.h7 : ¬∀ {α β γ : Type} {f : α → β → γ} {s : Set α} {t : Set β} {a : α},
        a ∈ s → Set.InjOn (f a) t → (Set.image2 f s t).Infinite := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (0) (by
  decide) (by
  simp)) (by
  simp)

-- Archimedean.embedReal_apply, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Archimedean.embedReal_apply.h6 : Not
      (∀ {M : Type} [inst : AddCommGroup M] [inst_1 : LinearOrder M]
        [inst_2 :
          @IsOrderedAddMonoid M (@AddCommGroup.toAddCommMonoid M inst)
            (@PartialOrder.toPreorder M
              (@SemilatticeInf.toPartialOrder M
                (@Lattice.toSemilatticeInf M (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1)))))]
        [inst_3 : One M]
        [inst_4 :
          @ZeroLEOneClass M
            (@NegZeroClass.toZero M
              (@SubNegZeroMonoid.toNegZeroClass M
                (@SubtractionMonoid.toSubNegZeroMonoid M
                  (@SubtractionCommMonoid.toSubtractionMonoid M (@AddCommGroup.toDivisionAddCommMonoid M inst)))))
            inst_3
            (@Preorder.toLE M
              (@PartialOrder.toPreorder M
                (@SemilatticeInf.toPartialOrder M
                  (@Lattice.toSemilatticeInf M
                    (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))))]
        [inst_5 :
          @Archimedean M (@AddCommGroup.toAddCommMonoid M inst)
            (@SemilatticeInf.toPartialOrder M
              (@Lattice.toSemilatticeInf M (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))]
        (a : M),
        @NeZero M
          (@NegZeroClass.toZero M
            (@SubNegZeroMonoid.toNegZeroClass M
              (@SubtractionMonoid.toSubNegZeroMonoid M
                (@SubtractionCommMonoid.toSubtractionMonoid M (@AddCommGroup.toDivisionAddCommMonoid M inst)))))
          (@OfNat.ofNat M (nat_lit 1) (@One.toOfNat1 M inst_3))) := fun hc_h => absurd (@hc_h (Unit) (PUnit.addCommGroup) (PUnit.instLinearOrder) (@IsOrderedAddMonoid.mk (Unit) (@AddCommGroup.toAddCommMonoid Unit PUnit.addCommGroup) (@PartialOrder.toPreorder Unit
      (@SemilatticeInf.toPartialOrder Unit
        (@Lattice.toSemilatticeInf Unit
          (@DistribLattice.toLattice Unit (@instDistribLatticeOfLinearOrder Unit PUnit.instLinearOrder))))) (by (try dsimp only);   decide) (by (try dsimp only);   decide)) (PUnit.instOne_mathlib) _ (@Archimedean.mk (Unit) (@AddCommGroup.toAddCommMonoid Unit PUnit.addCommGroup) (@SemilatticeInf.toPartialOrder Unit
      (@Lattice.toSemilatticeInf Unit
        (@DistribLattice.toLattice Unit (@instDistribLatticeOfLinearOrder Unit PUnit.instLinearOrder)))) (by (try dsimp only);   (intros; simp_all; done))) (PUnit.unit)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.Injective.beq_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.beq_eq.h3 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : BEq β] [inst_2 : LawfulBEq β] {f : α → β},
        Function.Injective f → ∀ {a b : α}, (f a == f b) = (a == b) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (⟨fun _ _ => true⟩ : BEq Bool) (instBEqOfDecidableEq) _ (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) (Bool.false) (Bool.true)) (by
  decide +kernel)

-- Function.Injective.beq_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.beq_eq.h7 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : LawfulBEq α] [inst_2 : BEq β] [inst_3 : LawfulBEq β] {f : α → β} {a b : α},
        (f a == f b) = (a == b) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instBEqOfDecidableEq) _ (instBEqOfDecidableEq) _ (fun _ => 0 : ℕ → ℕ) (0) (1)) (by
  decide +kernel)

-- Function.injective_of_isPartialInv_right, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Function.injective_of_isPartialInv_right.h4.inst : ¬Bool.false = Bool.true := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Function.injective_of_isPartialInv_right.h4.prem0 : 0 ∈ (fun (a : Bool) => Option.some 0) Bool.false := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Function.injective_of_isPartialInv_right.h4.prem1 : 0 ∈ (fun (a : Bool) => Option.some 0) Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Function.injective_of_isPartialInv_right.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → Option α} (x y : β), ∀ b ∈ g x, b ∈ g y → x = y := fun hc_h => HypCheckProof.Function.injective_of_isPartialInv_right.h4.inst (@hc_h (ℕ) (Bool) (fun (n : ℕ) => n % 2 == 0) (fun (a : Bool) => Option.some 0) (Bool.false) (Bool.true) (0) HypCheckProof.Function.injective_of_isPartialInv_right.h4.prem0 HypCheckProof.Function.injective_of_isPartialInv_right.h4.prem1)

-- Archimedean.embedReal_one, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Archimedean.embedReal_one.h6 : Not
      (∀ {M : Type} [inst : AddCommGroup M] [inst_1 : LinearOrder M]
        [inst_2 :
          @IsOrderedAddMonoid M (@AddCommGroup.toAddCommMonoid M inst)
            (@PartialOrder.toPreorder M
              (@SemilatticeInf.toPartialOrder M
                (@Lattice.toSemilatticeInf M (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1)))))]
        [inst_3 : One M]
        [inst_4 :
          @ZeroLEOneClass M
            (@NegZeroClass.toZero M
              (@SubNegZeroMonoid.toNegZeroClass M
                (@SubtractionMonoid.toSubNegZeroMonoid M
                  (@SubtractionCommMonoid.toSubtractionMonoid M (@AddCommGroup.toDivisionAddCommMonoid M inst)))))
            inst_3
            (@Preorder.toLE M
              (@PartialOrder.toPreorder M
                (@SemilatticeInf.toPartialOrder M
                  (@Lattice.toSemilatticeInf M
                    (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))))]
        [inst_5 :
          @Archimedean M (@AddCommGroup.toAddCommMonoid M inst)
            (@SemilatticeInf.toPartialOrder M
              (@Lattice.toSemilatticeInf M (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))],
        @NeZero M
          (@NegZeroClass.toZero M
            (@SubNegZeroMonoid.toNegZeroClass M
              (@SubtractionMonoid.toSubNegZeroMonoid M
                (@SubtractionCommMonoid.toSubtractionMonoid M (@AddCommGroup.toDivisionAddCommMonoid M inst)))))
          (@OfNat.ofNat M (nat_lit 1) (@One.toOfNat1 M inst_3))) := fun hc_h => absurd (@hc_h (Unit) (PUnit.addCommGroup) (PUnit.instLinearOrder) (@IsOrderedAddMonoid.mk (Unit) (@AddCommGroup.toAddCommMonoid Unit PUnit.addCommGroup) (@PartialOrder.toPreorder Unit
      (@SemilatticeInf.toPartialOrder Unit
        (@Lattice.toSemilatticeInf Unit
          (@DistribLattice.toLattice Unit (@instDistribLatticeOfLinearOrder Unit PUnit.instLinearOrder))))) (by (try dsimp only);   decide) (by (try dsimp only);   decide)) (PUnit.instOne_mathlib) _ (@Archimedean.mk (Unit) (@AddCommGroup.toAddCommMonoid Unit PUnit.addCommGroup) (@SemilatticeInf.toPartialOrder Unit
      (@Lattice.toSemilatticeInf Unit
        (@DistribLattice.toLattice Unit (@instDistribLatticeOfLinearOrder Unit PUnit.instLinearOrder)))) (by (try dsimp only);   (intros; simp_all; done)))) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Archimedean.embedReal_injective, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Archimedean.embedReal_injective.h6 : Not
      (∀ (M : Type) [inst : AddCommGroup M] [inst_1 : LinearOrder M]
        [inst_2 :
          @IsOrderedAddMonoid M (@AddCommGroup.toAddCommMonoid M inst)
            (@PartialOrder.toPreorder M
              (@SemilatticeInf.toPartialOrder M
                (@Lattice.toSemilatticeInf M (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1)))))]
        [inst_3 : One M]
        [inst_4 :
          @ZeroLEOneClass M
            (@NegZeroClass.toZero M
              (@SubNegZeroMonoid.toNegZeroClass M
                (@SubtractionMonoid.toSubNegZeroMonoid M
                  (@SubtractionCommMonoid.toSubtractionMonoid M (@AddCommGroup.toDivisionAddCommMonoid M inst)))))
            inst_3
            (@Preorder.toLE M
              (@PartialOrder.toPreorder M
                (@SemilatticeInf.toPartialOrder M
                  (@Lattice.toSemilatticeInf M
                    (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))))]
        [inst_5 :
          @Archimedean M (@AddCommGroup.toAddCommMonoid M inst)
            (@SemilatticeInf.toPartialOrder M
              (@Lattice.toSemilatticeInf M (@DistribLattice.toLattice M (@instDistribLatticeOfLinearOrder M inst_1))))],
        @NeZero M
          (@NegZeroClass.toZero M
            (@SubNegZeroMonoid.toNegZeroClass M
              (@SubtractionMonoid.toSubNegZeroMonoid M
                (@SubtractionCommMonoid.toSubtractionMonoid M (@AddCommGroup.toDivisionAddCommMonoid M inst)))))
          (@OfNat.ofNat M (nat_lit 1) (@One.toOfNat1 M inst_3))) := fun hc_h => absurd (@hc_h (Unit) (PUnit.addCommGroup) (PUnit.instLinearOrder) (@IsOrderedAddMonoid.mk (Unit) (@AddCommGroup.toAddCommMonoid Unit PUnit.addCommGroup) (@PartialOrder.toPreorder Unit
      (@SemilatticeInf.toPartialOrder Unit
        (@Lattice.toSemilatticeInf Unit
          (@DistribLattice.toLattice Unit (@instDistribLatticeOfLinearOrder Unit PUnit.instLinearOrder))))) (by (try dsimp only);   decide) (by (try dsimp only);   decide)) (PUnit.instOne_mathlib) _ (@Archimedean.mk (Unit) (@AddCommGroup.toAddCommMonoid Unit PUnit.addCommGroup) (@SemilatticeInf.toPartialOrder Unit
      (@Lattice.toSemilatticeInf Unit
        (@DistribLattice.toLattice Unit (@instDistribLatticeOfLinearOrder Unit PUnit.instLinearOrder)))) (by (try dsimp only);   (intros; simp_all; done)))) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.le_iInf_mul_iInf, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_iInf_mul_iInf.h7 : ¬∀ {ι κ : Type} {f : ι → ENNReal} {a : ENNReal} {g : κ → ENNReal},
        (∃ (i : ι), f i ≠ ⊤) → (∃ (j : κ), g j ≠ ⊤) → a ≤ (⨅ (i : ι), f i) * ⨅ (j : κ), g j := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => 0) (1) (fun (a : ℕ) => 0) (by
  simp) (by
  simp)) (by
  simp)

-- ENNReal.mem_Ioo_self_sub_add, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mem_Ioo_self_sub_add.h4 : ¬∀ {x ε₁ ε₂ : ENNReal}, x ≠ ⊤ → ε₁ ≠ 0 → ε₂ ≠ 0 → x ∈ Set.Ioo (x - ε₁) (x + ε₂) := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide) (by
  simp) (by
  simp)) (by
  simp)

-- ENNReal.mem_Ioo_self_sub_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mem_Ioo_self_sub_add.h5 : ¬∀ {x ε₁ ε₂ : ENNReal}, x ≠ ⊤ → x ≠ 0 → ε₂ ≠ 0 → x ∈ Set.Ioo (x - ε₁) (x + ε₂) := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide) (by
  simp) (by
  simp)) (by
  norm_num)

-- ENNReal.mem_Ioo_self_sub_add, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mem_Ioo_self_sub_add.h6 : ¬∀ {x ε₁ ε₂ : ENNReal}, x ≠ ⊤ → x ≠ 0 → ε₁ ≠ 0 → x ∈ Set.Ioo (x - ε₁) (x + ε₂) := fun hc_h => absurd (@hc_h (1) (1) (0) (by
  decide) (by
  simp) (by
  simp)) (by
  simp)

-- ENNReal.add_lt_add_of_lt_of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.add_lt_add_of_lt_of_le.h5 : ¬∀ {a b c d : ENNReal}, c ≠ ⊤ → c ≤ d → a + c < b + d := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (by
  decide) (by
  rfl)) (by
  simp)

-- Function.Surjective.of_comp_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.of_comp_left.h5 : ¬∀ {α β γ : Type} {f : α → β} {g : γ → α}, Function.Injective f → Function.Surjective g := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool) (fun b => if b then 1 else 0 : Bool → ℕ) (fun _ => true : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- ENNReal.sub_right_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_right_inj.h4 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → c ≤ a → (a - b = a - c ↔ b = c) := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide) (by
  rfl)) (by
  simp)

-- ENNReal.sub_right_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_right_inj.h5 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → b ≤ a → (a - b = a - c ↔ b = c) := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide) (by
  rfl)) (by
  simp)

-- ENNReal.toReal_le_add_of_top_imp_top, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_le_add_of_top_imp_top.h3 : ¬∀ {a b c : ENNReal}, (b = ⊤ → a = ⊤) → (c = ⊤ → a = ⊤) → a.toReal ≤ b.toReal + c.toReal := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide) (by
  decide)) (by
  simp)

-- ENNReal.mul_lt_mul_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_lt_mul_right.h3 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → b < c → a * b < a * c := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide) (by
  simp)) (by
  simp)

-- ENNReal.mul_lt_mul_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_lt_mul_right.h5 : ¬∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * b < a * c := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  simp) (by
  decide)) (by
  simp)

-- ENNReal.le_mul_of_forall_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_mul_of_forall_lt.h5 : ¬∀ {a b c : ENNReal}, a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ 0 → c ≤ a * b := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  simp) (by
  decide)) (by
  simp)

-- PartialEquiv.eq_symm_apply, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.eq_symm_apply.h5 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) {x : α} {y : β},
        @Membership.mem β (Set β) (@Set.instMembership β) (@PartialEquiv.target α β e) y →
          Iff (@Eq α x (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e) y)) (@Eq β (@PartialEquiv.toFun α β e x) y)) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool (fun (x : Bool) => Bool.true) (fun (x : Bool) => Bool.true)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            @Set.decidableOfPred Bool Bool.true (fun (b : Bool) => @Eq Bool b Bool.true)
              (instDecidableEqBool Bool.true Bool.true))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  @Set.decidableOfPred Bool Bool.true (fun (b : Bool) => @Eq Bool b Bool.true)
                    (instDecidableEqBool Bool.true Bool.true)))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            @Set.decidableOfPred Bool Bool.true (fun (b : Bool) => @Eq Bool b Bool.true)
              (instDecidableEqBool Bool.true Bool.true))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  @Set.decidableOfPred Bool Bool.true (fun (b : Bool) => @Eq Bool b Bool.true)
                    (instDecidableEqBool Bool.true Bool.true)))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool Bool.true x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool Bool.true x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool Bool.true a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            instDecidableEqBool Bool.true a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool Bool.true x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool Bool.true x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool Bool.true a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  instDecidableEqBool Bool.true a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool Bool.true x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool Bool.true x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool Bool.true a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            instDecidableEqBool Bool.true a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool Bool.true x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool Bool.true x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool Bool.true a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  instDecidableEqBool Bool.true a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (Bool.false) (Bool.true) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- PartialEquiv.eq_symm_apply, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.eq_symm_apply.h6 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) {x : α} {y : β},
        @Membership.mem α (Set α) (@Set.instMembership α) (@PartialEquiv.source α β e) x →
          Iff (@Eq α x (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e) y)) (@Eq β (@PartialEquiv.toFun α β e x) y)) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not (fun (x : Bool) => Bool.true)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                  (instDecidableEqBool a.not Bool.false))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                        (instDecidableEqBool a.not Bool.false))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            @Set.decidableOfPred Bool Bool.true (fun (b : Bool) => @Eq Bool b Bool.true)
              (instDecidableEqBool Bool.true Bool.true))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  @Set.decidableOfPred Bool Bool.true (fun (b : Bool) => @Eq Bool b Bool.true)
                    (instDecidableEqBool Bool.true Bool.true)))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool Bool.true x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool Bool.true x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool Bool.true a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            instDecidableEqBool Bool.true a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool Bool.true x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool Bool.true x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool Bool.true a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  instDecidableEqBool Bool.true a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool Bool.true.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool Bool.true.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool Bool.true.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            instDecidableEqBool Bool.true.not a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool Bool.true.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool Bool.true.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool Bool.true.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  instDecidableEqBool Bool.true.not a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (Bool.true) (Bool.true) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- SetRel.exists_eq_singleton_of_prod_subset_id, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.exists_eq_singleton_of_prod_subset_id.h3 : ¬∀ {α : Type} {s t : Set α}, t.Nonempty → s ×ˢ t ⊆ SetRel.id → ∃ (x : α), s = {x} ∧ t = {x} := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp) (by
  simp)) (by
  simp)

-- SetRel.exists_eq_singleton_of_prod_subset_id, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.exists_eq_singleton_of_prod_subset_id.h4 : ¬∀ {α : Type} {s t : Set α}, s.Nonempty → s ×ˢ t ⊆ SetRel.id → ∃ (x : α), s = {x} ∧ t = {x} := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (by
  simp)) (by
  simp)

-- SetRel.exists_eq_singleton_of_prod_subset_id, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.exists_eq_singleton_of_prod_subset_id.h5 : ¬∀ {α : Type} {s t : Set α}, s.Nonempty → t.Nonempty → ∃ (x : α), s = {x} ∧ t = {x} := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (by
  simp) (by
  simp)) (by
  simp)

-- Equiv.swap_bijOn_exchange, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.swap_bijOn_exchange.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a b : α} {s : Set α},
        b ∉ s → Set.BijOn (⇑(Equiv.swap a b)) s (Insert.insert b (s \ {a})) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (0) ({x : ℕ | False}) (by
  decide)) (by
  simp)

-- SetRel.IsCover.mono_entourage, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.IsCover.mono_entourage.h6 : ¬∀ {X : Type} {U V : SetRel X X} {s N : Set X}, U ⊆ V → V.IsCover s N := fun hc_h => absurd (@hc_h (ℕ) (∅) (∅) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  rfl)) (by
  simp)

-- Relation.TransGen.tail', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.TransGen.tail'.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, Relation.ReflTransGen r a b → Relation.TransGen r a c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) (0) (by
  rfl)) (by
  nofun)

-- Relation.TransGen.trans_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.TransGen.trans_right.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, Relation.ReflTransGen r a b → Relation.TransGen r a c := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) (0) (by
  rfl)) (by
  nofun)

-- Equiv.image_swap_of_mem_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.image_swap_of_mem_of_notMem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {s : Set α} {i j : α}, j ∉ s → ⇑(Equiv.swap i j) '' s = Insert.insert j s \ {i} := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ({x : ℕ | False}) (0) (1) (by
  decide)) (by
  simp)

-- Set.BijOn.toPartialEquiv_symm_apply, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.toPartialEquiv_symm_apply.h6 : ¬∀ {α β : Type} [inst : Nonempty α] (f : α → β) (s : Set α) (t : Set β), Set.BijOn f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _ (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- Set.BijOn.toPartialEquiv_source, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.toPartialEquiv_source.h6 : ¬∀ {α β : Type} [inst : Nonempty α] (f : α → β) (s : Set α) (t : Set β), Set.BijOn f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _ (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- Relation.TransGen.head, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.TransGen.head.h6.inst : ¬Relation.TransGen (fun (a b : ℕ) => a < b) 0 0 := by
  nofun
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.TransGen.head.h6.prem0 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Relation.TransGen.head.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a b c : α}, r a b → Relation.TransGen r a c := fun hc_h => HypCheckProof.Relation.TransGen.head.h6.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (0) (1) (0) HypCheckProof.Relation.TransGen.head.h6.prem0)

-- Set.BijOn.toPartialEquiv_target, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.toPartialEquiv_target.h6 : ¬∀ {α β : Type} [inst : Nonempty α] (f : α → β) (s : Set α) (t : Set β), Set.BijOn f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _ (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- PEquiv.single_trans_single_of_ne, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PEquiv.single_trans_single_of_ne.h8 : ¬∀ {α β γ : Type} [inst : DecidableEq α] [inst_1 : DecidableEq β] [inst_2 : DecidableEq γ] {b₁ b₂ : β} (a : α) (c : γ),
        (PEquiv.single a b₁).trans (PEquiv.single b₂ c) = ⊥ := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (instDecidableEqBool) (instDecidableEqNat) (instDecidableEqNat) (0) (0) (Bool.false) (0)) (by
  decide +kernel)

-- Pairwise.eq, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Pairwise.eq.h4.inst : ¬1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Pairwise.eq.h4.prem0 : ¬(fun (a b : ℕ) => a < b) 1 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Pairwise.eq.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, ¬r a b → a = b := fun hc_h => HypCheckProof.Pairwise.eq.h4.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (1) (0) HypCheckProof.Pairwise.eq.h4.prem0)

-- Pairwise.eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Pairwise.eq.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, Pairwise r → a = b := fun hc_h => absurd (@hc_h (Bool) (fun a b => a ≠ b : Bool → Bool → Prop) (Bool.false) (Bool.true) (by
  simp)) (by
  decide +kernel)

-- Function.Injective.surjective_comp_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.surjective_comp_right.h5 : ¬∀ {α β γ : Type} {f : α → β} [inst : Nonempty γ], Function.Surjective fun (g : β → γ) => g ∘ f := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool) (fun _ => true : Bool → Bool) _) (by
  decide +kernel)

-- ENNReal.div_le_div, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_le_div.h4 : ¬∀ {a b c d : ENNReal}, d ≤ c → a / c ≤ b / d := fun hc_h => absurd (@hc_h (1) (0) (0) (0) (by
  rfl)) (by
  simp)

-- SetRel.isSeparated_insert_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.isSeparated_insert_of_notMem.h5 : ¬∀ {X : Type} {R : SetRel X X} {s : Set X} {x : X} [inst : R.IsSymm],
        R.IsSeparated (Insert.insert x s) ↔ R.IsSeparated s ∧ ∀ y ∈ s, (x, y) ∉ R := fun hc_h => absurd (@hc_h (ℕ) (⊤) ({n : ℕ | n = 0}) (0) _) (by
  simp)

-- Function.LeftInverse.rightInverse_of_surjective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.rightInverse_of_surjective.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α}, Function.Surjective g → Function.RightInverse f g := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ => true : Bool → Bool) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- ne_of_eq_of_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ne_of_eq_of_ne.h4 : ¬∀ {α : Type} {a b c : α}, b ≠ c → a ≠ c := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- ne_of_eq_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ne_of_eq_of_ne.h5 : ¬∀ {α : Type} {a b c : α}, a = b → a ≠ c := fun hc_h => absurd (@hc_h (ℕ) _ (0) (0) rfl) (by
  decide +kernel)

-- Ne.trans_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ne.trans_eq.h4 : ¬∀ {α : Type} {a b c : α}, b = c → a ≠ c := fun hc_h => absurd (@hc_h (ℕ) (0) _ (0) rfl) (by
  decide +kernel)

-- Ne.trans_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ne.trans_eq.h5 : ¬∀ {α : Type} {a b c : α}, a ≠ b → a ≠ c := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- imp_congr_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.imp_congr_eq.h4 : ¬∀ {a b c d : Prop}, b = d → (a → b) = (c → d) := fun hc_h => absurd (@hc_h (True) _ (False) (False) rfl) (by
  decide +kernel)

-- imp_congr_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.imp_congr_eq.h5 : ¬∀ {a b c d : Prop}, a = c → (a → b) = (c → d) := fun hc_h => absurd (@hc_h _ (True) (True) (False) rfl) (by
  decide +kernel)

-- not_beq_of_ne, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_beq_of_ne.h2 : ¬∀ {α : Type} [inst : BEq α] {a b : α}, a ≠ b → ¬(a == b) = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) (0) (1) (by
  decide)) (by
  decide +kernel)

-- not_beq_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_beq_of_ne.h5 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {a b : α}, ¬(a == b) = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ (0) (0)) (by
  decide +kernel)

-- Iff.iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iff.iff.h4 : ¬∀ {p₁ p₂ q₁ q₂ : Prop}, (q₁ ↔ q₂) → ((p₁ ↔ q₁) ↔ (p₂ ↔ q₂)) := fun hc_h => absurd (@hc_h (True) (False) (True) (True) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Iff.iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iff.iff.h5 : ¬∀ {p₁ p₂ q₁ q₂ : Prop}, (p₁ ↔ p₂) → ((p₁ ↔ q₁) ↔ (p₂ ↔ q₂)) := fun hc_h => absurd (@hc_h (True) (True) (True) (False) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Iff.or, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iff.or.h4 : ¬∀ {a c b d : Prop}, (b ↔ d) → (a ∨ b ↔ c ∨ d) := fun hc_h => absurd (@hc_h (True) (False) (False) (False) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Iff.or, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iff.or.h5 : ¬∀ {a c b d : Prop}, (a ↔ c) → (a ∨ b ↔ c ∨ d) := fun hc_h => absurd (@hc_h (False) (False) (True) (False) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- BEx.imp_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.BEx.imp_left.h4 : ¬∀ {α : Type} {r p q : α → Prop}, (∃ (x : α) (_ : p x), r x) → ∃ (x : α) (_ : q x), r x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (by
  simp)) (by
  simp)

-- BEx.imp_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.BEx.imp_left.h5 : ¬∀ {α : Type} {r p q : α → Prop}, (∀ (x : α), p x → q x) → ∃ (x : α) (_ : q x), r x := fun hc_h => absurd (@hc_h (ℕ) (fun _ => False : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (by
  simp)) (by
  simp)

-- Function.invFun_eq, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Function.invFun_eq.h2.der.{u_1, u_2} : ∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {b : β}, (∃ (a : α), @Eq β (f a) b) → Nonempty α := by
  (intros; tauto)
theorem HypCheckProof.Function.invFun_eq.h2.{u_1, u_2} : ∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {b : β} (h : ∃ (a : α), @Eq β (f a) b),
      @Eq β (f (@Function.invFun α β (@HypCheckProof.Function.invFun_eq.h2.der α β f b h) f b)) b := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @Function.invFun_eq hc_x0 hc_x1 (@HypCheckProof.Function.invFun_eq.h2.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4) hc_x2 hc_x3 hc_x4

-- Function.invFun_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.invFun_eq.h5 : ¬∀ {α β : Type} [inst : Nonempty α] {f : α → β} {b : β}, f (Function.invFun f b) = b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _ (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Function.Injective.swap_apply, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.swap_apply.h5 : ¬∀ {α β : Type} [inst : DecidableEq α] [inst_1 : DecidableEq β] {f : α → β} (x y z : α),
        (Equiv.swap (f x) (f y)) (f z) = f ((Equiv.swap x y) z) := fun hc_h => absurd (@hc_h (ℕ) (Bool) (instDecidableEqNat) (instDecidableEqBool) (fun n => n % 2 == 0 : ℕ → Bool) (0) (1) (2)) (by
  decide +kernel)

-- Function.update_comp_eq_of_forall_ne, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.update_comp_eq_of_forall_ne.h8 : ¬∀ {α' : Type} [inst : DecidableEq α'] {α β : Type} (g : α' → β) {f : α → α'} {i : α'} (a : β),
        Function.update g i a ∘ f = g ∘ f := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (Bool) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (0) (0)) (by
  decide +kernel)

-- ENNReal.mul_lt_mul_iff_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_lt_mul_iff_left.h3 : ¬∀ {a b c : ENNReal}, c ≠ ⊤ → (a * c < b * c ↔ a < b) := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  simp)

-- ENNReal.div_lt_div_iff_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_lt_div_iff_right.h3 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → (a / b < a / c ↔ c < b) := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  simp)

-- ENNReal.div_le_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_le_iff.h3 : ¬∀ {x y z : ENNReal}, y ≠ ⊤ → (x / y ≤ z ↔ x ≤ z * y) := fun hc_h => absurd (@hc_h (1) (0) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.mul_div_mul_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_div_mul_right.h3 : ¬∀ {c : ENNReal} (a b : ENNReal), c ≠ ⊤ → a * c / (b * c) = a / b := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  norm_num)

-- ENNReal.le_div_iff_mul_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_div_iff_mul_le.h3 : ¬∀ {a b c : ENNReal}, b ≠ ⊤ ∨ c ≠ ⊤ → (a ≤ c / b ↔ a * b ≤ c) := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.zpow_le_of_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.zpow_le_of_le.h1 : ¬∀ {x : ENNReal} {a b : ℤ}, a ≤ b → x ^ a ≤ x ^ b := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.zpow_le_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.zpow_le_of_le.h4 : ¬∀ {x : ENNReal}, 1 ≤ x → ∀ {a b : ℤ}, x ^ a ≤ x ^ b := fun hc_h => absurd (@hc_h (2) (by
  simp) (1) (0)) (by
  simp)

-- ENNReal.div_lt_div_iff_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_lt_div_iff_left.h3 : ¬∀ {a b c : ENNReal}, c ≠ ⊤ → (a / c < b / c ↔ a < b) := fun hc_h => absurd (@hc_h (1) (2) (0) (by
  decide)) (by
  simp)

-- ENNReal.div_le_iff', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_le_iff'.h3 : ¬∀ {x y z : ENNReal}, y ≠ ⊤ → (x / y ≤ z ↔ x ≤ y * z) := fun hc_h => absurd (@hc_h (1) (0) (⊤) (by
  decide)) (by
  simp)

-- Function.rightInverse_invFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.rightInverse_invFun.h4 : ¬∀ {α β : Type} [inst : Nonempty α] {f : α → β}, Function.RightInverse (Function.invFun f) f := fun hc_h => absurd (@hc_h (ℕ) (Bool) _ (fun _ => true : ℕ → Bool)) (by
  decide +kernel)

-- finAddFlip_apply_mk_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finAddFlip_apply_mk_right.h3 : ¬∀ {m n k : ℕ}, k < m + n → m ≤ k := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- finAddFlip_apply_mk_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finAddFlip_apply_mk_right.h4 : ¬∀ {m n k : ℕ}, m ≤ k → k < m + n := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- SetRel.prod_comp_prod_of_inter_nonempty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.prod_comp_prod_of_inter_nonempty.h5 : ¬∀ {α β γ : Type} {t₁ t₂ : Set β} (s : Set α) (u : Set γ), SetRel.comp (s ×ˢ t₁) (t₂ ×ˢ u) = s ×ˢ u := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- ENNReal.sub_lt_iff_lt_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_lt_iff_lt_left.h4 : ¬∀ {a b c : ENNReal}, b ≠ ⊤ → (a - b < c ↔ a < b + c) := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  simp)

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

-- ENNReal.sub_eq_of_eq_add_rev, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_eq_of_eq_add_rev.h3 : ¬∀ {a b c : ENNReal}, a = b + c → a - b = c := fun hc_h => absurd (@hc_h _ (⊤) (1) rfl) (by
  simp)

-- ENNReal.sub_eq_of_eq_add_rev, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_eq_of_eq_add_rev.h4 : ¬∀ {a b c : ENNReal}, b ≠ ⊤ → a - b = c := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.mul_left_inj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_left_inj.h3 : ¬∀ {a b c : ENNReal}, c ≠ ⊤ → (a * c = b * c ↔ a = b) := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  simp)

-- ExistsUnique.intro, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ExistsUnique.intro.h3 : ¬∀ {α : Type} {p : α → Prop} (w : α), (∀ (y : α), p y → y = w) → ∃! x : α, p x := fun hc_h => absurd (@hc_h (ℕ) (fun _ => False : ℕ → Prop) (0) (by
  simp)) (by
  simp)

-- ExistsUnique.intro, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ExistsUnique.intro.h4 : ¬∀ {α : Type} {p : α → Prop} (w : α), p w → ∃! x : α, p x := fun hc_h => absurd (@hc_h (Bool) (fun _ => True : Bool → Prop) (Bool.false) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  nofun)

-- ENNReal.mul_lt_mul_iff_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_lt_mul_iff_right.h3 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → (a * b < a * c ↔ b < c) := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.le_sub_iff_add_le_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_sub_iff_add_le_right.h4 : ¬∀ {a b c : ENNReal}, c ≠ ⊤ → (a ≤ b - c ↔ a + c ≤ b) := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.eq_sub_of_add_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.eq_sub_of_add_eq.h3 : ¬∀ {a b c : ENNReal}, a + c = b → a = b - c := fun hc_h => absurd (@hc_h (1) _ (⊤) rfl) (by
  simp)

-- ENNReal.eq_sub_of_add_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.eq_sub_of_add_eq.h4 : ¬∀ {a b c : ENNReal}, c ≠ ⊤ → a = b - c := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  simp)

-- ENNReal.sub_sub_sub_cancel_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_sub_sub_cancel_left.h4 : ¬∀ {a b c : ENNReal}, a ≠ ⊤ → a - c - (a - b) = b - c := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  simp)

-- Equiv.Perm.eq_of_prodExtendRight_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Perm.eq_of_prodExtendRight_ne.h7 : ¬∀ {α₁ β₁ : Type} [inst : DecidableEq α₁] {e : Equiv.Perm β₁} {a a' : α₁} {b : β₁}, a' = a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (1) (0) (1) (0)) (by
  decide +kernel)

-- ENNReal.sub_lt_iff_lt_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_lt_iff_lt_right.h4 : ¬∀ {a b c : ENNReal}, b ≠ ⊤ → (a - b < c ↔ a < c + b) := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  simp)

-- Iff.ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iff.ne.h6 : ¬∀ {α β : Type} {a b : α} {c d : β}, a ≠ b ↔ c ≠ d := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) (0) (0) (1)) (by
  decide +kernel)

-- Function.Semiconj.eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Semiconj.eq.h5 : ¬∀ {α β : Type} {f : α → β} {ga : α → α} {gb : β → β} (x : α), f (ga x) = gb (f x) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Equiv.image_antitone, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.image_antitone.h6 : Not
      (∀ {α β : Type} [inst : Preorder α] [inst_1 : Preorder β] {e : Equiv α β} (s : Set α),
        @Antitone (@Set.Elem α s)
          (@Set.Elem β
            (@Set.image α β
              (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
                (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e)
              s))
          (@Subtype.preorder α inst fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) s x)
          (@Subtype.preorder β inst_1 fun (x : β) =>
            @Membership.mem β (Set β) (@Set.instMembership β)
              (@Set.image α β
                (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
                  (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e)
                s)
              x)
          (@DFunLike.coe
            (Equiv (@Set.Elem α s)
              (@Set.Elem β
                (@Set.image α β
                  (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
                    (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e)
                  s)))
            (@Set.Elem α s)
            (fun (x : @Set.Elem α s) =>
              @Set.Elem β
                (@Set.image α β
                  (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
                    (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e)
                  s))
            (@EquivLike.toFunLike
              (Equiv (@Set.Elem α s)
                (@Set.Elem β
                  (@Set.image α β
                    (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
                      (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e)
                    s)))
              (@Set.Elem α s)
              (@Set.Elem β
                (@Set.image α β
                  (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
                    (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e)
                  s))
              (@Equiv.instEquivLike (@Set.Elem α s)
                (@Set.Elem β
                  (@Set.image α β
                    (@DFunLike.coe (Equiv α β) α (fun (x : α) => β)
                      (@EquivLike.toFunLike (Equiv α β) α β (@Equiv.instEquivLike α β)) e)
                    s))))
            (@Equiv.image α β e s))) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialOrder.toPreorder Bool Bool.instPartialOrder) (@PartialOrder.toPreorder Bool Bool.instPartialOrder) (@Equiv.mk Bool Bool (fun (b : Bool) => b) (fun (b : Bool) => b)
      (@of_decide_eq_true
        (autoParam (@Function.LeftInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b) Equiv.left_inv._autoParam)
        (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype (fun (b : Bool) => b)
          fun (b : Bool) => b)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (autoParam (@Function.LeftInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b)
                Equiv.left_inv._autoParam)
              (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype (fun (b : Bool) => b)
                fun (b : Bool) => b))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (autoParam (@Function.RightInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b) Equiv.right_inv._autoParam)
        (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype (fun (b : Bool) => b)
          fun (b : Bool) => b)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (autoParam (@Function.RightInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b)
                Equiv.right_inv._autoParam)
              (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype (fun (b : Bool) => b)
                fun (b : Bool) => b))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Set.ofPred Bool fun (x : Bool) => True)) (by
  decide +kernel)

-- ENNReal.div_mul_cancel', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_mul_cancel'.h2 : ¬∀ {a b : ENNReal}, (a = ⊤ → b = 0) → b / a * a = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.div_mul_cancel', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_mul_cancel'.h3 : ¬∀ {a b : ENNReal}, (a = 0 → b = 0) → b / a * a = b := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.zpow_le_one_of_nonpos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.zpow_le_one_of_nonpos.h1 : ¬∀ {n : ℤ} {x : ENNReal}, 1 ≤ x → x ^ n ≤ 1 := fun hc_h => absurd (@hc_h (1) (2) (by
  simp)) (by
  simp)

-- ENNReal.inv_mul_cancel_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_mul_cancel_right.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → a * b⁻¹ * b = a := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  simp)

-- ENNReal.inv_mul_cancel_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_mul_cancel_right.h3 : ¬∀ {a b : ENNReal}, b ≠ 0 → a * b⁻¹ * b = a := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.exists_nat_pos_inv_mul_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_nat_pos_inv_mul_lt.h2 : Not
      (∀ {a b : ENNReal},
        @Ne ENNReal b (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) →
          ∃ (n : Nat),
            And (@GT.gt Nat instLTNat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder))
                (@HMul.hMul ENNReal ENNReal ENNReal
                  (@instHMul ENNReal
                    (@Distrib.toMul ENNReal
                      (@instDistribOfSemiring ENNReal (@CommSemiring.toSemiring ENNReal ENNReal.instCommSemiring))))
                  (@Inv.inv ENNReal ENNReal.instInv
                    (@Nat.cast ENNReal
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      n))
                  a)
                b)) := fun hc_h => absurd (@hc_h (@Top.top ENNReal ENNReal.instTop) (@OfNat.ofNat ENNReal (nat_lit 1) (@One.toOfNat1 ENNReal ENNReal.instOne)) (by
  simp)) (by
  simp)

-- ENNReal.exists_nat_pos_inv_mul_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_nat_pos_inv_mul_lt.h3 : Not
      (∀ {a b : ENNReal},
        @Ne ENNReal a (@Top.top ENNReal ENNReal.instTop) →
          ∃ (n : Nat),
            And (@GT.gt Nat instLTNat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder))
                (@HMul.hMul ENNReal ENNReal ENNReal
                  (@instHMul ENNReal
                    (@Distrib.toMul ENNReal
                      (@instDistribOfSemiring ENNReal (@CommSemiring.toSemiring ENNReal ENNReal.instCommSemiring))))
                  (@Inv.inv ENNReal ENNReal.instInv
                    (@Nat.cast ENNReal
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      n))
                  a)
                b)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero)) (by
  decide)) (by
  simp)

-- ENNReal.div_ne_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_ne_top.h2 : ¬∀ {x y : ENNReal}, y ≠ 0 → x / y ≠ ⊤ := fun hc_h => absurd (@hc_h (⊤) (1) (by
  simp)) (by
  simp)

-- ENNReal.div_ne_top, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_ne_top.h3 : ¬∀ {x y : ENNReal}, x ≠ ⊤ → x / y ≠ ⊤ := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  simp)

-- Function.Injective2.left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective2.left.h4 : ¬∀ {α β γ : Type} {f : α → β → γ} (b : β), Function.Injective fun (a : α) => f a b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) (fun a b => a < b : ℕ → ℕ → Bool) (0)) (by
  simp)

-- ENNReal.mul_div_cancel_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_div_cancel_right.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → a * b / b = a := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  norm_num)

-- ENNReal.mul_div_cancel_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_div_cancel_right.h3 : ¬∀ {a b : ENNReal}, b ≠ 0 → a * b / b = a := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.div_lt_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_lt_top.h2 : ¬∀ {x y : ENNReal}, y ≠ 0 → x / y < ⊤ := fun hc_h => absurd (@hc_h (⊤) (1) (by
  simp)) (by
  simp)

-- ENNReal.div_lt_top, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_lt_top.h3 : ¬∀ {x y : ENNReal}, x ≠ ⊤ → x / y < ⊤ := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  simp)

-- ENNReal.mul_inv_cancel_left', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_inv_cancel_left'.h2 : ¬∀ {a b : ENNReal}, (a = ⊤ → b = 0) → a * (a⁻¹ * b) = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.mul_inv_cancel_left', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_inv_cancel_left'.h3 : ¬∀ {a b : ENNReal}, (a = 0 → b = 0) → a * (a⁻¹ * b) = b := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- instUncountableSigmaOfNonempty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instUncountableSigmaOfNonempty.h3 : ¬∀ {α : Type} {π : α → Type} [inst : Nonempty α], Uncountable (Sigma π) := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) _) (by
  simp)

-- instUncountableProdOfNonempty_1, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instUncountableProdOfNonempty_1.h3 : ¬∀ {α β : Type} [inst : Nonempty α], Uncountable (α × β) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _) (by
  simp)

-- Function.mtr, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.mtr.h2 : ¬∀ {a b : Prop}, b → a := fun hc_h => absurd (@hc_h (False) (True) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Function.mtr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.mtr.h3 : ¬∀ {a b : Prop}, (¬a → ¬b) → a := fun hc_h => absurd (@hc_h (False) (False) (by
  decide)) (by
  decide +kernel)

-- Equiv.coe_subtypeEquiv_eq_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.coe_subtypeEquiv_eq_map.h5 : ¬∀ {X Y : Type} {p : X → Prop} {q : Y → Prop} (e : X ≃ Y) (x : X), p x ↔ q (e x) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (1)) (by
  simp)

-- Not.imp_symm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Not.imp_symm.h2 : ¬∀ {a b : Prop}, ¬b → a := fun hc_h => absurd (@hc_h (False) (False) (by
  decide)) (by
  decide +kernel)

-- Not.imp_symm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Not.imp_symm.h3 : ¬∀ {a b : Prop}, (¬a → b) → a := fun hc_h => absurd (@hc_h (False) (True) (by
  decide)) (by
  decide +kernel)

-- Ne.dite_eq_left_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ne.dite_eq_left_iff.h5 : ¬∀ {α : Type} {P : Prop} [inst : Decidable P] {a : α} {B : ¬P → α}, dite P (fun (x : P) => a) B = a ↔ P := fun hc_h => absurd (@hc_h (ℕ) (False) (instDecidableFalse) (0) (fun (a : ¬False) => 0)) (by
  decide +kernel)

-- Function.RightInverse.eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.RightInverse.eq.h4 : ¬∀ {α β : Type} {g : β → α} {f : α → β} (x : β), f (g x) = x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- ENNReal.HolderConjugate.sub_one_mul_inv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderConjugate.sub_one_mul_inv.h2 : ¬∀ (p q : ENNReal), p ≠ ⊤ → (p - 1) * p⁻¹ = q⁻¹ := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.HolderConjugate.sub_one_mul_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderConjugate.sub_one_mul_inv.h3 : ¬∀ (p q : ENNReal) [inst : p.HolderConjugate q], (p - 1) * p⁻¹ = q⁻¹ := fun hc_h => absurd (@hc_h (⊤) (1) _) (by
  simp)

-- Function.mt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.mt.h2 : ¬∀ {a b : Prop}, ¬b → ¬a := fun hc_h => absurd (@hc_h (True) (False) (by
  decide)) (by
  decide +kernel)

-- Function.mt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.mt.h3 : ¬∀ {a b : Prop}, (a → b) → ¬a := fun hc_h => absurd (@hc_h (True) (True) (by
  decide)) (by
  decide +kernel)

-- Function.Semiconj₂.comp_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Semiconj₂.comp_eq.h5 : ¬∀ {α β : Type} {f : α → β} {ga : α → α → α} {gb : β → β → β}, Function.bicompr f ga = Function.bicompl gb f f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun a b => !a || b : Bool → Bool → Bool) (fun a b => a - b : ℕ → ℕ → ℕ)) (by
  decide +kernel)

-- sign_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.sign_pow.h3 : ¬∀ {α : Type} [inst : Ring α] [inst_1 : LinearOrder α] (x : α) (n : ℕ), SignType.sign (x ^ n) = SignType.sign x ^ n := fun hc_h => absurd (@hc_h (Unit) (PUnit.commRing.toRing) (PUnit.instLinearOrder) (PUnit.unit) (0)) (by
  decide +kernel)

-- SignType.pow_even, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignType.pow_even.h2 : ¬∀ (s : SignType) {n : ℕ}, s ≠ 0 → s ^ n = 1 := fun hc_h => absurd (@hc_h (SignType.neg) (1) (by
  decide)) (by
  decide +kernel)

-- SignType.pow_even, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignType.pow_even.h3 : ¬∀ (s : SignType) {n : ℕ}, Even n → s ^ n = 1 := fun hc_h => absurd (@hc_h (SignType.zero) (2) (by
  decide)) (by
  decide +kernel)

-- existsUnique_of_exists_of_unique, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.existsUnique_of_exists_of_unique.h2 : ¬∀ {α : Type} {p : α → Prop}, (∀ (y₁ y₂ : α), p y₁ → p y₂ → y₁ = y₂) → ∃! x : α, p x := fun hc_h => absurd (@hc_h (ℕ) (fun _ => False : ℕ → Prop) (by
  simp)) (by
  simp)

-- existsUnique_of_exists_of_unique, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.existsUnique_of_exists_of_unique.h3.inst : ¬∃! x : Bool, (fun (x : Bool) => True) x := by
  nofun
set_option maxHeartbeats 300 in
theorem HypCheckProof.existsUnique_of_exists_of_unique.h3.prem0 : ∃ (x : Bool), (fun (x : Bool) => True) x := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.existsUnique_of_exists_of_unique.h3 : ¬∀ {α : Type} {p : α → Prop}, (∃ (x : α), p x) → ∃! x : α, p x := fun hc_h => HypCheckProof.existsUnique_of_exists_of_unique.h3.inst (@hc_h (Bool) (fun (x : Bool) => True) HypCheckProof.existsUnique_of_exists_of_unique.h3.prem0)

-- SignType.zpow_even, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignType.zpow_even.h2 : ¬∀ (s : SignType) {z : ℤ}, s ≠ 0 → s ^ z = 1 := fun hc_h => absurd (@hc_h (SignType.neg) (1) (by
  decide)) (by
  decide +kernel)

-- SignType.zpow_even, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignType.zpow_even.h3 : ¬∀ (s : SignType) {z : ℤ}, Even z → s ^ z = 1 := fun hc_h => absurd (@hc_h (SignType.zero) (2) (by
  decide)) (by
  decide +kernel)

-- Function.Injective.surjective_comp_right', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.surjective_comp_right'.h4 : ¬∀ {α β γ : Type} {f : α → β} (g₀ : β → γ), Function.Surjective fun (g : β → γ) => g ∘ f := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool) (fun _ => true : Bool → Bool) (not : Bool → Bool)) (by
  decide +kernel)

-- Function.iterate_invariant, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.iterate_invariant.h4 : ¬∀ {α β : Type} {f : α → α} {g : α → β} (n : ℕ), g ∘ f^[n] = g := fun hc_h => absurd (@hc_h (Bool) (ℕ) (not : Bool → Bool) (fun b => if b then 1 else 0 : Bool → ℕ) (1)) (by
  decide +kernel)

-- SetRel.image_subset_image_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.image_subset_image_left.h5 : ¬∀ {α β : Type} {R₁ R₂ : SetRel α β} {s : Set α}, R₁.image s ⊆ R₂.image s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (⊤) (∅) ({n : ℕ | n = 0})) (by
  simp)

-- NNReal.exists_mem_Ico_zpow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.exists_mem_Ico_zpow.h3 : ¬∀ {x y : NNReal}, x ≠ 0 → ∃ (n : ℤ), x ∈ Set.Ico (y ^ n) (y ^ (n + 1)) := fun hc_h => absurd (@hc_h (1) (1) (by
  simp)) (by
  simp)

-- ENNReal.toNNReal_eq_toNNReal_iff', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_eq_toNNReal_iff'.h2 : ¬∀ {x y : ENNReal}, y ≠ ⊤ → (x.toNNReal = y.toNNReal ↔ x = y) := fun hc_h => absurd (@hc_h (⊤) (0) (by
  decide)) (by
  simp)

-- ENNReal.toNNReal_eq_toNNReal_iff', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_eq_toNNReal_iff'.h3 : ¬∀ {x y : ENNReal}, x ≠ ⊤ → (x.toNNReal = y.toNNReal ↔ x = y) := fun hc_h => absurd (@hc_h (0) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.toNNReal_lt_toNNReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_lt_toNNReal.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → (a.toNNReal < b.toNNReal ↔ a < b) := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.toNNReal_lt_toNNReal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_lt_toNNReal.h3 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → (a.toNNReal < b.toNNReal ↔ a < b) := fun hc_h => absurd (@hc_h (0) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.toReal_mono_of_top_imp_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_mono_of_top_imp_top.h2 : ¬∀ {a b : ENNReal}, (b = ⊤ → a = ⊤) → a.toReal ≤ b.toReal := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  simp)

-- coe_finRotate_symm_of_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.coe_finRotate_symm_of_ne_zero.h3 : Not
      (∀ {n : Nat} [inst : @NeZero Nat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) n] {i : Fin n},
        @Eq Nat
          (@Fin.val n
            (@DFunLike.coe (Equiv (Fin n) (Fin n)) (Fin n) (fun (x : Fin n) => Fin n)
              (@EquivLike.toFunLike (Equiv (Fin n) (Fin n)) (Fin n) (Fin n) (@Equiv.instEquivLike (Fin n) (Fin n)))
              (@Equiv.symm (Fin n) (Fin n) (finRotate n)) i))
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@Fin.val n i)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) _ (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- ENNReal.toReal_strict_mono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_strict_mono.h3 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → a.toReal < b.toReal := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.toNNReal_strict_mono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_strict_mono.h3 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → a.toNNReal < b.toNNReal := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.toReal_lt_toReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_lt_toReal.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → (a.toReal < b.toReal ↔ a < b) := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.toReal_lt_toReal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_lt_toReal.h3 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → (a.toReal < b.toReal ↔ a < b) := fun hc_h => absurd (@hc_h (0) (⊤) (by
  decide)) (by
  simp)

-- ENNReal.lt_top_of_mul_ne_top_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.lt_top_of_mul_ne_top_left.h2 : ¬∀ {a b : ENNReal}, b ≠ 0 → a < ⊤ := fun hc_h => absurd (@hc_h (⊤) (1) (by
  simp)) (by
  decide +kernel)

-- ENNReal.lt_top_of_mul_ne_top_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.lt_top_of_mul_ne_top_left.h3 : ¬∀ {a b : ENNReal}, a * b ≠ ⊤ → a < ⊤ := fun hc_h => absurd (@hc_h (⊤) (0) (by
  simp)) (by
  decide +kernel)

-- ENNReal.mul_eq_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_eq_left.h2 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → (a * b = a ↔ b = 1) := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.mul_eq_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_eq_left.h3 : ¬∀ {a b : ENNReal}, a ≠ 0 → (a * b = a ↔ b = 1) := fun hc_h => absurd (@hc_h (⊤) (2) (by
  decide)) (by
  simp)

-- instLeftCommutativeOfCommutativeOfAssociative, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instLeftCommutativeOfCommutativeOfAssociative.h2 : ¬∀ {α : Type} {f : α → α → α} [ha : Std.Associative f], LeftCommutative f := fun hc_h => absurd (@hc_h (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done)))) (by
  exact fun hc_c =>
    absurd (hc_c.left_comm (0 : ℕ) (1 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- instLeftCommutativeOfCommutativeOfAssociative, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instLeftCommutativeOfCommutativeOfAssociative.h3 : ¬∀ {α : Type} {f : α → α → α} [hc : Std.Commutative f], LeftCommutative f := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide))) (by
  exact fun hc_c =>
    absurd (hc_c.left_comm (Bool.false : Bool) (Bool.true : Bool) (Bool.false : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.sub_sub_cancel, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_sub_cancel.h3 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → a - (a - b) = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- Function.LeftInverse.eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.eq.h4 : ¬∀ {α β : Type} {g : β → α} {f : α → β} (x : α), g (f x) = x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Equiv.Set.insert_apply_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.insert_apply_right.h4 : ¬∀ {α : Type} {s : Set α} [inst : DecidablePred fun (x : α) => x ∈ s] {a : α} (b : ↑s), a ∉ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => Set.decidableOfPred a fun (n : ℕ) => n = 0) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n = 0} }))) (by
  decide +kernel)

-- Function.Injective2.right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective2.right.h4 : ¬∀ {α β γ : Type} {f : α → β → γ} (a : α), Function.Injective (f a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0)) (by
  simp)

-- Equiv.Set.image_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Set.image_apply.h4 : ¬∀ {α β : Type} (f : α → β) (s : Set α) (p : ↑s), Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0}) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n = 0} }))) (by
  simp)

-- Equiv.ofLeftInverse_apply_coe, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofLeftInverse_apply_coe.h4 : ¬∀ {α β : Type} (f : α → β) (f_inv : Nonempty α → β → α) (a : α) (h : Nonempty α), Function.LeftInverse (f_inv h) f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun (a : Nonempty Bool) (n : ℕ) => n % 2 == 0) (Bool.false)) (by
  (simp <;> decide))

-- Ne.dite_ne_right_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ne.dite_ne_right_iff.h5 : ¬∀ {α : Type} {P : Prop} [inst : Decidable P] {b : α} {A : P → α}, (dite P A fun (x : ¬P) => b) ≠ b ↔ P := fun hc_h => absurd (@hc_h (ℕ) (True) (instDecidableTrue) (0) (fun (a : True) => 0)) (by
  decide +kernel)

-- ENNReal.le_iInf_add_iInf, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_iInf_add_iInf.h5 : ¬∀ {ι : Type} {f : ι → ENNReal} {a : ENNReal} {κ : Type} {g : κ → ENNReal}, a ≤ iInf f + iInf g := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => 0) (1) (ℕ) (fun (a : ℕ) => 0)) (by
  simp)

-- ENNReal.toNNReal_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_add.h2 : ¬∀ {r₁ r₂ : ENNReal}, r₂ ≠ ⊤ → (r₁ + r₂).toNNReal = r₁.toNNReal + r₂.toNNReal := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.toNNReal_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_add.h3 : ¬∀ {r₁ r₂ : ENNReal}, r₁ ≠ ⊤ → (r₁ + r₂).toNNReal = r₁.toNNReal + r₂.toNNReal := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  simp)

-- instSubsingletonSumOfIsEmpty_1, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instSubsingletonSumOfIsEmpty_1.h2 : ¬∀ {α β : Type} [inst : Subsingleton β], Subsingleton (α ⊕ β) := fun hc_h => absurd (@hc_h (ℕ) (Unit) _) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (Sum.inl 0 : ℕ ⊕ Unit) (Sum.inr PUnit.unit : ℕ ⊕ Unit))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- instSubsingletonSumOfIsEmpty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instSubsingletonSumOfIsEmpty.h3 : ¬∀ {α β : Type} [inst : Subsingleton α], Subsingleton (α ⊕ β) := fun hc_h => absurd (@hc_h (Unit) (ℕ) _) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (Sum.inl PUnit.unit : Unit ⊕ ℕ) (Sum.inr 0 : Unit ⊕ ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- PartialEquiv.IsImage.symm_image_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.IsImage.symm_image_eq.h5 : Not
      (∀ {α β : Type} {e : PartialEquiv α β} {s : Set α} {t : Set β},
        @Eq (Set α)
          (@Set.image β α (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e))
            (@Min.min (Set β) (@Set.instMin β) (@PartialEquiv.target α β e) t))
          (@Min.min (Set α) (@Set.instMin α) (@PartialEquiv.source α β e) s)) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not Bool.not (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                  (instDecidableEqBool a.not Bool.true))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                        (instDecidableEqBool a.not Bool.true))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                  (instDecidableEqBool a.not Bool.false))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                        (instDecidableEqBool a.not Bool.false))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)) (by
  simp)

-- Ne.ite_ne_left_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ne.ite_ne_left_iff.h5 : ¬∀ {α : Type} {P : Prop} [inst : Decidable P] {a b : α}, (if P then a else b) ≠ a ↔ ¬P := fun hc_h => absurd (@hc_h (ℕ) (False) (instDecidableFalse) (0) (0)) (by
  decide +kernel)

-- Function.Bijective.of_comp_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Bijective.of_comp_iff.h5 : ¬∀ {α β γ : Type} (f : α → β) {g : γ → α}, Function.Bijective (f ∘ g) ↔ Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool) (not : Bool → Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- PartialEquiv.IsImage.preimage_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.IsImage.preimage_eq.h5 : Not
      (∀ {α β : Type} {e : PartialEquiv α β} {s : Set α} {t : Set β},
        @Eq (Set α)
          (@Min.min (Set α) (@Set.instMin α) (@PartialEquiv.source α β e) (@Set.preimage α β (@PartialEquiv.toFun α β e) t))
          (@Min.min (Set α) (@Set.instMin α) (@PartialEquiv.source α β e) s)) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not Bool.not (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                  (instDecidableEqBool a.not Bool.true))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                        (instDecidableEqBool a.not Bool.true))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                  (instDecidableEqBool a.not Bool.false))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                        (instDecidableEqBool a.not Bool.false))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)) (by
  simp)

-- Equiv.toPartialEquivOfImageEq_apply, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.toPartialEquivOfImageEq_apply.h5 : ¬∀ {α β : Type} (e : α ≃ β) (s : Set α) (t : Set β), ⇑e '' s = t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- ENNReal.exists_nat_mul_gt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_nat_mul_gt.h2 : ¬∀ {a b : ENNReal}, b ≠ ⊤ → ∃ (n : ℕ), b < ↑n * a := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  simp)

-- ENNReal.exists_nat_mul_gt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.exists_nat_mul_gt.h3 : ¬∀ {a b : ENNReal}, a ≠ 0 → ∃ (n : ℕ), b < ↑n * a := fun hc_h => absurd (@hc_h (1) (⊤) (by
  simp)) (by
  simp)

-- ENNReal.div_div_cancel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_div_cancel.h2 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → a / (a / b) = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.div_div_cancel, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_div_cancel.h3 : ¬∀ {a b : ENNReal}, a ≠ 0 → a / (a / b) = b := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.inv_mul_cancel_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_mul_cancel_left.h2 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → a⁻¹ * (a * b) = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.inv_mul_cancel_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_mul_cancel_left.h3 : ¬∀ {a b : ENNReal}, a ≠ 0 → a⁻¹ * (a * b) = b := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- ENNReal.div_mul_cancel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_mul_cancel.h2 : ¬∀ {a b : ENNReal}, a ≠ ⊤ → b / a * a = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- ENNReal.div_mul_cancel, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_mul_cancel.h3 : ¬∀ {a b : ENNReal}, a ≠ 0 → b / a * a = b := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  simp)

-- NNReal.iSup_mul_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.iSup_mul_le.h4 : ¬∀ {ι : Type} {a : NNReal} {g : ι → NNReal} {h : NNReal}, iSup g * h ≤ a := fun hc_h => absurd (@hc_h (ℕ) (0) (fun (a : ℕ) => 1) (1)) (by
  simp)

-- Encodable.choose_spec, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Encodable.choose_spec.h4 : ¬∀ {α : Type} {p : α → Prop} [inst : Encodable α] [inst : DecidablePred p], ∃ (x : α), p x := fun hc_h => absurd (@hc_h (ℕ) (fun _ => False : ℕ → Prop) (Nat.encodable) (fun (a : ℕ) => instDecidableFalse)) (by
  simp)

-- Equivalence.comap, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equivalence.comap.h3 : ¬∀ {α β : Type} {r : β → β → Prop} (f : α → β), Equivalence (Function.onFun r f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  nofun)

-- Function.instIsPreorderOnFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instIsPreorderOnFun.h4 : ¬∀ {α β : Type} (r : β → β → Prop) (f : α → β), IsPreorder α (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.toRefl.refl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Denumerable.ofNat_of_decode, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Denumerable.ofNat_of_decode.h4 : ¬∀ {α : Type} [inst : Denumerable α] {n : ℕ} {b : α}, Denumerable.ofNat α n = b := fun hc_h => absurd (@hc_h (ℕ) (Denumerable.nat) (0) (1)) (by
  decide +kernel)

-- Relation.ReflTransGen.cases_tail, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.ReflTransGen.cases_tail.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, b = a ∨ ∃ (c : α), Relation.ReflTransGen r a c ∧ r c b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) (0)) (by
  simp)

-- Ne.ne_or_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ne.ne_or_ne.h4 : ¬∀ {α : Type} {x y : α} (z : α), x ≠ z ∨ y ≠ z := fun hc_h => absurd (@hc_h (ℕ) (0) (0) (0)) (by
  decide +kernel)

-- Function.Bijective.comp_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Bijective.comp_right.h4 : ¬∀ {α β γ : Type} {f : α → β}, Function.Bijective fun (g : β → γ) => g ∘ f := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- Relation.SymmGen.of_ge, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Relation.SymmGen.of_ge.h4.inst : ¬Relation.SymmGen (fun (x1 x2 : Bool) => False) Bool.false Bool.false := by
  decide +kernel
theorem HypCheckProof.Relation.SymmGen.of_ge.h4 : ¬∀ {α : Type} [inst : LE α] {a b : α}, Relation.SymmGen (fun (x1 x2 : α) => x1 ≤ x2) a b := fun hc_h => HypCheckProof.Relation.SymmGen.of_ge.h4.inst (@hc_h (Bool) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (Bool.false) (Bool.false))

-- Relation.SymmGen.of_rel_symm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.SymmGen.of_rel_symm.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, Relation.SymmGen r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0)) (by
  decide +kernel)

-- Relation.SymmGen.symm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.SymmGen.symm.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, Relation.SymmGen r b a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0)) (by
  decide +kernel)

-- Function.instReflOnFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instReflOnFun.h4 : ¬∀ {α β : Type} (r : β → β → Prop) (f : α → β), Std.Refl (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.refl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Relation.symmGen_of_total, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.symmGen_of_total.h2 : ¬∀ {α : Type} {r : α → α → Prop} (a b : α), Relation.SymmGen r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0)) (by
  decide +kernel)

-- Function.instIsStrictWeakOrderOnFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instIsStrictWeakOrderOnFun.h4 : ¬∀ {α β : Type} (r : β → β → Prop) (f : α → β), IsStrictWeakOrder α (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsStrictOrder.toIrrefl.irrefl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Relation.SymmGen.of_rel, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.SymmGen.of_rel.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, Relation.SymmGen r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0)) (by
  decide +kernel)

-- IsEquiv.comap, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsEquiv.comap.h3 : ¬∀ {α β : Type} {r : β → β → Prop} (f : α → β), IsEquiv α (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPreorder.toRefl.refl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.instAsymmOnFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instAsymmOnFun.h4 : ¬∀ {α β : Type} (r : β → β → Prop) (f : α → β), Std.Asymm (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd
      (hc_c.asymm (0 : ℕ) (0 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.instTotalOnFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instTotalOnFun.h4 : ¬∀ {α β : Type} (r : β → β → Prop) (f : α → β), Std.Total (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.Symm.iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Symm.iff.h2 : ¬∀ {α : Type} {r : α → α → Prop} (x y : α), r x y ↔ r y x := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (1)) (by
  decide +kernel)

-- Relation.ReflTransGen.cases_head, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.ReflTransGen.cases_head.h4 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, a = b ∨ ∃ (c : α), r a c ∧ Relation.ReflTransGen r c b := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => False : Bool → Bool → Prop) (Bool.false) (Bool.true)) (by
  simp)

-- Function.Bijective.existsUnique, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Bijective.existsUnique.h3 : ¬∀ {α β : Type} {f : α → β} (b : β), ∃! a : α, f a = b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  simp)

-- forall_or_of_or_forall, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.forall_or_of_or_forall.h3 : ¬∀ {α : Type} {p : α → Prop} {b : Prop} (x : α), b ∨ p x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (False) (1)) (by
  decide +kernel)

-- Function.instIsStrictOrderOnFun, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instIsStrictOrderOnFun.h4 : ¬∀ {α β : Type} (r : β → β → Prop) (f : α → β), IsStrictOrder α (Function.onFun r f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.toIrrefl.irrefl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Equiv.ofBijective_symm_apply_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofBijective_symm_apply_apply.h3 : ¬∀ {α β : Type} (f : α → β) (x : α), Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ => 0 : Bool → ℕ) (Bool.false)) (by
  nofun)

-- Function.RightInverse.injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.RightInverse.injective.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α}, Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Equiv.Perm.congr_fun, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.Perm.congr_fun.h3 : Not
      (∀ {α : Type} {f g : Equiv.Perm α} (x : α),
        @Eq α
          (@DFunLike.coe (Equiv.Perm α) α (fun (x : α) => α)
            (@EquivLike.toFunLike (Equiv.Perm α) α α (@Equiv.instEquivLike α α)) f x)
          (@DFunLike.coe (Equiv.Perm α) α (fun (x : α) => α)
            (@EquivLike.toFunLike (Equiv.Perm α) α α (@Equiv.instEquivLike α α)) g x)) := fun hc_h => absurd (@hc_h (Bool) (@Equiv.mk Bool Bool Bool.not Bool.not
      (@of_decide_eq_true (autoParam (@Function.LeftInverse Bool Bool Bool.not Bool.not) Equiv.left_inv._autoParam)
        (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not)
        (@id
          (@Eq Bool
            (@Decidable.decide (autoParam (@Function.LeftInverse Bool Bool Bool.not Bool.not) Equiv.left_inv._autoParam)
              (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true (autoParam (@Function.RightInverse Bool Bool Bool.not Bool.not) Equiv.right_inv._autoParam)
        (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not)
        (@id
          (@Eq Bool
            (@Decidable.decide (autoParam (@Function.RightInverse Bool Bool Bool.not Bool.not) Equiv.right_inv._autoParam)
              (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Equiv.mk Bool Bool (fun (b : Bool) => b) (fun (b : Bool) => b)
      (@of_decide_eq_true
        (autoParam (@Function.LeftInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b) Equiv.left_inv._autoParam)
        (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype (fun (b : Bool) => b)
          fun (b : Bool) => b)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (autoParam (@Function.LeftInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b)
                Equiv.left_inv._autoParam)
              (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype (fun (b : Bool) => b)
                fun (b : Bool) => b))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (autoParam (@Function.RightInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b) Equiv.right_inv._autoParam)
        (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype (fun (b : Bool) => b)
          fun (b : Bool) => b)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (autoParam (@Function.RightInverse Bool Bool (fun (b : Bool) => b) fun (b : Bool) => b)
                Equiv.right_inv._autoParam)
              (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype (fun (b : Bool) => b)
                fun (b : Bool) => b))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (Bool.false)) (by
  decide +kernel)

-- Function.LeftInverse.surjective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.surjective.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α}, Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ => true : Bool → Bool) (not : Bool → Bool)) (by
  decide +kernel)

-- Function.Surjective.exists, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.exists.h3 : ¬∀ {α β : Type} {f : α → β} {p : β → Prop}, (∃ (y : β), p y) ↔ ∃ (x : α), p (f x) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n = 0 : ℕ → Prop)) (by
  simp)

-- eq_rec_on_bijective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.eq_rec_on_bijective.h4 : ¬∀ {α : Type} {C : α → Prop} {a a' : α}, a = a' := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (0) (1)) (by
  decide +kernel)

-- Equiv.removeNoneAux_none, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.removeNoneAux_none.h4 : ¬∀ {α β : Type} (e : Option α ≃ Option β) {x : α}, Option.some (e.removeNoneAux x) = e Option.none := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1) (0)) (by
  decide +kernel)

-- Equiv.removeNone_none, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.removeNone_none.h4 : ¬∀ {α β : Type} (e : Option α ≃ Option β) {x : α}, Option.some (e.removeNone x) = e Option.none := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1) (0)) (by
  decide +kernel)

-- Equiv.removeNone_aux_none, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.removeNone_aux_none.h4 : ¬∀ {α β : Type} (e : Option α ≃ Option β) {x : α}, Option.some (e.removeNoneAux x) = e Option.none := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1) (0)) (by
  decide +kernel)

-- Equiv.sumCompl_symm_apply_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.sumCompl_symm_apply_of_pos.h4 : ¬∀ {α : Type} {p : α → Prop} [inst : DecidablePred p] {a : α}, p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (1)) (by
  decide +kernel)

-- Equiv.sumCompl_symm_apply_of_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.sumCompl_symm_apply_of_neg.h4 : ¬∀ {α : Type} {p : α → Prop} [inst : DecidablePred p] {a : α}, ¬p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0)) (by
  decide +kernel)

-- Equiv.instAssociativeCoeForallForallArrowCongr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.instAssociativeCoeForallForallArrowCongr.h4 : ¬∀ {α₁ β₁ : Type} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁), Std.Associative ((e.arrowCongr (e.arrowCongr e)) f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1) (fun a b => a - b : ℕ → ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (1 : ℕ) (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Equiv.subtypeEquivRight_symm_apply_coe, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subtypeEquivRight_symm_apply_coe.h3 : ¬∀ {α : Type} {p q : α → Prop} (b : { b : α // q b }) (x : α), p x ↔ q x := fun hc_h => absurd (@hc_h (ℕ) (fun _ => False : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { b : ℕ // (fun (n : ℕ) => n = 0) b }))) (by
  simp)

-- Function.IsPartialInv.injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.IsPartialInv.injective.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → Option α}, Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (fun _ => none : ℕ → Option ℕ)) (by
  simp)

-- Equiv.subtypeSubtypeEquivSubtype_symm_apply_coe_coe, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subtypeSubtypeEquivSubtype_symm_apply_coe_coe.h3 : ¬∀ {α : Type} {p q : α → Prop} (a : Subtype q) {x : α}, q x → p x := fun hc_h => absurd (@hc_h (ℕ) (fun _ => False : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n = 0 }))) (by
  simp)

-- Equiv.instIdempotentOpCoeForallForallArrowCongr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.instIdempotentOpCoeForallForallArrowCongr.h4 : ¬∀ {α₁ β₁ : Type} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁), Std.IdempotentOp ((e.arrowCongr (e.arrowCongr e)) f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1) (fun a b => a - b : ℕ → ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.idempotent (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- NNReal.iSup_mul_iSup_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.iSup_mul_iSup_le.h4 : ¬∀ {ι : Type} {a : NNReal} {g h : ι → NNReal}, iSup g * iSup h ≤ a := fun hc_h => absurd (@hc_h (ℕ) (0) (fun (a : ℕ) => 1) (fun (a : ℕ) => 1)) (by
  simp)

-- Subtype.impEmbedding_apply_coe, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.impEmbedding_apply_coe.h3 : ¬∀ {α : Type} (p q : α → Prop) (x : { x : α // p x }) (x : α), p x → q x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // (fun (n : ℕ) => n = 0) x }))) (by
  simp)

-- Function.Commute.comp_iterate, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Commute.comp_iterate.h3 : ¬∀ {α : Type} {f g : α → α} (n : ℕ), (f ∘ g)^[n] = f^[n] ∘ g^[n] := fun hc_h => absurd (@hc_h (Bool) (not : Bool → Bool) (fun _ => true : Bool → Bool) (2)) (by
  decide +kernel)

-- SetRel.cod_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.cod_mono.h4 : ¬∀ {α β : Type} {R₁ R₂ : SetRel α β}, R₁.cod ⊆ R₂.cod := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (⊤) (∅)) (by
  simp)

-- Equiv.ofInjective_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofInjective_apply.h3 : ¬∀ {α β : Type} (f : α → β) (a : α), Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (0)) (by
  simp)

-- Set.strictMono_equivOfEq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.strictMono_equivOfEq.h4 : ¬∀ {α : Type} {s t : Set α} [inst : Preorder α], s = t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (Nat.instPreorder)) (by
  simp)

-- Function.RightInverse.iterate, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.RightInverse.iterate.h3 : ¬∀ {α : Type} {f g : α → α} (n : ℕ), Function.RightInverse g^[n] f^[n] := fun hc_h => absurd (@hc_h (Bool) (not : Bool → Bool) (fun _ => true : Bool → Bool) (1)) (by
  decide +kernel)

-- Equiv.ofLeftInverse_eq_ofInjective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofLeftInverse_eq_ofInjective.h4 : ¬∀ {α β : Type} (f : α → β) (f_inv : Nonempty α → β → α) (h : Nonempty α), Function.LeftInverse (f_inv h) f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun (a : Nonempty Bool) (n : ℕ) => n % 2 == 0)) (by
  (simp <;> decide))

-- Equiv.ofInjective_symm_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofInjective_symm_apply.h3 : ¬∀ {α β : Type} {f : α → β} (a : α), Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (0)) (by
  simp)

-- Function.Embedding.sumSet_preimage_inl, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.sumSet_preimage_inl.h4 : ¬∀ {α : Type} {s t : Set α} {r : Set α}, Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- Equiv.ofLeftInverse'_eq_ofInjective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofLeftInverse'_eq_ofInjective.h4 : ¬∀ {α β : Type} (f : α → β) (f_inv : β → α), Function.LeftInverse f_inv f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n % 2 == 0 : ℕ → Bool)) (by
  decide +kernel)

-- PEquiv.ext, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PEquiv.ext.h4 : Not (∀ {α β : Type} {f g : PEquiv α β}, @Eq (PEquiv α β) f g) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PEquiv.mk Bool Bool (fun (x : Bool) => @Option.none Bool) (fun (x : Bool) => @Option.none Bool)
      (@of_decide_eq_true
        (∀ (a b : Bool),
          Iff (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool a))
            (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool b)))
        (@Bool.instDecidableForallOfDecidablePred
          (fun (a : Bool) =>
            ∀ (b : Bool),
              Iff (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool a))
                (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool b)))
          fun (a : Bool) =>
          @Bool.instDecidableForallOfDecidablePred
            (fun (b : Bool) =>
              Iff (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool a))
                (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool b)))
            fun (a_1 : Bool) =>
            @instDecidableIff (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool a))
              (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool a_1))
              ((fun (a : Bool) => @Option.decidableNoneEq Bool (@Option.some Bool a)) a)
              (@Option.decidableNoneEq Bool (@Option.some Bool a_1)))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ (a b : Bool),
                Iff (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool a))
                  (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool b)))
              (@Bool.instDecidableForallOfDecidablePred
                (fun (a : Bool) =>
                  ∀ (b : Bool),
                    Iff (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool a))
                      (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool b)))
                fun (a : Bool) =>
                @Bool.instDecidableForallOfDecidablePred
                  (fun (b : Bool) =>
                    Iff (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool a))
                      (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool b)))
                  fun (a_1 : Bool) =>
                  @instDecidableIff (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool a))
                    (@Eq (Option Bool) (@Option.none Bool) (@Option.some Bool a_1))
                    ((fun (a : Bool) => @Option.decidableNoneEq Bool (@Option.some Bool a)) a)
                    (@Option.decidableNoneEq Bool (@Option.some Bool a_1))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@PEquiv.mk Bool Bool (@Option.some Bool) (@Option.some Bool)
      (@of_decide_eq_true
        (∀ (a b : Bool),
          Iff (@Eq (Option Bool) (@Option.some Bool b) (@Option.some Bool a))
            (@Eq (Option Bool) (@Option.some Bool a) (@Option.some Bool b)))
        (@Bool.instDecidableForallOfDecidablePred
          (fun (a : Bool) =>
            ∀ (b : Bool),
              Iff (@Eq (Option Bool) (@Option.some Bool b) (@Option.some Bool a))
                (@Eq (Option Bool) (@Option.some Bool a) (@Option.some Bool b)))
          fun (a : Bool) =>
          @Bool.instDecidableForallOfDecidablePred
            (fun (b : Bool) =>
              Iff (@Eq (Option Bool) (@Option.some Bool b) (@Option.some Bool a))
                (@Eq (Option Bool) (@Option.some Bool a) (@Option.some Bool b)))
            fun (a_1 : Bool) =>
            @instDecidableIff (@Eq (Option Bool) (@Option.some Bool a_1) (@Option.some Bool a))
              (@Eq (Option Bool) (@Option.some Bool a) (@Option.some Bool a_1))
              (@Option.instDecidableEq Bool instDecidableEqBool (@Option.some Bool a_1) (@Option.some Bool a))
              (@Option.instDecidableEq Bool instDecidableEqBool (@Option.some Bool a) (@Option.some Bool a_1)))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ (a b : Bool),
                Iff (@Eq (Option Bool) (@Option.some Bool b) (@Option.some Bool a))
                  (@Eq (Option Bool) (@Option.some Bool a) (@Option.some Bool b)))
              (@Bool.instDecidableForallOfDecidablePred
                (fun (a : Bool) =>
                  ∀ (b : Bool),
                    Iff (@Eq (Option Bool) (@Option.some Bool b) (@Option.some Bool a))
                      (@Eq (Option Bool) (@Option.some Bool a) (@Option.some Bool b)))
                fun (a : Bool) =>
                @Bool.instDecidableForallOfDecidablePred
                  (fun (b : Bool) =>
                    Iff (@Eq (Option Bool) (@Option.some Bool b) (@Option.some Bool a))
                      (@Eq (Option Bool) (@Option.some Bool a) (@Option.some Bool b)))
                  fun (a_1 : Bool) =>
                  @instDecidableIff (@Eq (Option Bool) (@Option.some Bool a_1) (@Option.some Bool a))
                    (@Eq (Option Bool) (@Option.some Bool a) (@Option.some Bool a_1))
                    (@Option.instDecidableEq Bool instDecidableEqBool (@Option.some Bool a_1) (@Option.some Bool a))
                    (@Option.instDecidableEq Bool instDecidableEqBool (@Option.some Bool a) (@Option.some Bool a_1))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- SetRel.IsCover.of_subset_iUnion_ball, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.IsCover.of_subset_iUnion_ball.h4 : ¬∀ {X : Type} {U : SetRel X X} {s N : Set X}, U.IsCover s N := fun hc_h => absurd (@hc_h (ℕ) (∅) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- IsEmpty.congr_fun, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsEmpty.congr_fun.h2 : ¬∀ {α β : Type} (f g : α → β), f = g := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun _ => 0 : Bool → ℕ)) (by
  decide +kernel)

-- eq_const_of_subsingleton, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.eq_const_of_subsingleton.h2 : ¬∀ {α β : Type} (f : α → β) (a : α), f = Function.const α (f a) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (Bool.false)) (by
  decide +kernel)

-- Function.Injective2.uncurry, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective2.uncurry.h4 : ¬∀ {α β γ : Type} {f : α → β → γ}, Function.Injective (Function.uncurry f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (ℕ) (fun (a b : Bool) => if b = Bool.true then 1 else 0)) (by
  decide +kernel)

-- PartialEquiv.right_inv', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.right_inv'.h4 : Not
      (∀ {α β : Type} (self : PartialEquiv α β) ⦃x : β⦄,
        @Eq β (@PartialEquiv.toFun α β self (@PartialEquiv.invFun α β self x)) x) := fun hc_h => absurd (@hc_h (Nat) (Nat) (@Inhabited.default (PartialEquiv Nat Nat) (@PartialEquiv.instInhabited Nat Nat instInhabitedNat instInhabitedNat)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Function.Embedding.sumSet_preimage_inr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.sumSet_preimage_inr.h4 : ¬∀ {α : Type} {s t : Set α} {r : Set α}, Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- PartialEquiv.symm_image_eq_source_inter_preimage, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.symm_image_eq_source_inter_preimage.h4 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) {s : Set β},
        @Eq (Set α) (@Set.image β α (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e)) s)
          (@Min.min (Set α) (@Set.instMin α) (@PartialEquiv.source α β e)
            (@Set.preimage α β (@PartialEquiv.toFun α β e) s))) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not Bool.not (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                  (instDecidableEqBool a.not Bool.true))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                        (instDecidableEqBool a.not Bool.true))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                  (instDecidableEqBool a.not Bool.false))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                        (instDecidableEqBool a.not Bool.false))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)) (by
  simp)

-- PartialEquiv.image_eq_target_inter_inv_preimage, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.image_eq_target_inter_inv_preimage.h4 : Not
      (∀ {α β : Type} (e : PartialEquiv α β) {s : Set α},
        @Eq (Set β) (@Set.image α β (@PartialEquiv.toFun α β e) s)
          (@Min.min (Set β) (@Set.instMin β) (@PartialEquiv.target α β e)
            (@Set.preimage β α (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e)) s))) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not Bool.not (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                  (instDecidableEqBool a.not Bool.true))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.true)
                        (instDecidableEqBool a.not Bool.true))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                  (instDecidableEqBool a.not Bool.false))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                        (instDecidableEqBool a.not Bool.false))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool x.not.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool x.not.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool a.not.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) => instDecidableEqBool a.not.not a) a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool x.not.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool x.not.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool a.not.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) => instDecidableEqBool a.not.not a) a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true)) (by
  simp)

-- Relation.SymmGen.rfl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.SymmGen.rfl.h3 : ¬∀ {α : Type} {r : α → α → Prop} {a : α}, Relation.SymmGen r a a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0)) (by
  decide +kernel)

-- Function.Bijective.injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Bijective.injective.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- ENNReal.pow_lt_pow_left_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.pow_lt_pow_left_iff.h3 : ¬∀ {a b : ENNReal} {n : ℕ}, a ^ n < b ^ n ↔ a < b := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  simp)

-- ENNReal.pow_le_pow_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.pow_le_pow_left.h3 : ¬∀ {a b : ENNReal} {n : ℕ}, a ^ n ≤ b ^ n := fun hc_h => absurd (@hc_h (1) (0) (1)) (by
  simp)

-- ENNReal.div_lt_of_lt_mul', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_lt_of_lt_mul'.h3 : ¬∀ {a b c : ENNReal}, a / b < c := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- ENNReal.div_le_div_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_le_div_left.h2 : ¬∀ {a b : ENNReal} (c : ENNReal), c / b ≤ c / a := fun hc_h => absurd (@hc_h (1) (0) (1)) (by
  simp)

-- Function.surjective_iff_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.surjective_iff_isEmpty.h2 : ¬∀ {α β : Type} (f : α → β), Function.Surjective f ↔ IsEmpty β := fun hc_h => absurd (@hc_h (Bool) (Bool) (not : Bool → Bool)) (by
  (simp <;> decide))

-- ENNReal.div_le_of_le_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_le_of_le_mul.h3 : ¬∀ {a b c : ENNReal}, a / c ≤ b := fun hc_h => absurd (@hc_h (1) (0) (0)) (by
  simp)

-- Equiv.isEmpty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.isEmpty.h3 : ¬∀ {α β : Type} (e : α ≃ β), IsEmpty α := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1)) (by
  exact fun hc_c =>
    absurd (hc_c.false (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.mul_lt_of_lt_div, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_lt_of_lt_div.h3 : ¬∀ {a b c : ENNReal}, a * c < b := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- Or.rotate, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Or.rotate.h3 : ¬∀ {a b c : Prop}, b ∨ c ∨ a := fun hc_h => absurd (@hc_h (False) (False) (False)) (by
  decide +kernel)

-- Denumerable.isChain_cons_raise'_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Denumerable.isChain_cons_raise'_of_lt.h3 : ¬∀ (l : List ℕ) {m n : ℕ}, List.IsChain (fun (x1 x2 : ℕ) => x1 < x2) (m :: Denumerable.raise' l n) := fun hc_h => absurd (@hc_h ([0]) (0) (0)) (by
  decide +kernel)

-- ENNReal.mul_le_of_le_div, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_le_of_le_div.h3 : ¬∀ {a b c : ENNReal}, a * c ≤ b := fun hc_h => absurd (@hc_h (1) (0) (1)) (by
  simp)

-- ENNReal.div_le_of_le_mul', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.div_le_of_le_mul'.h3 : ¬∀ {a b c : ENNReal}, a / b ≤ c := fun hc_h => absurd (@hc_h (1) (0) (0)) (by
  simp)

-- Function.rightInverse_surjInv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.rightInverse_surjInv.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- Equiv.subtypeUnivEquiv_apply, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.subtypeUnivEquiv_apply.h2 : ¬∀ {α : Type} {p : α → Prop} (x : Subtype p) (x : α), p x := fun hc_h => absurd (@hc_h (Bool) (fun b => b = true : Bool → Prop) ((⟨Bool.true, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { b : Bool // b = Bool.true }))) (by
  decide +kernel)

-- ENNReal.mul_inv_cancel, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_inv_cancel.h1 : ¬∀ {a : ENNReal}, a ≠ ⊤ → a * a⁻¹ = 1 := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  simp)

-- ENNReal.mul_inv_cancel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_inv_cancel.h2 : ¬∀ {a : ENNReal}, a ≠ 0 → a * a⁻¹ = 1 := fun hc_h => absurd (@hc_h (⊤) (by
  decide)) (by
  simp)

-- ENNReal.HolderTriple.inv_inv_add_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderTriple.inv_inv_add_inv.h3 : ¬∀ (p q r : ENNReal), (p⁻¹ + q⁻¹)⁻¹ = r := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- ENNReal.HolderTriple.one_div_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderTriple.one_div_eq.h3 : ¬∀ (p q r : ENNReal), 1 / r = 1 / p + 1 / q := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- not_finite, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_finite.h1 : ¬∀ (α : Type) [inst : Finite α], False := fun hc_h => absurd (@hc_h (Bool) _) (by
  decide +kernel)

-- not_finite, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_finite.h2 : ¬∀ (α : Type) [inst : Infinite α], False := fun hc_h => absurd (@hc_h (ℕ) _) (by
  decide +kernel)

-- Infinite.false, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Infinite.false.h2 : ¬∀ {α : Type} [inst : Finite α], False := fun hc_h => absurd (@hc_h (Bool) _) (by
  decide +kernel)

-- SetRel.rfl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.rfl.h3 : ¬∀ {α : Type} (R : SetRel α α) {a : α}, (a, a) ∈ R := fun hc_h => absurd (@hc_h (ℕ) (∅) (0)) (by
  decide +kernel)

-- Finite.false, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finite.false.h2 : ¬∀ {α : Type} [inst : Infinite α], False := fun hc_h => absurd (@hc_h (ℕ) _) (by
  decide +kernel)

-- SetRel.refl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.refl.h2 : ¬∀ {α : Type} (R : SetRel α α) (a : α), (a, a) ∈ R := fun hc_h => absurd (@hc_h (ℕ) (∅) (0)) (by
  decide +kernel)

-- SetRel.self_subset_preimage, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.self_subset_preimage.h2 : ¬∀ {α : Type} {R : SetRel α α} (s : Set α), s ⊆ R.preimage s := fun hc_h => absurd (@hc_h (ℕ) (∅) ({n : ℕ | n = 0})) (by
  simp)

-- NNReal.mul_eq_mul_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.mul_eq_mul_left.h3 : ¬∀ {a b c : NNReal}, a * b = a * c ↔ b = c := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- or_congr_left', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.or_congr_left'.h3 : ¬∀ {c a b : Prop}, a ∨ c ↔ b ∨ c := fun hc_h => absurd (@hc_h (False) (True) (False)) (by
  decide +kernel)

-- PEquiv.injective_of_forall_isSome, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PEquiv.injective_of_forall_isSome.h3 : ¬∀ {α β : Type} {f : α ≃. β}, Function.Injective ⇑f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (⊥)) (by
  decide +kernel)

-- Function.isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.isEmpty.h2 : ¬∀ {α β : Type} (f : α → β), IsEmpty α := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.false (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- NNReal.HolderTriple.inv_nonneg, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.NNReal.HolderTriple.inv_nonneg.h3.gneg : ∀ {p q r : NNReal}, ¬p.HolderTriple q r → 0 ≤ p⁻¹ := by
  (intros; simp; done)
theorem HypCheckProof.NNReal.HolderTriple.inv_nonneg.h3 : ∀ {p : NNReal} {q r : NNReal}, 0 ≤ p⁻¹ := by
  intro hc_x0 hc_x1 hc_x2
  exact Classical.byCases (fun hc_h => @NNReal.HolderTriple.inv_nonneg hc_x0 hc_x1 hc_x2 hc_h) (fun hc_hn => @HypCheckProof.NNReal.HolderTriple.inv_nonneg.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn)

-- NNReal.HolderTriple.one_div_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.one_div_pos.h3 : ¬∀ {p : NNReal} {q r : NNReal}, 0 < 1 / p := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- NNReal.HolderTriple.inv_nonneg', hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.NNReal.HolderTriple.inv_nonneg'.h3.gneg : ∀ {p q r : NNReal}, ¬p.HolderTriple q r → 0 ≤ r⁻¹ := by
  (intros; simp; done)
theorem HypCheckProof.NNReal.HolderTriple.inv_nonneg'.h3 : ∀ {p q : NNReal} {r : NNReal}, 0 ≤ r⁻¹ := by
  intro hc_x0 hc_x1 hc_x2
  exact Classical.byCases (fun hc_h => @NNReal.HolderTriple.inv_nonneg' hc_x0 hc_x1 hc_x2 hc_h) (fun hc_hn => @HypCheckProof.NNReal.HolderTriple.inv_nonneg'.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn)

-- Real.HolderTriple.lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.HolderTriple.lt.h3 : ¬∀ {p : ℝ} {q : ℝ} {r : ℝ}, r < p := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ })) (by
  simp)

-- NNReal.HolderTriple.inv_ne_zero', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.inv_ne_zero'.h3 : ¬∀ {p q : NNReal} {r : NNReal}, r⁻¹ ≠ 0 := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- NNReal.HolderTriple.one_div_ne_zero', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.one_div_ne_zero'.h3 : ¬∀ {p q : NNReal} {r : NNReal}, 1 / r ≠ 0 := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- NNReal.HolderTriple.one_div_nonneg', hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.NNReal.HolderTriple.one_div_nonneg'.h3.gneg : ∀ {p q r : NNReal}, ¬p.HolderTriple q r → 0 ≤ 1 / r := by
  (intros; simp; done)
theorem HypCheckProof.NNReal.HolderTriple.one_div_nonneg'.h3 : ∀ {p q : NNReal} {r : NNReal}, 0 ≤ 1 / r := by
  intro hc_x0 hc_x1 hc_x2
  exact Classical.byCases (fun hc_h => @NNReal.HolderTriple.one_div_nonneg' hc_x0 hc_x1 hc_x2 hc_h) (fun hc_hn => @HypCheckProof.NNReal.HolderTriple.one_div_nonneg'.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn)

-- NNReal.HolderTriple.inv_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.inv_ne_zero.h3 : ¬∀ {p : NNReal} {q r : NNReal}, p⁻¹ ≠ 0 := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- NNReal.HolderTriple.inv_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.inv_pos.h3 : ¬∀ {p : NNReal} {q r : NNReal}, 0 < p⁻¹ := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- And.rotate, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.And.rotate.h3 : ¬∀ {a b c : Prop}, b ∧ c ∧ a := fun hc_h => absurd (@hc_h (True) (True) (False)) (by
  decide +kernel)

-- NNReal.HolderTriple.inv_sub_inv_eq_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.inv_sub_inv_eq_inv.h3 : ¬∀ {p q r : NNReal}, r⁻¹ - q⁻¹ = p⁻¹ := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- NNReal.HolderTriple.one_div_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.one_div_ne_zero.h3 : ¬∀ {p : NNReal} {q r : NNReal}, 1 / p ≠ 0 := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- NNReal.HolderTriple.inv_inv_add_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.inv_inv_add_inv.h3 : ¬∀ {p q r : NNReal}, (p⁻¹ + q⁻¹)⁻¹ = r := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- NNReal.HolderTriple.pos', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.pos'.h3 : ¬∀ {p q : NNReal} {r : NNReal}, 0 < r := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- NNReal.HolderTriple.ne_zero', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderTriple.ne_zero'.h3 : ¬∀ {p q : NNReal} {r : NNReal}, r ≠ 0 := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- Eq.heq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Eq.heq.h3 : ¬∀ {α : Type} {a b : α}, a ≍ b := fun hc_h => absurd (@hc_h (ℕ) (0) (1)) (by
  simp)

-- HEq.eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.HEq.eq.h3 : ¬∀ {α : Type} {a b : α}, a = b := fun hc_h => absurd (@hc_h (ℕ) (0) (1)) (by
  decide +kernel)

-- Function.Embedding.coe_sumSet, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.coe_sumSet.h3 : ¬∀ {α : Type} {s t : Set α}, Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- PartialEquiv.injective_symm_of_target_eq_univ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.injective_symm_of_target_eq_univ.h3 : ¬∀ {α β : Type} (e : PartialEquiv α β), Function.Injective ↑e.symm := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Inhabited.default)) (by
  decide +kernel)

-- Function.Embedding.sumSet_range, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.sumSet_range.h3 : ¬∀ {α : Type} {s t : Set α}, Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- PartialEquiv.surjective_symm_of_source_eq_univ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PartialEquiv.surjective_symm_of_source_eq_univ.h3 : Not
      (∀ {α β : Type} (e : PartialEquiv α β), @Function.Surjective β α (@PartialEquiv.toFun β α (@PartialEquiv.symm α β e))) := fun hc_h => absurd (@hc_h (Bool) (Bool) (@PartialEquiv.mk Bool Bool Bool.not (fun (x : Bool) => Bool.true)
      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            (fun (a : Bool) =>
                @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                  (instDecidableEqBool a.not Bool.false))
              a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x.not)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a.not)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  (fun (a : Bool) =>
                      @Set.decidableOfPred Bool a.not (fun (b : Bool) => @Eq Bool b Bool.false)
                        (instDecidableEqBool a.not Bool.false))
                    a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            @Set.decidableOfPred Bool Bool.true (fun (b : Bool) => @Eq Bool b Bool.true)
              (instDecidableEqBool Bool.true Bool.true))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) Bool.true)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  @Set.decidableOfPred Bool Bool.true (fun (b : Bool) => @Eq Bool b Bool.true)
                    (instDecidableEqBool Bool.true Bool.true)))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
            @Eq Bool Bool.true x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
              @Eq Bool Bool.true x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
              @Eq Bool Bool.true a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
            instDecidableEqBool Bool.true a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                  @Eq Bool Bool.true x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) x →
                    @Eq Bool Bool.true x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                    @Eq Bool Bool.true a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.true) (instDecidableEqBool a Bool.true))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) a) =>
                  instDecidableEqBool Bool.true a))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true
        (∀ ⦃x : Bool⦄,
          @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
            @Eq Bool Bool.true.not x)
        (@Bool.instDecidableForallOfDecidablePred
          (fun (x : Bool) =>
            @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
              @Eq Bool Bool.true.not x)
          fun (a : Bool) =>
          @forall_prop_decidable
            (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
              (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
            (fun
                (a_1 :
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
              @Eq Bool Bool.true.not a)
            (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
            fun
              (h :
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                  (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
            instDecidableEqBool Bool.true.not a)
        (@id
          (@Eq Bool
            (@Decidable.decide
              (∀ ⦃x : Bool⦄,
                @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                  @Eq Bool Bool.true.not x)
              (@Bool.instDecidableForallOfDecidablePred
                (fun (x : Bool) =>
                  @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                      (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) x →
                    @Eq Bool Bool.true.not x)
                fun (a : Bool) =>
                @forall_prop_decidable
                  (@Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                    (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a)
                  (fun
                      (a_1 :
                        @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                          (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                    @Eq Bool Bool.true.not a)
                  (@Set.decidableOfPred Bool a (fun (b : Bool) => @Eq Bool b Bool.false) (instDecidableEqBool a Bool.false))
                  fun
                    (h :
                      @Membership.mem Bool (Set Bool) (@Set.instMembership Bool)
                        (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false) a) =>
                  instDecidableEqBool Bool.true.not a))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- NNReal.eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.eq.h2 : ¬∀ {n m : NNReal}, n = m := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- ENNReal.HolderConjugate.ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderConjugate.ne_zero.h2 : ¬∀ (p q : ENNReal), p ≠ 0 := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- ENNReal.HolderConjugate.one_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderConjugate.one_le.h2 : ¬∀ (p q : ENNReal), 1 ≤ p := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- ENNReal.HolderConjugate.inv_add_inv_eq_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.HolderConjugate.inv_add_inv_eq_one.h2 : ¬∀ (p q : ENNReal), p⁻¹ + q⁻¹ = 1 := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Function.Involutive.leftInverse, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Involutive.leftInverse.h2 : ¬∀ {α : Type} {f : α → α}, Function.LeftInverse f f := fun hc_h => absurd (@hc_h (Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- ExistsUnique.exists, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ExistsUnique.exists.h2 : ¬∀ {α : Type} {p : α → Prop}, ∃ (x : α), p x := fun hc_h => absurd (@hc_h (ℕ) (fun _ => False : ℕ → Prop)) (by
  simp)

-- Iff.not_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iff.not_right.h2 : ¬∀ {a b : Prop}, a ↔ ¬b := fun hc_h => absurd (@hc_h (True) (True)) (by
  decide +kernel)

-- SignType.zpow_odd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignType.zpow_odd.h2 : ¬∀ (s : SignType) {z : ℤ}, s ^ z = s := fun hc_h => absurd (@hc_h (SignType.zero) (0)) (by
  decide +kernel)

-- SignType.pow_odd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignType.pow_odd.h2 : ¬∀ (s : SignType) {n : ℕ}, s ^ n = s := fun hc_h => absurd (@hc_h (SignType.zero) (0)) (by
  decide +kernel)

-- ENNReal.ofNat_lt_ofReal, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofNat_lt_ofReal.h1 : ¬∀ {n : ℕ} {r : ℝ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h (0) ({ cauchy := 0 : ℝ })) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- isSymmOp_of_isCommutative, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.isSymmOp_of_isCommutative.h2 : ¬∀ (α : Type) (op : α → α → α), IsSymmOp op := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.symm_op (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- NNReal.iSup_empty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.iSup_empty.h1 : ¬∀ {ι : Type} (f : ι → NNReal), ⨆ (i : ι), f i = 0 := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => 1)) (by
  simp)

-- finSumNatEquiv_symm_apply_of_ge, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finSumNatEquiv_symm_apply_of_ge.h2 : ¬∀ {n i : ℕ}, (finSumNatEquiv n).symm i = Sum.inr (i - n) := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Function.bijective_of_subsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.bijective_of_subsingleton.h1 : ¬∀ {α : Type} (f : α → α), Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- or_not_of_imp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.or_not_of_imp.h2 : ¬∀ {a b : Prop}, b ∨ ¬a := fun hc_h => absurd (@hc_h (True) (False)) (by
  decide +kernel)

-- ENNReal.ofReal_eq_ofNat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_eq_ofNat.h2 : ¬∀ {r : ℝ} {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Relation.SymmGen.instRefl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Relation.SymmGen.instRefl.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Std.Refl (Relation.SymmGen r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.refl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.nnreal_smul_lt_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.nnreal_smul_lt_top.h2 : ¬∀ {x : NNReal} {y : ENNReal}, x • y < ⊤ := fun hc_h => absurd (@hc_h (1) (⊤)) (by
  simp)

-- Function.instAntisymmSwapProp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instAntisymmSwapProp.h2 : ¬∀ {α : Type} (r : α → α → Prop), Std.Antisymm (Function.swap r) := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.antisymm (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- NNReal.le_inv_iff_mul_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.le_inv_iff_mul_le.h2 : ¬∀ {r p : NNReal}, r ≤ p⁻¹ ↔ r * p ≤ 1 := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- ENNReal.toNNReal_sub, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toNNReal_sub.h2 : ¬∀ {a b : ENNReal}, (a - b).toNNReal = a.toNNReal - b.toNNReal := fun hc_h => absurd (@hc_h (1) (⊤)) (by
  simp)

-- SetRel.instIsIrreflOfPredProdMatch_1PropOfIrrefl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SetRel.instIsIrreflOfPredProdMatch_1PropOfIrrefl.h2 : ¬∀ {α : Type} {R : α → α → Prop}, SetRel.IsIrrefl {(a, b) : α × α | R a b} := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.irrefl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.Infinite.not_finite, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.not_finite.h2 : ¬∀ {α : Type} {s : Set α}, ¬s.Finite := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- NNReal.inv_le_of_le_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.inv_le_of_le_mul.h2 : ¬∀ {r p : NNReal}, r⁻¹ ≤ p := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- Function.Involutive.injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Involutive.injective.h2 : ¬∀ {α : Type} {f : α → α}, Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- ENNReal.trichotomy₂, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.trichotomy₂.h2 : ¬∀ {p q : ENNReal},
        p = 0 ∧ q = 0 ∨
          p = 0 ∧ q = ⊤ ∨
            p = 0 ∧ 0 < q.toReal ∨ p = ⊤ ∧ q = ⊤ ∨ 0 < p.toReal ∧ q = ⊤ ∨ 0 < p.toReal ∧ 0 < q.toReal ∧ p.toReal ≤ q.toReal := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- NNReal.coe_sub, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.coe_sub.h2 : Not
      (∀ {r₁ r₂ : NNReal},
        @Eq Real (↑(@HSub.hSub NNReal NNReal NNReal (@instHSub NNReal NNReal.instSub) r₁ r₂))
          (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) ↑r₁ ↑r₂)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat NNReal (nat_lit 0) (@Zero.toOfNat0 NNReal NNReal.instZero)) (@OfNat.ofNat NNReal (nat_lit 1) (@One.toOfNat1 NNReal NNReal.instOne))) (by
  simp)

-- Real.ofNat_lt_toNNReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.ofNat_lt_toNNReal.h2 : ¬∀ {r : ℝ} {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.sub_lt_self_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.sub_lt_self_iff.h2 : ¬∀ {a b : ENNReal}, a - b < a ↔ 0 < a ∧ 0 < b := fun hc_h => absurd (@hc_h (⊤) (1)) (by
  simp)

-- Function.instTotalSwapProp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instTotalSwapProp.h2 : ¬∀ {α : Type} (r : α → α → Prop), Std.Total (Function.swap r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Prod.isEmpty_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.isEmpty_left.h2 : ¬∀ {α β : Type}, IsEmpty (α × β) := fun hc_h => absurd (@hc_h (ℕ) (ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.false ((0, 0) : ℕ × ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- IsEmpty.exists_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsEmpty.exists_iff.h1 : ¬∀ {α : Type} {p : α → Prop}, (∃ (a : α), p a) ↔ False := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop)) (by
  simp)

-- Real.toNNReal_lt_ofNat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toNNReal_lt_ofNat.h2 : ¬∀ {r : ℝ} {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.eq_inv_of_mul_eq_one_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.eq_inv_of_mul_eq_one_left.h2 : ¬∀ {a b : ENNReal}, a = b⁻¹ := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Sigma.isEmpty_left, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sigma.isEmpty_left.h1 : ¬∀ {α : Type} {E : α → Type}, IsEmpty (Sigma E) := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.false ((⟨0, 0⟩ : (_ : ℕ) × ℕ) : (_ : ℕ) × ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.le_of_forall_pos_nnreal_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_of_forall_pos_nnreal_lt.h2 : ¬∀ {x y : ENNReal}, x ≤ y := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- Function.instIsLinearOrderSwapProp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instIsLinearOrderSwapProp.h2 : ¬∀ {α : Type} (r : α → α → Prop), IsLinearOrder α (Function.swap r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.toIsPartialOrder.toIsPreorder.toRefl.refl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- peirce, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.peirce.h2 : ¬∀ (a b : Prop), a := fun hc_h => absurd (@hc_h (False) (True)) (by
  decide +kernel)

-- ENNReal.le_of_forall_nnreal_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.le_of_forall_nnreal_lt.h2 : ¬∀ {x y : ENNReal}, x ≤ y := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- NNReal.HolderConjugate.div_conj_eq_sub_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderConjugate.div_conj_eq_sub_one.h2 : ¬∀ {p q : NNReal}, p / q = p - 1 := fun hc_h => absurd (@hc_h (1) (1)) (by
  simp)

-- Function.instIsTransSwapProp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instIsTransSwapProp.h2 : ¬∀ {α : Type} (r : α → α → Prop), IsTrans α (Function.swap r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≠ b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.trans (0 : ℕ) (1 : ℕ) (0 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Complex.div_ofNat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Complex.div_ofNat.h2 : ¬∀ (z : ℂ) (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h ({ re := { cauchy := 0 : ℝ }, im := { cauchy := 0 : ℝ } : ℂ }) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.coe_lt_coe_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.coe_lt_coe_of_lt.h2 : Not
      (∀ {r q : NNReal},
        @LT.lt ENNReal (@Preorder.toLT ENNReal (@PartialOrder.toPreorder ENNReal ENNReal.instPartialOrder)) ↑r ↑q) := fun hc_h => absurd (@hc_h (@OfNat.ofNat NNReal (nat_lit 0) (@Zero.toOfNat0 NNReal NNReal.instZero)) (@OfNat.ofNat NNReal (nat_lit 0) (@Zero.toOfNat0 NNReal NNReal.instZero))) (by
  simp)

-- NNReal.HolderConjugate.inv_add_inv_ennreal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderConjugate.inv_add_inv_ennreal.h2 : Not
      (∀ {p q : NNReal},
        @Eq ENNReal
          (@HAdd.hAdd ENNReal ENNReal ENNReal (@instHAdd ENNReal ENNReal.instAdd) ↑(@Inv.inv NNReal NNReal.instInv p)
            ↑(@Inv.inv NNReal NNReal.instInv q))
          (@OfNat.ofNat ENNReal (nat_lit 1) (@One.toOfNat1 ENNReal ENNReal.instOne))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat NNReal (nat_lit 0) (@Zero.toOfNat0 NNReal NNReal.instZero)) (@OfNat.ofNat NNReal (nat_lit 0) (@Zero.toOfNat0 NNReal NNReal.instZero))) (by
  simp)

-- Denumerable.raise_lower, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Denumerable.raise_lower.h2 : ¬∀ {l : List ℕ} {n : ℕ}, Denumerable.raise (Denumerable.lower l n) n = l := fun hc_h => absurd (@hc_h ([0]) (1)) (by
  decide +kernel)

-- ENNReal.pow_ne_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.pow_ne_zero.h1 : ¬∀ {a : ENNReal} (n : ℕ), a ^ n ≠ 0 := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- ENNReal.mulRightOrderIso_apply, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mulRightOrderIso_apply.h1 : ¬∀ (a x : ENNReal), IsUnit a := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Function.Involutive.rightInverse, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Involutive.rightInverse.h2 : ¬∀ {α : Type} {f : α → α}, Function.RightInverse f f := fun hc_h => absurd (@hc_h (Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- of_not_imp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.of_not_imp.h2 : ¬∀ {a : Prop} {b : Prop}, a := fun hc_h => absurd (@hc_h (False) (True)) (by
  decide +kernel)

-- ENNReal.add_sSup, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.add_sSup.h2 : ¬∀ {s : Set ENNReal} {a : ENNReal}, a + SupSet.sSup s = ⨆ b ∈ s, a + b := fun hc_h => absurd (@hc_h (∅) (1)) (by
  simp)

-- ENNReal.mulRightOrderIso_symm_apply, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mulRightOrderIso_symm_apply.h1 : ¬∀ (a x : ENNReal), IsUnit a := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Function.Involutive.bijective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Involutive.bijective.h2 : ¬∀ {α : Type} {f : α → α}, Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- NNReal.HolderConjugate.mul_eq_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.HolderConjugate.mul_eq_add.h2 : ¬∀ {p q : NNReal}, p * q = p + q := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- ENNReal.inv_le_inv', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.inv_le_inv'.h2 : ¬∀ {a b : ENNReal}, b⁻¹ ≤ a⁻¹ := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- NNReal.le_of_forall_lt_one_mul_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.le_of_forall_lt_one_mul_le.h2 : ¬∀ {x y : NNReal}, x ≤ y := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- Iff.not_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Iff.not_left.h2 : ¬∀ {a b : Prop}, ¬a ↔ b := fun hc_h => absurd (@hc_h (True) (True)) (by
  decide +kernel)

-- Function.Involutive.comp_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Involutive.comp_self.h2 : ¬∀ {α : Type} {f : α → α}, f ∘ f = id := fun hc_h => absurd (@hc_h (Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- Subsingleton.forall₂_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subsingleton.forall₂_iff.h1 : ¬∀ {ι : Type} (P : ι → ι → Prop), (∀ (i j : ι), P i j) ↔ ∀ (i : ι), P i i := fun hc_h => absurd (@hc_h (Bool) (fun a b => a = b : Bool → Bool → Prop)) (by
  decide +kernel)

-- Function.Involutive.surjective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Involutive.surjective.h2 : ¬∀ {α : Type} {f : α → α}, Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- Function.instReflSwapProp, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.instReflSwapProp.h2 : ¬∀ {α : Type} (r : α → α → Prop), Std.Refl (Function.swap r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.refl (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.ofReal_lt_ofNat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_lt_ofNat.h2 : ¬∀ {p : ℝ} {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Real.lt_of_toNNReal_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.lt_of_toNNReal_lt.h2 : ¬∀ {r p : ℝ}, r < p := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) ({ cauchy := 0 : ℝ })) (by
  simp)

-- ENNReal.pow_ne_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.pow_ne_top.h2 : ¬∀ {a : ENNReal} {n : ℕ}, a ^ n ≠ ⊤ := fun hc_h => absurd (@hc_h (⊤) (1)) (by
  decide +kernel)

-- Complex.ofReal_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Complex.ofReal_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- IsEmpty.subsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsEmpty.subsingleton.h1 : ¬∀ {α : Type}, Subsingleton α := fun hc_h => absurd (@hc_h (ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.toReal_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toReal_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.ofReal_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.ofReal_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENat.toENNReal_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.toENNReal_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.cancel_of_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.cancel_of_lt.h1 : ¬∀ {a : ENNReal}, AddLECancellable a := fun hc_h => absurd (@hc_h (⊤)) (by
  simp)

-- subsingleton_of_not_nonempty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.subsingleton_of_not_nonempty.h1 : ¬∀ {α : Type}, Subsingleton α := fun hc_h => absurd (@hc_h (ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENNReal.coe_sInf, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.coe_sInf.h1 : Not
      (∀ {s : Set NNReal},
        @Eq ENNReal
          (↑(@InfSet.sInf NNReal
              (@ConditionallyCompletePartialOrderInf.toInfSet NNReal
                (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderInf NNReal
                  (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder NNReal
                    (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice NNReal
                      (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder NNReal
                        NNReal.instConditionallyCompleteLinearOrderBot)))))
              s))
          (⨅ (a : NNReal), ⨅ (_ : @Membership.mem NNReal (Set NNReal) (@Set.instMembership NNReal) s a), ↑a)) := fun hc_h => absurd (@hc_h (@EmptyCollection.emptyCollection (Set NNReal) (@Set.instEmptyCollection NNReal))) (by
  simp)

-- Classical.by_contradiction, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Classical.by_contradiction.h1 : ¬∀ {p : Prop}, p := fun hc_h => absurd (@hc_h (False)) (by
  decide +kernel)

-- ENNReal.Finiteness.inv_ne_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.Finiteness.inv_ne_top.h1 : ¬∀ {a : ENNReal}, a⁻¹ ≠ ⊤ := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Uncountable.of_not_small, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Uncountable.of_not_small.h1 : ¬∀ {α : Type}, Uncountable α := fun hc_h => absurd (@hc_h (ℕ)) (by
  simp)

-- ENNReal.top_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.top_pow.h1 : Not
      (∀ {n : Nat},
        @Eq ENNReal
          (@HPow.hPow ENNReal Nat ENNReal
            (@instHPow ENNReal Nat
              (@NPow.toPow ENNReal
                (@Monoid.toNPow ENNReal
                  (@Semiring.toMonoid ENNReal (@CommSemiring.toSemiring ENNReal ENNReal.instCommSemiring)))))
            (@Top.top ENNReal ENNReal.instTop) n)
          (@Top.top ENNReal ENNReal.instTop)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- instUncountableULift, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instUncountableULift.h1 : ¬∀ {β : Type}, Uncountable (ULift.{0, 0} β) := fun hc_h => absurd (@hc_h (ℕ)) (by
  simp)

-- instUncountablePLift, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instUncountablePLift.h1 : ¬∀ {α : Type}, Uncountable (PLift α) := fun hc_h => absurd (@hc_h (ℕ)) (by
  simp)

-- Real.nnabs_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.nnabs_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fact.elim, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fact.elim.h1 : ¬∀ {p : Prop}, p := fun hc_h => absurd (@hc_h (False)) (by
  decide +kernel)

-- Option.instUncountable, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.instUncountable.h1 : ¬∀ {α : Type}, Uncountable (Option α) := fun hc_h => absurd (@hc_h (ℕ)) (by
  simp)

-- ENNReal.top_div_of_ne_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.top_div_of_ne_top.h1 : ¬∀ {a : ENNReal}, ⊤ / a = ⊤ := fun hc_h => absurd (@hc_h (⊤)) (by
  simp)

-- ENNReal.top_mul, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.top_mul.h1 : ¬∀ {a : ENNReal}, ⊤ * a = ⊤ := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- ENNReal.mul_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mul_top.h1 : ¬∀ {a : ENNReal}, a * ⊤ = ⊤ := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- ENNReal.mulLeftOrderIso_toEquiv, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.mulLeftOrderIso_toEquiv.h1 : ¬∀ (a : ENNReal), IsUnit a := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- NNReal.inv_lt_one_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNReal.inv_lt_one_iff.h1 : ¬∀ {x : NNReal}, x⁻¹ < 1 ↔ 1 < x := fun hc_h => absurd (@hc_h (0)) (by
  simp)

