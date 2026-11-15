import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.inst : ¬1 • 1 % 2 ≤ 2 • 1 % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.prem0 : 1 ≤ 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.prem1 : 1 % 2 ≤ 1 % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.prem2 : 0 % 2 ≤ 1 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.NatModule M] {k₁ k₂ : Nat} {x y : M},
        k₁ ≤ k₂ → x ≤ y → 0 ≤ x → k₁ • x ≤ k₂ • y := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule) (1) (2) (1) (1) HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.prem0 HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.prem1 HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h4.prem2)

-- Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg, hypothesis 11: necessary
/- FAILED: 17:10: Unknown identifier `_proof_3` | 42:10: Unknown identifier `_proof_3`
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.inst : ¬1 • 1 ≤ 0 • 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.prem0 : 0 ≤ 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.prem1 : 1 ≤ 1 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.NatModule M]
        [inst_3 : Lean.Grind.OrderedAdd M] {k₁ k₂ : Nat} {x y : M}, k₁ ≤ k₂ → x ≤ y → k₁ • x ≤ k₂ • y := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => b ≤ a : LE Nat }) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) => @LE.le Nat instLENat b a) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule) (@Lean.Grind.OrderedAdd.mk (Nat) (@instHAdd Nat
      (@Lean.Grind.AddCommMonoid.toAdd Nat
        (@Lean.Grind.NatModule.toAddCommMonoid Nat
          (@Lean.Grind.Semiring.toNatModule Nat (@Lean.Grind.CommSemiring.toSemiring Nat Lean.Grind.instCommSemiringNat))))) (@LE.mk Nat fun (a b : Nat) => @LE.le Nat instLENat b a) (@Std.IsPreorder.mk Nat (@LE.mk Nat fun (a b : Nat) => @LE.le Nat instLENat b a)
      (fun (a : Nat) =>
        @Decidable.byContradiction (@LE.le Nat instLENat a a) (a.decLe a) fun (a_1 : Not (@LE.le Nat instLENat a a)) =>
          _proof_3 a a_1)
      fun (a b c : Nat) (a_1 : @LE.le Nat instLENat b a) (a_2 : @LE.le Nat instLENat c b) =>
      @Decidable.byContradiction (@LE.le Nat instLENat c a) (c.decLe a) fun (a_3 : Not (@LE.le Nat instLENat c a)) =>
        _proof_4 a b c a_1 a_2 a_3) (by (try dsimp only);   (intros; omega))) (0) (1) (1) (1) HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.prem0 HypCheckProof.Lean.Grind.OrderedAdd.nsmul_le_nsmul_of_le_of_le_of_nonneg.h11.prem1)
-/

-- Lean.Grind.Order.le_of_not_lt, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_of_not_lt.h3.inst : ¬1 % 2 ≤ 2 % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_of_not_lt.h3.prem0 : ¬2 < 1 := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_of_not_lt.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.IsLinearPreorder α] {a b : α}, ¬a < b → b ≤ a := fun hc_h => HypCheckProof.Lean.Grind.Order.le_of_not_lt.h3.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (instLTNat) (@Std.IsLinearPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (2) (1) HypCheckProof.Lean.Grind.Order.le_of_not_lt.h3.prem0)

-- Lean.Grind.Order.le_of_not_lt, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_of_not_lt.h4.inst : ¬0 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.le_of_not_lt.h4.prem0 : ¬0 < 0 := by
  decide
theorem HypCheckProof.Lean.Grind.Order.le_of_not_lt.h4 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α] {a b : α}, ¬a < b → b ≤ a := fun hc_h => HypCheckProof.Lean.Grind.Order.le_of_not_lt.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a < b : LE Nat }) (instLTNat) (@Std.LawfulOrderLT.mk (Nat) (instLTNat) (@LE.mk Nat fun (a b : Nat) => @LT.lt Nat instLTNat a b) (by (try dsimp only);   (intros; omega))) (0) (0) HypCheckProof.Lean.Grind.Order.le_of_not_lt.h4.prem0)

-- Lean.Grind.OrderedAdd.add_le_right_iff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_right_iff.h4.inst : ¬(0 % 2 ≤ 1 % 2 ↔ (1 + 0) % 2 ≤ (1 + 1) % 2) := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_right_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M] {a b : M} (c : M),
        a ≤ b ↔ c + a ≤ c + b := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_le_right_iff.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) (0) (1) (1))

-- Lean.Grind.PartialOrder.le_iff_lt_or_eq, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.PartialOrder.le_iff_lt_or_eq.h4.inst : ¬(0 < 0 ↔ 0 < 0 ∨ 0 = 0) := by
  decide
theorem HypCheckProof.Lean.Grind.PartialOrder.le_iff_lt_or_eq.h4 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α] {a b : α}, a ≤ b ↔ a < b ∨ a = b := fun hc_h => HypCheckProof.Lean.Grind.PartialOrder.le_iff_lt_or_eq.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a < b : LE Nat }) (instLTNat) (@Std.LawfulOrderLT.mk (Nat) (instLTNat) (@LE.mk Nat fun (a b : Nat) => @LT.lt Nat instLTNat a b) (by (try dsimp only);   (intros; omega))) (0) (0))

