import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.OrderedAdd.add_lt_right, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right.h4.inst : ¬(1 + 0) % 2 < (1 + 1) % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right.h4.prem0 : 0 % 2 < 1 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M] [inst_3 : LT M]
        [inst : Std.LawfulOrderLT M] {a b : M} (c : M), a < b → c + a < c + b := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) ({ lt := fun (a b : Nat) => a % 2 < b % 2 : LT Nat }) (@Std.LawfulOrderLT.mk (Nat) (@LT.mk Nat fun (a b : Nat) =>
      @LT.lt Nat instLTNat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega))) (0) (1) (1) HypCheckProof.Lean.Grind.OrderedAdd.add_lt_right.h4.prem0)

-- Lean.Grind.LinearOrder.lt_of_not_le, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.LinearOrder.lt_of_not_le.h3.inst : ¬1 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.LinearOrder.lt_of_not_le.h3.prem0 : ¬1 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.LinearOrder.lt_of_not_le.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.IsLinearOrder α] {a b : α}, ¬a ≤ b → b < a := fun hc_h => HypCheckProof.Lean.Grind.LinearOrder.lt_of_not_le.h3.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => b ≤ a : LE Nat }) (instLTNat) (@Std.IsLinearOrder.mk (Nat) (@LE.mk Nat fun (a b : Nat) => @LE.le Nat instLENat b a) (@Std.IsPartialOrder.mk (Nat) (@LE.mk Nat fun (a b : Nat) => @LE.le Nat instLENat b a) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) => @LE.le Nat instLENat b a) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (0) (1) HypCheckProof.Lean.Grind.LinearOrder.lt_of_not_le.h3.prem0)

-- Lean.Grind.LinearOrder.lt_of_not_le, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.LinearOrder.lt_of_not_le.h4.inst : ¬0 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.LinearOrder.lt_of_not_le.h4.prem0 : ¬0 < 0 := by
  decide
theorem HypCheckProof.Lean.Grind.LinearOrder.lt_of_not_le.h4 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α] {a b : α}, ¬a ≤ b → b < a := fun hc_h => HypCheckProof.Lean.Grind.LinearOrder.lt_of_not_le.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a < b : LE Nat }) (instLTNat) (@Std.LawfulOrderLT.mk (Nat) (instLTNat) (@LE.mk Nat fun (a b : Nat) => @LT.lt Nat instLTNat a b) (by (try dsimp only);   (intros; omega))) (0) (0) HypCheckProof.Lean.Grind.LinearOrder.lt_of_not_le.h4.prem0)

