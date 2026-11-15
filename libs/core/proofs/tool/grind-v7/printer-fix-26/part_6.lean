import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff.h4.inst : ¬(2 • 0 % 2 < 2 • 1 % 2 ↔ 0 < 2) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff.h4.prem0 : 0 % 2 < 1 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.NatModule M] [inst_3 : LT M]
        [inst : Std.LawfulOrderLT M] (k : Nat) {a b : M}, a < b → (k • a < k • b ↔ 0 < k) := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule) ({ lt := fun (a b : Nat) => a % 2 < b % 2 : LT Nat }) (@Std.LawfulOrderLT.mk (Nat) (@LT.mk Nat fun (a b : Nat) =>
      @LT.lt Nat instLTNat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega))) (2) (0) (1) HypCheckProof.Lean.Grind.OrderedAdd.nsmul_lt_nsmul_iff.h4.prem0)

