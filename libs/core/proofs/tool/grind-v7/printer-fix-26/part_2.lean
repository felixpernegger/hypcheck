import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Lean.Grind.OrderedAdd.add_lt_left, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h4.inst : ¬(0 + 1) % 2 < (1 + 1) % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h4.prem0 : 0 % 2 < 1 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M] [inst_3 : LT M]
        [inst : Std.LawfulOrderLT M] {a b : M}, a < b → ∀ (c : M), a + c < b + c := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) ({ lt := fun (a b : Nat) => a % 2 < b % 2 : LT Nat }) (@Std.LawfulOrderLT.mk (Nat) (@LT.mk Nat fun (a b : Nat) =>
      @LT.lt Nat instLTNat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega))) (0) (1) HypCheckProof.Lean.Grind.OrderedAdd.add_lt_left.h4.prem0 (1))

-- Lean.Grind.CommRing.Expr.toLinQ_spec, hypothesis 6: necessary
/- FAILED: 2:106: failed to synthesize instance of type class
  Lean.Grind.Ring Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 2:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.toLinQ_spec.h6.inst : ¬(Lean.Grind.CommRing.PPoly.denoteG (Lean.Grind.CommRing.PPoly.linVal fun (a : Nat) => 0)
            (Lean.Grind.CommRing.Expr.toLinQ [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).fst =
          ↑(Lean.Grind.CommRing.Expr.toLinQ [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).snd *
            Lean.Grind.CommRing.Expr.denoteF (fun (a : Nat) => 0) (Lean.Grind.CommRing.Expr.var 0) ∧
        (Lean.Grind.CommRing.Expr.toLinQ [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).snd ≠ 0 ∧
          Lean.Grind.CommRing.PPoly.kron (2 ^ 0)
                (Lean.Grind.CommRing.Expr.toLinQ [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).fst =
              (Lean.Grind.CommRing.Expr.kronQLin_k 0 [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).fst ∧
            (Lean.Grind.CommRing.Expr.toLinQ [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).snd =
                (Lean.Grind.CommRing.Expr.kronQLin_k 0 [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).snd ∧
              (Lean.Grind.CommRing.Expr.toLinQ [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).fst.norm1 ≤
                  (Lean.Grind.CommRing.Expr.majQ_k [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).fst ∧
                (Lean.Grind.CommRing.Expr.toLinQ [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).snd =
                  (Lean.Grind.CommRing.Expr.majQ_k [(0, 0)] (Lean.Grind.CommRing.Expr.var 0)).snd) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.CommRing.Expr.toLinQ_spec.h6.prem0 : Lean.Grind.CommRing.Expr.degQL_k [(0, 0)] (Lean.Grind.CommRing.Expr.var 0) ≤ 1 := by
  decide
theorem HypCheckProof.Lean.Grind.CommRing.Expr.toLinQ_spec.h6 : ¬∀ {α : Type} [inst : Lean.Grind.Field α] [inst_1 : Lean.Grind.IsCharP α 0] (f : Nat → α) (K : Nat)
        (invs : Lean.Grind.CommRing.InvVars) (e : Lean.Grind.CommRing.Expr),
        Lean.Grind.CommRing.Expr.degQL_k invs e ≤ 1 →
          Lean.Grind.CommRing.PPoly.denoteG (Lean.Grind.CommRing.PPoly.linVal f)
                (Lean.Grind.CommRing.Expr.toLinQ invs e).fst =
              ↑(Lean.Grind.CommRing.Expr.toLinQ invs e).snd * Lean.Grind.CommRing.Expr.denoteF f e ∧
            (Lean.Grind.CommRing.Expr.toLinQ invs e).snd ≠ 0 ∧
              Lean.Grind.CommRing.PPoly.kron (2 ^ K) (Lean.Grind.CommRing.Expr.toLinQ invs e).fst =
                  (Lean.Grind.CommRing.Expr.kronQLin_k K invs e).fst ∧
                (Lean.Grind.CommRing.Expr.toLinQ invs e).snd = (Lean.Grind.CommRing.Expr.kronQLin_k K invs e).snd ∧
                  (Lean.Grind.CommRing.Expr.toLinQ invs e).fst.norm1 ≤ (Lean.Grind.CommRing.Expr.majQ_k invs e).fst ∧
                    (Lean.Grind.CommRing.Expr.toLinQ invs e).snd = (Lean.Grind.CommRing.Expr.majQ_k invs e).snd := fun hc_h => HypCheckProof.Lean.Grind.CommRing.Expr.toLinQ_spec.h6.inst (@hc_h (Rat) (Lean.Grind.instFieldRat) _ (fun (a : Nat) => 0) (0) ([(0, 0)]) (Lean.Grind.CommRing.Expr.var 0) HypCheckProof.Lean.Grind.CommRing.Expr.toLinQ_spec.h6.prem0)
-/

-- Lean.Grind.OrderedAdd.add_le_left, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_left.h4.inst : ¬(0 + 1) % 2 ≤ (1 + 1) % 2 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_left.h4.prem0 : 0 % 2 ≤ 1 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.add_le_left.h4 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.AddCommMonoid M] {a b : M},
        a ≤ b → ∀ (c : M), a + c ≤ b + c := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.add_le_left.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule.toAddCommMonoid) (0) (1) HypCheckProof.Lean.Grind.OrderedAdd.add_le_left.h4.prem0 (1))

-- Lean.Grind.OrderedAdd.nsmul_nonneg, hypothesis 7: necessary
/- FAILED: 11:10: Unknown identifier `_proof_4` | 33:10: Unknown identifier `_proof_4`
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_nonneg.h7.inst : ¬1 • 1 ≤ 0 := by
  decide
theorem HypCheckProof.Lean.Grind.OrderedAdd.nsmul_nonneg.h7 : ¬∀ {M : Type} [inst : LE M] [inst_1 : Std.IsPreorder M] [inst_2 : Lean.Grind.NatModule M]
        [inst_3 : Lean.Grind.OrderedAdd M] {k : Nat} {a : M}, 0 ≤ k • a := fun hc_h => HypCheckProof.Lean.Grind.OrderedAdd.nsmul_nonneg.h7.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => b ≤ a : LE Nat }) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) => @LE.le Nat instLENat b a) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (Lean.Grind.Semiring.toNatModule) (@Lean.Grind.OrderedAdd.mk (Nat) (@instHAdd Nat
      (@Lean.Grind.AddCommMonoid.toAdd Nat
        (@Lean.Grind.NatModule.toAddCommMonoid Nat
          (@Lean.Grind.Semiring.toNatModule Nat (@Lean.Grind.CommSemiring.toSemiring Nat Lean.Grind.instCommSemiringNat))))) (@LE.mk Nat fun (a b : Nat) => @LE.le Nat instLENat b a) (@Std.IsPreorder.mk Nat (@LE.mk Nat fun (a b : Nat) => @LE.le Nat instLENat b a)
      (fun (a : Nat) =>
        @Decidable.byContradiction (@LE.le Nat instLENat a a) (a.decLe a) fun (a_1 : Not (@LE.le Nat instLENat a a)) =>
          _proof_4 a a_1)
      fun (a b c : Nat) (a_1 : @LE.le Nat instLENat b a) (a_2 : @LE.le Nat instLENat c b) =>
      @Decidable.byContradiction (@LE.le Nat instLENat c a) (c.decLe a) fun (a_3 : Not (@LE.le Nat instLENat c a)) =>
        _proof_5 a b c a_1 a_2 a_3) (by (try dsimp only);   (intros; omega))) (1) (1))
-/

-- Lean.Grind.Order.lt_of_not_le, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le.h3.inst : ¬2 < 1 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le.h3.prem0 : ¬1 % 2 ≤ 2 % 2 := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.IsLinearPreorder α] {a b : α}, ¬a ≤ b → b < a := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_of_not_le.h3.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a % 2 ≤ b % 2 : LE Nat }) (instLTNat) (@Std.IsLinearPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@Std.IsPreorder.mk (Nat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; omega))) (by (try dsimp only);   (intros; omega))) (1) (2) HypCheckProof.Lean.Grind.Order.lt_of_not_le.h3.prem0)

-- Lean.Grind.Order.lt_of_not_le, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le.h4.inst : ¬0 < 0 := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le.h4.prem0 : ¬0 < 0 := by
  decide
theorem HypCheckProof.Lean.Grind.Order.lt_of_not_le.h4 : ¬∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Std.LawfulOrderLT α] {a b : α}, ¬a ≤ b → b < a := fun hc_h => HypCheckProof.Lean.Grind.Order.lt_of_not_le.h4.inst (@hc_h (Nat) ({ le := fun (a b : Nat) => a < b : LE Nat }) (instLTNat) (@Std.LawfulOrderLT.mk (Nat) (instLTNat) (@LE.mk Nat fun (a b : Nat) => @LT.lt Nat instLTNat a b) (by (try dsimp only);   (intros; omega))) (0) (0) HypCheckProof.Lean.Grind.Order.lt_of_not_le.h4.prem0)

