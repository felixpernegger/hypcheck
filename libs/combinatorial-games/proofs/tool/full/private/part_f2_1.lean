import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.CombinatorialGames.Surreal.Division.0.numeric_option_inv, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.numeric_option_inv.h7.inst : Not IGame.star.{0}.Numeric := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.numeric_option_inv.h7.prem0 : IGame.Numeric.{0} (@OfNat.ofNat.{1} IGame.{0} (nat_lit 1) (@One.toOfNat1.{1} IGame.{0} IGame.instOne.{0})) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.numeric_option_inv.h7.prem1 : @LT.lt.{1} IGame.{0} (@Preorder.toLT.{1} IGame.{0} IGame.instPreorder.{0})
      (@OfNat.ofNat.{1} IGame.{0} (nat_lit 0) (@Zero.toOfNat0.{1} IGame.{0} IGame.instZero.{0}))
      (@OfNat.ofNat.{1} IGame.{0} (nat_lit 1) (@One.toOfNat1.{1} IGame.{0} IGame.instOne.{0})) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.numeric_option_inv.h7.prem2 : ∀ (y : IGame.{0}),
      @Membership.mem.{1, 1} IGame.{0} (Set.{1} IGame.{0}) (@Set.instMembership.{1} IGame.{0})
          (IGame.moves.{0} Player.left
            (@OfNat.ofNat.{1} IGame.{0} (nat_lit 1) (@One.toOfNat1.{1} IGame.{0} IGame.instOne.{0})))
          y →
        @LT.lt.{1} IGame.{0} (@Preorder.toLT.{1} IGame.{0} IGame.instPreorder.{0})
            (@OfNat.ofNat.{1} IGame.{0} (nat_lit 0) (@Zero.toOfNat0.{1} IGame.{0} IGame.instZero.{0})) y →
          (@Inv.inv.{1} IGame.{0} IGame.instInv.{0} y).Numeric := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.numeric_option_inv.h7.prem3 : ∀ (y : IGame.{0}),
      @Membership.mem.{1, 1} IGame.{0} (Set.{1} IGame.{0}) (@Set.instMembership.{1} IGame.{0})
          (IGame.moves.{0} Player.right
            (@OfNat.ofNat.{1} IGame.{0} (nat_lit 1) (@One.toOfNat1.{1} IGame.{0} IGame.instOne.{0})))
          y →
        (@Inv.inv.{1} IGame.{0} IGame.instInv.{0} y).Numeric := by
  simp
theorem HypCheckProof.numeric_option_inv.h7 : Not
      (∀ {x : IGame.{0}} [inst : x.Numeric],
        @LT.lt.{1} IGame.{0} (@Preorder.toLT.{1} IGame.{0} IGame.instPreorder.{0})
            (@OfNat.ofNat.{1} IGame.{0} (nat_lit 0) (@Zero.toOfNat0.{1} IGame.{0} IGame.instZero.{0})) x →
          (∀ (y : IGame.{0}),
              @Membership.mem.{1, 1} IGame.{0} (Set.{1} IGame.{0}) (@Set.instMembership.{1} IGame.{0})
                  (IGame.moves.{0} Player.left x) y →
                @LT.lt.{1} IGame.{0} (@Preorder.toLT.{1} IGame.{0} IGame.instPreorder.{0})
                    (@OfNat.ofNat.{1} IGame.{0} (nat_lit 0) (@Zero.toOfNat0.{1} IGame.{0} IGame.instZero.{0})) y →
                  (@Inv.inv.{1} IGame.{0} IGame.instInv.{0} y).Numeric) →
            (∀ (y : IGame.{0}),
                @Membership.mem.{1, 1} IGame.{0} (Set.{1} IGame.{0}) (@Set.instMembership.{1} IGame.{0})
                    (IGame.moves.{0} Player.right x) y →
                  (@Inv.inv.{1} IGame.{0} IGame.instInv.{0} y).Numeric) →
              ∀ (p : Player) (y : IGame.{0}), y.Numeric) := fun hc_h => HypCheckProof.numeric_option_inv.h7.inst (@hc_h (@OfNat.ofNat.{1} IGame.{0} (nat_lit 1) (@One.toOfNat1.{1} IGame.{0} IGame.instOne.{0})) HypCheckProof.numeric_option_inv.h7.prem0 HypCheckProof.numeric_option_inv.h7.prem1 HypCheckProof.numeric_option_inv.h7.prem2 HypCheckProof.numeric_option_inv.h7.prem3 (Player.left) (IGame.star.{0}))

