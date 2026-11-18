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

-- _private.CombinatorialGames.Surreal.Division.0.mulOption_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.mulOption_le.h7 : ¬∀ (x y : IGame.{0}) {a b : IGame.{0}} [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} a]
        [inst : IGame.Numeric.{0} b], LE.le.{1} b y → LE.le.{1} (IGame.mulOption.{0} x y a b) (HMul.hMul.{1, 1, 1} x b) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ _ (by
  simp)) (by
  simp)

-- _private.CombinatorialGames.Surreal.Division.0.le_mulOption, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.le_mulOption.h7 : ¬∀ (x y : IGame.{0}) {a b : IGame.{0}} [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} a]
        [inst : IGame.Numeric.{0} b], LE.le.{1} y b → LE.le.{1} (HMul.hMul.{1, 1, 1} x b) (IGame.mulOption.{0} x y a b) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _ (by
  simp)) (by
  (game_cmp; done))

-- _private.CombinatorialGames.Surreal.Division.0.one_neg_mul_invOption, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.one_neg_mul_invOption.h6.gneg.{u_1} : ∀ (x : IGame.{u_1}) {y : IGame.{u_1}},
      HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1 →
        ∀ (a : IGame.{u_1}) [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} y],
          ¬IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y) →
            ∀ [inst : IGame.Numeric.{u_1} a],
              HSub.hSub.{u_1 + 1, u_1 + 1, u_1 + 1} 1
                  (HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} x (IGame.invOption.{u_1} x y a)) ≈
                HDiv.hDiv.{u_1 + 1, u_1 + 1, u_1 + 1}
                  (HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (HSub.hSub.{u_1 + 1, u_1 + 1, u_1 + 1} 1 (HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} x a))
                    (HSub.hSub.{u_1 + 1, u_1 + 1, u_1 + 1} y x))
                  y := by
  (intros; solve_by_elim)
theorem HypCheckProof.one_neg_mul_invOption.h6.{u_1} : ∀ (x : IGame.{u_1}) {y : IGame.{u_1}},
      HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1 →
        ∀ (a : IGame.{u_1}) [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} y] [inst : IGame.Numeric.{u_1} a],
          HSub.hSub.{u_1 + 1, u_1 + 1, u_1 + 1} 1 (HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} x (IGame.invOption.{u_1} x y a)) ≈
            HDiv.hDiv.{u_1 + 1, u_1 + 1, u_1 + 1}
              (HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1}
                (HSub.hSub.{u_1 + 1, u_1 + 1, u_1 + 1} 1 (HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} x a))
                (HSub.hSub.{u_1 + 1, u_1 + 1, u_1 + 1} y x))
              y := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x7
  exact Classical.byCases (fun hc_h => @one_neg_mul_invOption hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_h hc_x7) (fun hc_hn => @HypCheckProof.one_neg_mul_invOption.h6.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_hn hc_x7)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.one_neg_mul_invOption.h6.derivable.{u_1} : ∀ (x : IGame.{u_1}) {y : IGame.{u_1}},
      HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1 →
        ∀ (a : IGame.{u_1}) [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} y] [inst : IGame.Numeric.{u_1} a],
          IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y) := by
  (intros; infer_instance)

-- _private.CombinatorialGames.Surreal.Division.0.numeric_inv, hypothesis 2: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.numeric_inv.h2.gneg.{u_1} : ∀ {x : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x],
      ¬LT.lt.{u_1 + 1} 0 x →
        (∀ (y : IGame.{u_1}),
            Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
              LT.lt.{u_1 + 1} 0 y → IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
          (∀ (y : IGame.{u_1}),
              Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
            (∀ (y : IGame.{u_1}),
                Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
                  LT.lt.{u_1 + 1} 0 y → HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
              (∀ (y : IGame.{u_1}),
                  Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                    HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
                IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} x) := by
  (intros; infer_instance)
theorem HypCheckProof.numeric_inv.h2.{u_1} : ∀ {x : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x],
      (∀ (y : IGame.{u_1}),
          Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
            LT.lt.{u_1 + 1} 0 y → IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
        (∀ (y : IGame.{u_1}),
            Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
              IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
          (∀ (y : IGame.{u_1}),
              Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
                LT.lt.{u_1 + 1} 0 y → HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
            (∀ (y : IGame.{u_1}),
                Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                  HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
              IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} x) := by
  intro hc_x0 hc_x1 hc_x3 hc_x4 hc_x5 hc_x6
  exact Classical.byCases (fun hc_h => @numeric_inv hc_x0 hc_x1 hc_h hc_x3 hc_x4 hc_x5 hc_x6) (fun hc_hn => @HypCheckProof.numeric_inv.h2.gneg hc_x0 hc_x1 hc_hn hc_x3 hc_x4 hc_x5 hc_x6)

-- _private.CombinatorialGames.Surreal.Division.0.numeric_inv, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.numeric_inv.h3.gneg.{u_1} : ∀ {x : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x],
      LT.lt.{u_1 + 1} 0 x →
        (¬∀ (y : IGame.{u_1}),
              Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
                LT.lt.{u_1 + 1} 0 y → IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
          (∀ (y : IGame.{u_1}),
              Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
            (∀ (y : IGame.{u_1}),
                Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
                  LT.lt.{u_1 + 1} 0 y → HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
              (∀ (y : IGame.{u_1}),
                  Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                    HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
                IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} x) := by
  (intros; infer_instance)
theorem HypCheckProof.numeric_inv.h3.{u_1} : ∀ {x : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x],
      LT.lt.{u_1 + 1} 0 x →
        (∀ (y : IGame.{u_1}),
            Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
              IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
          (∀ (y : IGame.{u_1}),
              Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
                LT.lt.{u_1 + 1} 0 y → HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
            (∀ (y : IGame.{u_1}),
                Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                  HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
              IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} x) := by
  intro hc_x0 hc_x1 hc_x2 hc_x4 hc_x5 hc_x6
  exact Classical.byCases (fun hc_h => @numeric_inv hc_x0 hc_x1 hc_x2 hc_h hc_x4 hc_x5 hc_x6) (fun hc_hn => @HypCheckProof.numeric_inv.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4 hc_x5 hc_x6)

-- _private.CombinatorialGames.Surreal.Division.0.numeric_inv, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.numeric_inv.h4.gneg.{u_1} : ∀ {x : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x],
      LT.lt.{u_1 + 1} 0 x →
        (∀ (y : IGame.{u_1}),
            Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
              LT.lt.{u_1 + 1} 0 y → IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
          (¬∀ (y : IGame.{u_1}),
                Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                  IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
            (∀ (y : IGame.{u_1}),
                Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
                  LT.lt.{u_1 + 1} 0 y → HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
              (∀ (y : IGame.{u_1}),
                  Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                    HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
                IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} x) := by
  (intros; infer_instance)
theorem HypCheckProof.numeric_inv.h4.{u_1} : ∀ {x : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x],
      LT.lt.{u_1 + 1} 0 x →
        (∀ (y : IGame.{u_1}),
            Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
              LT.lt.{u_1 + 1} 0 y → IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
          (∀ (y : IGame.{u_1}),
              Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
                LT.lt.{u_1 + 1} 0 y → HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
            (∀ (y : IGame.{u_1}),
                Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                  HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
              IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} x) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x5 hc_x6
  exact Classical.byCases (fun hc_h => @numeric_inv hc_x0 hc_x1 hc_x2 hc_x3 hc_h hc_x5 hc_x6) (fun hc_hn => @HypCheckProof.numeric_inv.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn hc_x5 hc_x6)

-- _private.CombinatorialGames.Surreal.Division.0.numeric_inv, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.numeric_inv.h5.gneg.{u_1} : ∀ {x : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x],
      LT.lt.{u_1 + 1} 0 x →
        (∀ (y : IGame.{u_1}),
            Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
              LT.lt.{u_1 + 1} 0 y → IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
          (∀ (y : IGame.{u_1}),
              Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
            (¬∀ (y : IGame.{u_1}),
                  Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
                    LT.lt.{u_1 + 1} 0 y → HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
              (∀ (y : IGame.{u_1}),
                  Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                    HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
                IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} x) := by
  (intros; infer_instance)
theorem HypCheckProof.numeric_inv.h5.{u_1} : ∀ {x : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x],
      LT.lt.{u_1 + 1} 0 x →
        (∀ (y : IGame.{u_1}),
            Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
              LT.lt.{u_1 + 1} 0 y → IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
          (∀ (y : IGame.{u_1}),
              Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
            (∀ (y : IGame.{u_1}),
                Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                  HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
              IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} x) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x6
  exact Classical.byCases (fun hc_h => @numeric_inv hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_h hc_x6) (fun hc_hn => @HypCheckProof.numeric_inv.h5.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_hn hc_x6)

-- _private.CombinatorialGames.Surreal.Division.0.numeric_inv, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.numeric_inv.h6.gneg.{u_1} : ∀ {x : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x],
      LT.lt.{u_1 + 1} 0 x →
        (∀ (y : IGame.{u_1}),
            Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
              LT.lt.{u_1 + 1} 0 y → IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
          (∀ (y : IGame.{u_1}),
              Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
            (∀ (y : IGame.{u_1}),
                Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
                  LT.lt.{u_1 + 1} 0 y → HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
              (¬∀ (y : IGame.{u_1}),
                    Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                      HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
                IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} x) := by
  (intros; infer_instance)
theorem HypCheckProof.numeric_inv.h6.{u_1} : ∀ {x : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x],
      LT.lt.{u_1 + 1} 0 x →
        (∀ (y : IGame.{u_1}),
            Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
              LT.lt.{u_1 + 1} 0 y → IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
          (∀ (y : IGame.{u_1}),
              Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.right x) y →
                IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)) →
            (∀ (y : IGame.{u_1}),
                Membership.mem.{u_1 + 1, u_1 + 1} (IGame.moves.{u_1} Player.left x) y →
                  LT.lt.{u_1 + 1} 0 y → HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1) →
              IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} x) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact Classical.byCases (fun hc_h => @numeric_inv hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_h) (fun hc_hn => @HypCheckProof.numeric_inv.h6.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_hn)

-- _private.CombinatorialGames.Surreal.Division.0.mul_inv_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.mul_inv_self.h2 : ¬∀ {x : IGame.{0}} [inst : IGame.Numeric.{0} x],
        (∀ (y : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) y → LT.lt.{1} 0 y → IGame.Numeric.{0} (Inv.inv.{1} y)) →
          (∀ (y : IGame.{0}),
              Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) y → IGame.Numeric.{0} (Inv.inv.{1} y)) →
            (∀ (y : IGame.{0}),
                Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) y →
                  LT.lt.{1} 0 y → HMul.hMul.{1, 1, 1} y (Inv.inv.{1} y) ≈ 1) →
              (∀ (y : IGame.{0}),
                  Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) y → HMul.hMul.{1, 1, 1} y (Inv.inv.{1} y) ≈ 1) →
                HMul.hMul.{1, 1, 1} x (Inv.inv.{1} x) ≈ 1 := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _ (by
  simp) (by
  simp) (by
  aesop) (by
  aesop)) (by
  (game_cmp; done))

-- _private.CombinatorialGames.Surreal.Division.0.inv_pos', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.inv_pos'.h2 : ¬∀ {x : IGame.{0}} [inst : IGame.Numeric.{0} (Inv.inv.{1} x)], LT.lt.{1} 0 (Inv.inv.{1} x) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- _private.CombinatorialGames.Surreal.Division.0.instNumericInvOptionOfInvIGame, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.instNumericInvOptionOfInvIGame.h5.gneg.{u_1} : ∀ {x y a : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} y],
      ¬IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y) →
        ∀ [inst : IGame.Numeric.{u_1} a], IGame.Numeric.{u_1} (IGame.invOption.{u_1} x y a) := by
  (intros; infer_instance)
theorem HypCheckProof.instNumericInvOptionOfInvIGame.h5.{u_1} : ∀ {x y a : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} y] [inst : IGame.Numeric.{u_1} a],
      IGame.Numeric.{u_1} (IGame.invOption.{u_1} x y a) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x6
  exact Classical.byCases (fun hc_h => @instNumericInvOptionOfInvIGame hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_h hc_x6) (fun hc_hn => @HypCheckProof.instNumericInvOptionOfInvIGame.h5.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_hn hc_x6)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.instNumericInvOptionOfInvIGame.h5.derivable.{u_1} : ∀ {x y a : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} y] [inst : IGame.Numeric.{u_1} a],
      IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y) := by
  (intros; infer_instance)

-- _private.CombinatorialGames.Surreal.Division.0.main, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.main.h2 : ¬∀ {x : IGame.{0}} [inst : IGame.Numeric.{0} x],
        IGame.Numeric.{0} (Inv.inv.{1} x) ∧ HMul.hMul.{1, 1, 1} x (Inv.inv.{1} x) ≈ 1 := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _) (by
  (game_cmp; done))

-- _private.CombinatorialGames.Surreal.Division.0.mulOption_self_inv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.mulOption_self_inv.h2 : ¬∀ (x : IGame.{0}) {y : IGame.{0}} (a : IGame.{0}) [inst : IGame.Numeric.{0} x]
        [inst : IGame.Numeric.{0} (Inv.inv.{1} x)] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} (Inv.inv.{1} y)]
        [inst : IGame.Numeric.{0} a],
        IGame.mulOption.{0} x (Inv.inv.{1} x) y a ≈
          HAdd.hAdd.{1, 1, 1} 1 (HMul.hMul.{1, 1, 1} (HSub.hSub.{1, 1, 1} (Inv.inv.{1} x) (IGame.invOption.{0} x y a)) y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ _ _ _) (by
  (game_cmp; done))

-- _private.CombinatorialGames.Surreal.Division.0.mulOption_self_inv, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.mulOption_self_inv.h5.gneg.{u_1} : ∀ (x : IGame.{u_1}) {y : IGame.{u_1}},
      HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1 →
        ∀ (a : IGame.{u_1}) [inst : IGame.Numeric.{u_1} x],
          ¬IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} x) →
            ∀ [inst : IGame.Numeric.{u_1} y] [inst : IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)]
              [inst : IGame.Numeric.{u_1} a],
              IGame.mulOption.{u_1} x (Inv.inv.{u_1 + 1} x) y a ≈
                HAdd.hAdd.{u_1 + 1, u_1 + 1, u_1 + 1} 1
                  (HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (HSub.hSub.{u_1 + 1, u_1 + 1, u_1 + 1} (Inv.inv.{u_1 + 1} x) (IGame.invOption.{u_1} x y a)) y) := by
  (intros; solve_by_elim)
theorem HypCheckProof.mulOption_self_inv.h5.{u_1} : ∀ (x : IGame.{u_1}) {y : IGame.{u_1}},
      HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1 →
        ∀ (a : IGame.{u_1}) [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} y]
          [inst : IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)] [inst : IGame.Numeric.{u_1} a],
          IGame.mulOption.{u_1} x (Inv.inv.{u_1 + 1} x) y a ≈
            HAdd.hAdd.{u_1 + 1, u_1 + 1, u_1 + 1} 1
              (HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1}
                (HSub.hSub.{u_1 + 1, u_1 + 1, u_1 + 1} (Inv.inv.{u_1 + 1} x) (IGame.invOption.{u_1} x y a)) y) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x6 hc_x7 hc_x8
  exact Classical.byCases (fun hc_h => @mulOption_self_inv hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_h hc_x6 hc_x7 hc_x8) (fun hc_hn => @HypCheckProof.mulOption_self_inv.h5.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_hn hc_x6 hc_x7 hc_x8)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.mulOption_self_inv.h5.derivable.{u_1} : ∀ (x : IGame.{u_1}) {y : IGame.{u_1}},
      HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1 →
        ∀ (a : IGame.{u_1}) [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} y]
          [inst : IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y)] [inst : IGame.Numeric.{u_1} a],
          IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} x) := by
  (intros; infer_instance)

-- _private.CombinatorialGames.Surreal.Division.0.mulOption_self_inv, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.mulOption_self_inv.h7.gneg.{u_1} : ∀ (x : IGame.{u_1}) {y : IGame.{u_1}},
      HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1 →
        ∀ (a : IGame.{u_1}) [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} x)]
          [inst : IGame.Numeric.{u_1} y],
          ¬IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y) →
            ∀ [inst : IGame.Numeric.{u_1} a],
              IGame.mulOption.{u_1} x (Inv.inv.{u_1 + 1} x) y a ≈
                HAdd.hAdd.{u_1 + 1, u_1 + 1, u_1 + 1} 1
                  (HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1}
                    (HSub.hSub.{u_1 + 1, u_1 + 1, u_1 + 1} (Inv.inv.{u_1 + 1} x) (IGame.invOption.{u_1} x y a)) y) := by
  (intros; solve_by_elim)
theorem HypCheckProof.mulOption_self_inv.h7.{u_1} : ∀ (x : IGame.{u_1}) {y : IGame.{u_1}},
      HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1 →
        ∀ (a : IGame.{u_1}) [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} x)]
          [inst : IGame.Numeric.{u_1} y] [inst : IGame.Numeric.{u_1} a],
          IGame.mulOption.{u_1} x (Inv.inv.{u_1 + 1} x) y a ≈
            HAdd.hAdd.{u_1 + 1, u_1 + 1, u_1 + 1} 1
              (HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1}
                (HSub.hSub.{u_1 + 1, u_1 + 1, u_1 + 1} (Inv.inv.{u_1 + 1} x) (IGame.invOption.{u_1} x y a)) y) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x8
  exact Classical.byCases (fun hc_h => @mulOption_self_inv hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h hc_x8) (fun hc_hn => @HypCheckProof.mulOption_self_inv.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn hc_x8)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.mulOption_self_inv.h7.derivable.{u_1} : ∀ (x : IGame.{u_1}) {y : IGame.{u_1}},
      HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} y (Inv.inv.{u_1 + 1} y) ≈ 1 →
        ∀ (a : IGame.{u_1}) [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} x)]
          [inst : IGame.Numeric.{u_1} y] [inst : IGame.Numeric.{u_1} a], IGame.Numeric.{u_1} (Inv.inv.{u_1 + 1} y) := by
  (intros; infer_instance)

