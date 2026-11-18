import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.CombinatorialGames.Surreal.Division.0.le_mulOption, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.le_mulOption.h7 : ¬∀ (x y : IGame.{0}) {a b : IGame.{0}} [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} a]
        [inst : IGame.Numeric.{0} b], LE.le.{1} y b → LE.le.{1} (HMul.hMul.{1, 1, 1} x b) (IGame.mulOption.{0} x y a b) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _ (by
  simp)) (by
  (game_cmp; done))

-- _private.CombinatorialGames.NatOrdinal.Basic.0.NatOrdinal.mul_add_lt₃', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.mul_add_lt₃'.h6 : ¬∀ {a b c a' b' c' : NatOrdinal.{0}},
        LT.lt.{1} b' b →
          LT.lt.{1} c' c →
            LT.lt.{1}
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b c))
                    (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b' c)))
                  (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b c')))
                (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b' c')))
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b c))
                    (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b' c)))
                  (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b c')))
                (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b' c'))) := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (0) (0) (by
  simp) (by
  simp)) (by
  simp)

-- _private.CombinatorialGames.NatOrdinal.Basic.0.NatOrdinal.mul_add_lt₃', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.mul_add_lt₃'.h7 : ¬∀ {a b c a' b' c' : NatOrdinal.{0}},
        LT.lt.{1} a' a →
          LT.lt.{1} c' c →
            LT.lt.{1}
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b c))
                    (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b' c)))
                  (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b c')))
                (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b' c')))
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b c))
                    (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b' c)))
                  (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b c')))
                (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b' c'))) := fun hc_h => absurd (@hc_h (1) (0) (1) (0) (0) (0) (by
  simp) (by
  simp)) (by
  simp)

-- _private.CombinatorialGames.NatOrdinal.Basic.0.NatOrdinal.mul_add_lt₃', hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.mul_add_lt₃'.h8 : ¬∀ {a b c a' b' c' : NatOrdinal.{0}},
        LT.lt.{1} a' a →
          LT.lt.{1} b' b →
            LT.lt.{1}
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b c))
                    (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b' c)))
                  (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b c')))
                (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b' c')))
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b c))
                    (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b' c)))
                  (HMul.hMul.{1, 1, 1} a' (HMul.hMul.{1, 1, 1} b c')))
                (HMul.hMul.{1, 1, 1} a (HMul.hMul.{1, 1, 1} b' c'))) := fun hc_h => absurd (@hc_h (1) (1) (0) (0) (0) (0) (by
  simp) (by
  simp)) (by
  simp)

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

-- _private.CombinatorialGames.Surreal.Multiplication.0.P1_of_IH, hypothesis 2: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.P1_of_IH.h2.gneg.{u} : ∀ {x y : IGame.{u}},
      (¬∀ (a : Args.{u}), ArgsRel.{u} a (Args.P1.{u} x y) → P124.{u} a) →
        ∀ [inst : IGame.Numeric.{u} x] [inst : IGame.Numeric.{u} y], IGame.Numeric.{u} (HMul.hMul.{u + 1, u + 1, u + 1} x y) := by
  (intros; infer_instance)
theorem HypCheckProof.P1_of_IH.h2.{u} : ∀ {x y : IGame.{u}} [inst : IGame.Numeric.{u} x] [inst : IGame.Numeric.{u} y],
      IGame.Numeric.{u} (HMul.hMul.{u + 1, u + 1, u + 1} x y) := by
  intro hc_x0 hc_x1 hc_x3 hc_x4
  exact Classical.byCases (fun hc_h => @P1_of_IH hc_x0 hc_x1 hc_h hc_x3 hc_x4) (fun hc_hn => @HypCheckProof.P1_of_IH.h2.gneg hc_x0 hc_x1 hc_hn hc_x3 hc_x4)

-- _private.CombinatorialGames.Nimber.SimplestExtension.Basic.0.Nimber.inv_lt_of_not_isField_aux, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.inv_lt_of_not_isField_aux.h1 : ¬∀ {x : Nimber.{0}},
        ¬Nimber.IsField.{0} x →
          LT.lt.{1} (Inv.inv.{1} x) x ∧ ∀ (y : Nimber.{0}), LT.lt.{1} y (Inv.inv.{1} x) → LT.lt.{1} (Inv.inv.{1} y) x := fun hc_h => absurd (@hc_h (0) (by
  aesop)) (by
  simp)

