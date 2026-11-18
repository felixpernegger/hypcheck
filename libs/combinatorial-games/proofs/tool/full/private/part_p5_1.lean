import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

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

