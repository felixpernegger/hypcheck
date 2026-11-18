import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.CombinatorialGames.Surreal.Multiplication.0.P3_of_lt_of_lt, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.P3_of_lt_of_lt.h9 : ¬∀ {x₁ x₂ y₁ y₂ : IGame.{0}} [inst : IGame.Numeric.{0} x₁] [inst : IGame.Numeric.{0} x₂] [inst : IGame.Numeric.{0} y₁]
        [inst : IGame.Numeric.{0} y₂], LT.lt.{1} x₁ x₂ → P3.{0} x₁ x₂ y₁ y₂ := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ _ _ (by
  simp)) (by
  nofun)

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

-- _private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.wpow_strictMono_aux, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.IGame.Numeric.wpow_strictMono_aux.h4.gneg.{u_1} : ∀ {x y : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} y],
      ¬IGame.Numeric.{u_1} (Wpow.wpow.{u_1 + 1} x) →
        ∀ [inst : IGame.Numeric.{u_1} (Wpow.wpow.{u_1 + 1} y)],
          (LT.lt.{u_1 + 1} x y →
              ∀ {r : ℝ},
                LT.lt.{0} 0 r →
                  LT.lt.{u_1 + 1} (HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} (↑r) (Wpow.wpow.{u_1 + 1} x))
                    (Wpow.wpow.{u_1 + 1} y)) ∧
            (LE.le.{u_1 + 1} x y → LE.le.{u_1 + 1} (Wpow.wpow.{u_1 + 1} x) (Wpow.wpow.{u_1 + 1} y)) := by
  (intros; solve_by_elim)
theorem HypCheckProof.IGame.Numeric.wpow_strictMono_aux.h4.{u_1} : ∀ {x y : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} y]
      [inst : IGame.Numeric.{u_1} (Wpow.wpow.{u_1 + 1} y)],
      (LT.lt.{u_1 + 1} x y →
          ∀ {r : ℝ},
            LT.lt.{0} 0 r →
              LT.lt.{u_1 + 1} (HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} (↑r) (Wpow.wpow.{u_1 + 1} x))
                (Wpow.wpow.{u_1 + 1} y)) ∧
        (LE.le.{u_1 + 1} x y → LE.le.{u_1 + 1} (Wpow.wpow.{u_1 + 1} x) (Wpow.wpow.{u_1 + 1} y)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x5
  exact Classical.byCases (fun hc_h => @IGame.Numeric.wpow_strictMono_aux hc_x0 hc_x1 hc_x2 hc_x3 hc_h hc_x5) (fun hc_hn => @HypCheckProof.IGame.Numeric.wpow_strictMono_aux.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn hc_x5)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.IGame.Numeric.wpow_strictMono_aux.h4.derivable.{u_1} : ∀ {x y : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} y]
      [inst : IGame.Numeric.{u_1} (Wpow.wpow.{u_1 + 1} y)], IGame.Numeric.{u_1} (Wpow.wpow.{u_1 + 1} x) := by
  (intros; infer_instance)

-- _private.CombinatorialGames.Surreal.Pow.0.IGame.Numeric.wpow_strictMono_aux, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.IGame.Numeric.wpow_strictMono_aux.h5.gneg.{u_1} : ∀ {x y : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} y]
      [inst : IGame.Numeric.{u_1} (Wpow.wpow.{u_1 + 1} x)],
      ¬IGame.Numeric.{u_1} (Wpow.wpow.{u_1 + 1} y) →
        (LT.lt.{u_1 + 1} x y →
            ∀ {r : ℝ},
              LT.lt.{0} 0 r →
                LT.lt.{u_1 + 1} (HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} (↑r) (Wpow.wpow.{u_1 + 1} x))
                  (Wpow.wpow.{u_1 + 1} y)) ∧
          (LE.le.{u_1 + 1} x y → LE.le.{u_1 + 1} (Wpow.wpow.{u_1 + 1} x) (Wpow.wpow.{u_1 + 1} y)) := by
  (intros; solve_by_elim)
theorem HypCheckProof.IGame.Numeric.wpow_strictMono_aux.h5.{u_1} : ∀ {x y : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} y]
      [inst : IGame.Numeric.{u_1} (Wpow.wpow.{u_1 + 1} x)],
      (LT.lt.{u_1 + 1} x y →
          ∀ {r : ℝ},
            LT.lt.{0} 0 r →
              LT.lt.{u_1 + 1} (HMul.hMul.{u_1 + 1, u_1 + 1, u_1 + 1} (↑r) (Wpow.wpow.{u_1 + 1} x))
                (Wpow.wpow.{u_1 + 1} y)) ∧
        (LE.le.{u_1 + 1} x y → LE.le.{u_1 + 1} (Wpow.wpow.{u_1 + 1} x) (Wpow.wpow.{u_1 + 1} y)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact Classical.byCases (fun hc_h => @IGame.Numeric.wpow_strictMono_aux hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_h) (fun hc_hn => @HypCheckProof.IGame.Numeric.wpow_strictMono_aux.h5.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_hn)
set_option maxHeartbeats 5000 in
theorem HypCheckProof.IGame.Numeric.wpow_strictMono_aux.h5.derivable.{u_1} : ∀ {x y : IGame.{u_1}} [inst : IGame.Numeric.{u_1} x] [inst : IGame.Numeric.{u_1} y]
      [inst : IGame.Numeric.{u_1} (Wpow.wpow.{u_1 + 1} x)], IGame.Numeric.{u_1} (Wpow.wpow.{u_1 + 1} y) := by
  (intros; infer_instance)

-- _private.CombinatorialGames.Game.IGame.0.IGame.le_trans', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.le_trans'.h3 : ¬∀ {x y z : IGame.{0}}, LE.le.{1} y z → LE.le.{1} x z := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  rfl)) (by
  simp)

-- _private.CombinatorialGames.Game.IGame.0.IGame.le_trans', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.le_trans'.h4 : ¬∀ {x y z : IGame.{0}}, LE.le.{1} x y → LE.le.{1} x z := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  rfl)) (by
  simp)

-- _private.CombinatorialGames.SignExpansion.Simplicity.0.Simplicity.exists_of_sSup_apply_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Simplicity.exists_of_sSup_apply_ne_zero.h3 : ¬∀ {s : Set.{1} Simplicity.{0}},
        IsChain.{1} (fun (x1 x2 : Simplicity.{0}) => LE.le.{1} x1 x2) s →
          ∀ {o : NatOrdinal.{0}}, ∃ (x : Simplicity.{0}), Membership.mem.{1, 1} s x ∧ Ne.{1} (x o) 0 := fun hc_h => absurd (@hc_h (EmptyCollection.emptyCollection.{1}) (by
  simp) (0)) (by
  nofun)

-- _private.CombinatorialGames.Surreal.Real.0.Real.toIGame_lt_mulOption, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toIGame_lt_mulOption.h4 : ¬∀ {x : ℝ} {q r s : ℚ}, LT.lt.{1} (↑(HMul.hMul.{0, 0, 0} x ↑q)) (IGame.mulOption.{0} ↑x ↑q ↑r ↑s) := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) (0) (0) (0)) (by
  simp)

-- _private.CombinatorialGames.Surreal.Division.0.main, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.main.h2 : ¬∀ {x : IGame.{0}} [inst : IGame.Numeric.{0} x],
        IGame.Numeric.{0} (Inv.inv.{1} x) ∧ HMul.hMul.{1, 1, 1} x (Inv.inv.{1} x) ≈ 1 := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _) (by
  (game_cmp; done))

