import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.CombinatorialGames.Surreal.Pow.0.Surreal.exists_mk_wpow_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.exists_mk_wpow_eq.h2 : ¬∀ {x : IGame.{0}} [inst : IGame.Numeric.{0} x],
        ∃ (y : Subtype.{2} IGame.Numeric.{0}),
          Eq.{2} (ArchimedeanClass.mk.{1} (Wpow.wpow.{1} (Surreal.mk.{0} ↑y))) (ArchimedeanClass.mk.{1} (Surreal.mk.{0} x)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _) (by
  (simp <;> omega))

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

-- _private.CombinatorialGames.Surreal.Pow.0.Surreal.mk_lt_mk_of_ne', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.mk_lt_mk_of_ne'.h5 : ¬∀ {x : IGame.{0}} [inst : IGame.Numeric.{0} x],
        LT.lt.{1} 0 x →
          (∀ (y : IGame.{0}) (h : Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) y),
              have this := IGame.Numeric.of_mem_moves.{0} h;
              Ne.{2} (ArchimedeanClass.mk.{1} (Surreal.mk.{0} y)) (ArchimedeanClass.mk.{1} (Surreal.mk.{0} x))) →
            ∀ (y : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) y := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) _ (by
  simp) (by
  simp) ((0 : IGame) : IGame.{0})) (by
  simp)

