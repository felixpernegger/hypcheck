import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- _private.CombinatorialGames.Game.Loopy.StoppingTime.0.LGame.le_of_finite, hypothesis 6: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.LGame.le_of_finite.h6.gneg.{u} : ∀ (p : Player) {x y : LGame.{u} → WithTop.{u + 1} NatOrdinal.{u}},
      Eq.{u + 2} ((LGame.stoppingTimeApprox.{u} p) x) x →
        Eq.{u + 2} ((LGame.stoppingTimeApprox.{u} p) y) y →
          ∀ {i : LGame.{u}}, ¬Ne.{u + 2} (y i) Top.top.{u + 1} → LE.le.{u + 1} (x i) (y i) := by
  (intros; simp_all; done)
theorem HypCheckProof.LGame.le_of_finite.h6.{u} : ∀ (p : Player) {x y : LGame.{u} → WithTop.{u + 1} NatOrdinal.{u}},
      Eq.{u + 2} ((LGame.stoppingTimeApprox.{u} p) x) x →
        Eq.{u + 2} ((LGame.stoppingTimeApprox.{u} p) y) y → ∀ {i : LGame.{u}}, LE.le.{u + 1} (x i) (y i) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact Classical.byCases (fun hc_h => @LGame.le_of_finite hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_h) (fun hc_hn => @HypCheckProof.LGame.le_of_finite.h6.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_hn)

-- _private.CombinatorialGames.Game.Loopy.StoppingTime.0.Monotone.iInf', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Monotone.iInf'.h6 : ¬∀ {α β ι : Type} [inst : Preorder α] [inst_1 : CompleteLattice β] {f : ι → α → β},
        Monotone fun (x : α) => ⨅ (i : ι), f i x := fun hc_h => absurd (@hc_h (Bool) (Bool) (ℕ) (Bool.instPartialOrder.toPreorder) (Bool.completeBooleanAlgebra.toCompleteLattice) (fun (a : ℕ) => Bool.not)) (by
  (simp <;> decide))

-- _private.CombinatorialGames.Game.Loopy.StoppingTime.0.Monotone.iSup', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Monotone.iSup'.h6 : ¬∀ {α β ι : Type} [inst : Preorder α] [inst_1 : CompleteLattice β] {f : ι → α → β},
        Monotone fun (x : α) => ⨆ (i : ι), f i x := fun hc_h => absurd (@hc_h (Bool) (Bool) (ℕ) (Bool.instPartialOrder.toPreorder) (Bool.completeBooleanAlgebra.toCompleteLattice) (fun (a : ℕ) => Bool.not)) (by
  (simp <;> decide))

-- _private.CombinatorialGames.Surreal.Leading.0.Surreal.leadingTerm_mono', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.leadingTerm_mono'.h3 : ¬∀ {x y : Surreal.{0}}, LE.le.{1} 0 x → LE.le.{1} (Surreal.leadingTerm.{0} x) (Surreal.leadingTerm.{0} y) := fun hc_h => absurd (@hc_h ((1 : Surreal) : Surreal.{0}) ((0 : Surreal) : Surreal.{0}) (by
  simp)) (by
  simp)

-- _private.CombinatorialGames.Surreal.Real.0.Real.mulOption_lt_toIGame, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.mulOption_lt_toIGame.h4 : ¬∀ {x : ℝ} {q r s : ℚ}, LT.lt.{1} (IGame.mulOption.{0} ↑x ↑q ↑r ↑s) ↑(HMul.hMul.{0, 0, 0} x ↑q) := fun hc_h => absurd (@hc_h ({ cauchy := 0 : ℝ }) (0) (0) (0)) (by
  simp)

-- _private.CombinatorialGames.Game.IGame.0.IGame.add_le_add_right', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.add_le_add_right'.h2 : ¬∀ {x y : IGame.{0}} (z : IGame.{0}), LE.le.{1} (HAdd.hAdd.{1, 1, 1} x z) (HAdd.hAdd.{1, 1, 1} y z) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- _private.CombinatorialGames.NatOrdinal.Pow.0.NatOrdinal.wpow_mul_natCast_add_of_lt_aux, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.wpow_mul_natCast_add_of_lt_aux.h2 : ¬∀ {x y : NatOrdinal.{0}} (n : ℕ),
        (∀ (z : NatOrdinal.{0}), LT.lt.{1} z (Wpow.wpow.{1} x) → LT.lt.{1} (HAdd.hAdd.{1, 1, 1} z y) (Wpow.wpow.{1} x)) ∧
          Eq.{2} (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} (Wpow.wpow.{1} x) ↑n) y)
            (NatOrdinal.of.{0}
              (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} (HPow.hPow.{1, 1, 1} Ordinal.omega0.{0} (NatOrdinal.val.{0} x)) ↑n)
                (NatOrdinal.val.{0} y))) := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  simp)

-- _private.CombinatorialGames.NatOrdinal.AddMonoidAlgebra.0.Ordinal.CNF.coeff_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordinal.CNF.coeff_lt.h1 : ¬∀ {b : Ordinal.{0}} (o e : Ordinal.{0}), LT.lt.{1} ((Ordinal.CNF.coeff.{0} b o) e) b := fun hc_h => absurd (@hc_h ((0 : Ordinal) : Ordinal.{0}) ((0 : Ordinal) : Ordinal.{0}) ((0 : Ordinal) : Ordinal.{0})) (by
  simp)

-- _private.CombinatorialGames.Surreal.Division.0.inv_pos', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.inv_pos'.h2 : ¬∀ {x : IGame.{0}} [inst : IGame.Numeric.{0} (Inv.inv.{1} x)], LT.lt.{1} 0 (Inv.inv.{1} x) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _) (by
  simp)

