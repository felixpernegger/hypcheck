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

