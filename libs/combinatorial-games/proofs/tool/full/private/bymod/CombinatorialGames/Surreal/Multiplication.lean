import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
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

-- _private.CombinatorialGames.Surreal.Multiplication.0.P3_of_lt_of_lt, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.P3_of_lt_of_lt.h9 : ¬∀ {x₁ x₂ y₁ y₂ : IGame.{0}} [inst : IGame.Numeric.{0} x₁] [inst : IGame.Numeric.{0} x₂] [inst : IGame.Numeric.{0} y₁]
        [inst : IGame.Numeric.{0} y₂], LT.lt.{1} x₁ x₂ → P3.{0} x₁ x₂ y₁ y₂ := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ _ _ (by
  simp)) (by
  nofun)

-- _private.CombinatorialGames.Surreal.Multiplication.0.P3_of_IH3, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.P3_of_IH3.h4 : ¬∀ {x₁ x₂ y₁ y₂ : IGame.{0}},
        (∀ (i : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} Player.left (Neg.neg.{1} x₁)) i →
              IH3.{0} (Neg.neg.{1} x₂) i (Neg.neg.{1} x₁) y₁ y₂) →
          LT.lt.{1} x₁ x₂ → P3.{0} x₁ x₂ y₁ y₂ := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp) (by
  simp)) (by
  nofun)

-- _private.CombinatorialGames.Surreal.Multiplication.0.P3_of_IH3, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.P3_of_IH3.h6 : ¬∀ {x₁ x₂ y₁ y₂ : IGame.{0}},
        (∀ (i : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left x₂) i → IH3.{0} x₁ i x₂ y₁ y₂) →
          (∀ (i : IGame.{0}),
              Membership.mem.{1, 1} (IGame.moves.{0} Player.left (Neg.neg.{1} x₁)) i →
                IH3.{0} (Neg.neg.{1} x₂) i (Neg.neg.{1} x₁) y₁ y₂) →
            P3.{0} x₁ x₂ y₁ y₂ := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp) (by
  simp)) (by
  nofun)

-- _private.CombinatorialGames.Surreal.Multiplication.0.P3_of_le_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.P3_of_le_left.h5 : ¬∀ {x₁ x₂ y₁ y₂ : IGame.{0}} (i : IGame.{0}), LE.le.{1} x₁ i → P3.{0} x₁ x₂ y₁ y₂ := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  rfl)) (by
  nofun)

