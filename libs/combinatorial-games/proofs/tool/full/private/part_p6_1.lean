import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

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

-- _private.CombinatorialGames.Surreal.Multiplication.0.P3_of_le_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.P3_of_le_left.h5 : ¬∀ {x₁ x₂ y₁ y₂ : IGame.{0}} (i : IGame.{0}), LE.le.{1} x₁ i → P3.{0} x₁ x₂ y₁ y₂ := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  rfl)) (by
  nofun)

-- _private.CombinatorialGames.SignExpansion.Simplicity.0.WithTop.isGLB_of_coe_preimage, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithTop.isGLB_of_coe_preimage.h4 : ¬∀ {α : Type} [inst : PartialOrder α] {x : α} {s : Set (WithTop α)}, IsGLB (WithTop.some ⁻¹' s) x → IsGLB s ↑x := fun hc_h => absurd (@hc_h (Bool) (Bool.instPartialOrder) (Bool.true) (∅) (by
  simp)) (by
  simp)

-- _private.CombinatorialGames.SignExpansion.Simplicity.0.WithTop.isGLB_of_coe_preimage, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithTop.isGLB_of_coe_preimage.h5 : ¬∀ {α : Type} [inst : PartialOrder α] {x : α} {s : Set (WithTop α)}, (∃ (y : α), ↑y ∈ s) → IsGLB s ↑x := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) (1) (⊤) (by
  simp)) (by
  simp)

-- _private.CombinatorialGames.SignExpansion.Simplicity.0.WithTop.isLUB_of_coe_preimage, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithTop.isLUB_of_coe_preimage.h5 : ¬∀ {α : Type} [inst : PartialOrder α] {x : α} {s : Set (WithTop α)}, ⊤ ∉ s → IsLUB s ↑x := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) (1) (∅) (by
  decide)) (by
  simp)

