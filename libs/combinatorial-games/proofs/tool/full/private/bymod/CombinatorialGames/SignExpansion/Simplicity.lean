import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/
-- _private.CombinatorialGames.SignExpansion.Simplicity.0.Simplicity.exists_of_sSup_apply_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Simplicity.exists_of_sSup_apply_ne_zero.h3 : ¬∀ {s : Set.{1} Simplicity.{0}},
        IsChain.{1} (fun (x1 x2 : Simplicity.{0}) => LE.le.{1} x1 x2) s →
          ∀ {o : NatOrdinal.{0}}, ∃ (x : Simplicity.{0}), Membership.mem.{1, 1} s x ∧ Ne.{1} (x o) 0 := fun hc_h => absurd (@hc_h (EmptyCollection.emptyCollection.{1}) (by
  simp) (0)) (by
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

