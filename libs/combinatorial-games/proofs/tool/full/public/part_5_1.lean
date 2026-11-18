module
public import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- IGame.Numeric.mul_congr_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_congr_right.h6 : ¬∀ {x y₁ y₂ : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y₁] [inst : IGame.Numeric.{0} y₂],
        HMul.hMul.{1, 1, 1} x y₁ ≈ HMul.hMul.{1, 1, 1} x y₂ := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _) (by
  (game_cmp; done))

-- le_of_le_of_lt_of_lt, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.le_of_le_of_lt_of_lt.h7 : ¬∀ {α β : Type} [inst : PartialOrder α] [inst_1 : Preorder β] {x y : α} {f : α → β}, x ≤ y → f x ≤ f y := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Nat.instPartialOrder) (Bool.instPartialOrder.toPreorder) (0) (1) (fun n => n % 2 == 0 : ℕ → Bool) (by
  decide)) (by
  decide +kernel)

-- le_of_le_of_lt_of_lt, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.le_of_le_of_lt_of_lt.h8.inst : ¬(fun (n : ℕ) => n + 1) 1 ≤ (fun (n : ℕ) => n + 1) 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.le_of_le_of_lt_of_lt.h8.prem0 : 1 < 0 → (fun (n : ℕ) => n + 1) 1 < (fun (n : ℕ) => n + 1) 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.le_of_le_of_lt_of_lt.h8 : ¬∀ {α β : Type} [inst : PartialOrder α] [inst_1 : Preorder β] {x y : α} {f : α → β}, (x < y → f x < f y) → f x ≤ f y := fun hc_h => HypCheckProof.le_of_le_of_lt_of_lt.h8.inst (@hc_h (ℕ) (ℕ) (Nat.instPartialOrder) (Nat.instPreorder) (1) (0) (fun (n : ℕ) => n + 1) HypCheckProof.le_of_le_of_lt_of_lt.h8.prem0)

-- IGame.Numeric.mul_le_mul_iff_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_le_mul_iff_right.h6 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        LE.le.{1} (HMul.hMul.{1, 1, 1} x y) (HMul.hMul.{1, 1, 1} x z) ↔ LE.le.{1} y z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ _) (by
  simp)

-- IGame.equiv_of_exists_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.equiv_of_exists_le.h2 : ¬∀ {x y : IGame.{0}},
        (∀ (a : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) a →
              ∃ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) b ∧ LE.le.{1} b a) →
          (∀ (b : IGame.{0}),
              Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) b →
                ∃ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) a ∧ LE.le.{1} b a) →
            (∀ (b : IGame.{0}),
                Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) b →
                  ∃ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) a ∧ LE.le.{1} a b) →
              x ≈ y := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp) (by
  simp) (by
  simp)) (by
  (game_cmp; done))

-- IGame.equiv_of_exists_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.equiv_of_exists_le.h3 : ¬∀ {x y : IGame.{0}},
        (∀ (a : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) a →
              ∃ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) b ∧ LE.le.{1} a b) →
          (∀ (b : IGame.{0}),
              Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) b →
                ∃ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) a ∧ LE.le.{1} b a) →
            (∀ (b : IGame.{0}),
                Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) b →
                  ∃ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) a ∧ LE.le.{1} a b) →
              x ≈ y := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  simp) (by
  simp) (by
  simp)) (by
  (game_cmp; done))

-- IGame.equiv_of_exists_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.equiv_of_exists_le.h4 : ¬∀ {x y : IGame.{0}},
        (∀ (a : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) a →
              ∃ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) b ∧ LE.le.{1} a b) →
          (∀ (a : IGame.{0}),
              Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) a →
                ∃ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) b ∧ LE.le.{1} b a) →
            (∀ (b : IGame.{0}),
                Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) b →
                  ∃ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) a ∧ LE.le.{1} a b) →
              x ≈ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  simp) (by
  simp) (by
  simp)) (by
  (game_cmp; done))

-- IGame.equiv_of_exists_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.equiv_of_exists_le.h5 : ¬∀ {x y : IGame.{0}},
        (∀ (a : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) a →
              ∃ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) b ∧ LE.le.{1} a b) →
          (∀ (a : IGame.{0}),
              Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) a →
                ∃ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) b ∧ LE.le.{1} b a) →
            (∀ (b : IGame.{0}),
                Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) b →
                  ∃ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) a ∧ LE.le.{1} b a) →
              x ≈ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((-1 : IGame) : IGame.{0}) (by
  simp) (by
  simp) (by
  simp)) (by
  (game_cmp; done))

-- IGame.equiv_of_exists, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.equiv_of_exists.h2 : ¬∀ {x y : IGame.{0}},
        (∀ (a : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) a →
              ∃ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) b ∧ a ≈ b) →
          (∀ (b : IGame.{0}),
              Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) b →
                ∃ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) a ∧ a ≈ b) →
            (∀ (b : IGame.{0}),
                Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) b →
                  ∃ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) a ∧ a ≈ b) →
              x ≈ y := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp) (by
  simp) (by
  simp)) (by
  (game_cmp; done))

-- IGame.equiv_of_exists, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.equiv_of_exists.h3 : ¬∀ {x y : IGame.{0}},
        (∀ (a : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) a →
              ∃ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) b ∧ a ≈ b) →
          (∀ (b : IGame.{0}),
              Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) b →
                ∃ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) a ∧ a ≈ b) →
            (∀ (b : IGame.{0}),
                Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) b →
                  ∃ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) a ∧ a ≈ b) →
              x ≈ y := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  simp) (by
  simp) (by
  simp)) (by
  (game_cmp; done))

-- IGame.equiv_of_exists, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.equiv_of_exists.h4 : ¬∀ {x y : IGame.{0}},
        (∀ (a : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) a →
              ∃ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) b ∧ a ≈ b) →
          (∀ (a : IGame.{0}),
              Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) a →
                ∃ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) b ∧ a ≈ b) →
            (∀ (b : IGame.{0}),
                Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) b →
                  ∃ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) a ∧ a ≈ b) →
              x ≈ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  simp) (by
  simp) (by
  simp)) (by
  (game_cmp; done))

-- IGame.equiv_of_exists, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.equiv_of_exists.h5 : ¬∀ {x y : IGame.{0}},
        (∀ (a : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) a →
              ∃ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) b ∧ a ≈ b) →
          (∀ (a : IGame.{0}),
              Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) a →
                ∃ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) b ∧ a ≈ b) →
            (∀ (b : IGame.{0}),
                Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) b →
                  ∃ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) a ∧ a ≈ b) →
              x ≈ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((-1 : IGame) : IGame.{0}) (by
  simp) (by
  simp) (by
  simp)) (by
  (game_cmp; done))

-- IGame.Fits.surrealBirthday_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Fits.surrealBirthday_lt.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst_1 : IGame.Numeric.{0} y],
        ¬x ≈ y → LT.lt.{1} (Surreal.birthday.{0} (Surreal.mk.{0} y)) (Surreal.birthday.{0} (Surreal.mk.{0} x)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ (by
  (game_cmp; done))) (by
  simp)

-- IGame.Fits.surrealBirthday_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Fits.surrealBirthday_lt.h5 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst_1 : IGame.Numeric.{0} y],
        IGame.Fits.{0} x y → LT.lt.{1} (Surreal.birthday.{0} (Surreal.mk.{0} y)) (Surreal.birthday.{0} (Surreal.mk.{0} x)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ (by
  simp)) (by
  simp)

-- IGame.lf_of_lt_leftStop, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.lf_of_lt_leftStop.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Short.{0} x] [inst : IGame.Numeric.{0} y], ¬LE.le.{1} x y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _) (by
  simp)

-- Nimber.IsField.sqrt_le_of_not_perfectField, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.sqrt_le_of_not_perfectField.h2 : ¬∀ {x y : Nimber.{0}}, LE.le.{1} y (HPow.hPow.{1, 0, 1} x 2) → Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0) (0) (by
  simp)) (by
  nofun)

-- IGame.lt_of_leftStop_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.lt_of_leftStop_lt.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Short.{0} x] [inst : IGame.Numeric.{0} y], LT.lt.{1} x y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _) (by
  simp)

-- IGame.Fits.equiv_of_forall_moves, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Fits.equiv_of_forall_moves.h2 : ¬∀ {x y : IGame.{0}},
        (∀ (z : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) z →
              ∃ (w : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) w ∧ LE.le.{1} z w) →
          (∀ (z : IGame.{0}),
              Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) z →
                ∃ (w : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) w ∧ LE.le.{1} w z) →
            x ≈ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  simp) (by
  simp)) (by
  (game_cmp; done))

-- IGame.Numeric.inv_equiv_of_mul_eq_one, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.inv_equiv_of_mul_eq_one.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y], Inv.inv.{1} x ≈ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _) (by
  (simp <;> game_cmp <;> done))

-- IGame.Numeric.lt_of_not_ge, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.lt_of_not_ge.h2 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} y], ¬LE.le.{1} x y → LT.lt.{1} y x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) _ (by
  aesop)) (by
  simp)

-- IGame.Numeric.lt_of_not_ge, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.lt_of_not_ge.h3 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x], ¬LE.le.{1} x y → LT.lt.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) _ (by
  aesop)) (by
  simp)

-- IGame.Numeric.lt_of_not_ge, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.lt_of_not_ge.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y], LT.lt.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _) (by
  simp)

-- Surreal.toGame_ofSets, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.toGame_ofSets.h4 : ¬∀ (s t : Set.{1} Surreal.{0}) [inst : Small.{0, 1} ↑s] [inst : Small.{0, 1} ↑t] (x : Surreal.{0}),
        Membership.mem.{1, 1} s x → ∀ (y : Surreal.{0}), Membership.mem.{1, 1} t y → LT.lt.{1} x y := fun hc_h => absurd (@hc_h (({0} : Set Surreal) : Set.{1} Surreal.{0}) (({0} : Set Surreal) : Set.{1} Surreal.{0}) _ _) (by
  simp)

-- IGame.Impartial.ge_iff_equiv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.ge_iff_equiv.h2 : ¬∀ {x y : IGame.{0}} [hy : IGame.Impartial.{0} y], LE.le.{1} y x ↔ x ≈ y := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  (simp <;> game_cmp <;> done))

-- IGame.Impartial.ge_iff_equiv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.ge_iff_equiv.h3 : ¬∀ {x y : IGame.{0}} [hx : IGame.Impartial.{0} x], LE.le.{1} y x ↔ x ≈ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((-1 : IGame) : IGame.{0}) _) (by
  (simp <;> game_cmp <;> done))

-- IGame.Impartial.le_iff_equiv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.le_iff_equiv.h2 : ¬∀ {x y : IGame.{0}} [hy : IGame.Impartial.{0} y], LE.le.{1} x y ↔ x ≈ y := fun hc_h => absurd (@hc_h ((-1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  (simp <;> game_cmp <;> done))

-- IGame.Impartial.le_iff_equiv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.le_iff_equiv.h3 : ¬∀ {x y : IGame.{0}} [hx : IGame.Impartial.{0} x], LE.le.{1} x y ↔ x ≈ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _) (by
  (simp <;> game_cmp <;> done))

-- IGame.Impartial.not_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.not_lt.h2 : ¬∀ (x y : IGame.{0}) [hy : IGame.Impartial.{0} y], ¬LT.lt.{1} x y := fun hc_h => absurd (@hc_h ((-1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Impartial.not_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.not_lt.h3 : ¬∀ (x y : IGame.{0}) [hx : IGame.Impartial.{0} x], ¬LT.lt.{1} x y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.not_fuzzy, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.not_fuzzy.h2 : ¬∀ (x y : IGame.{0}) [inst : IGame.Numeric.{0} y], ¬x ‖ y := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.not_fuzzy, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.not_fuzzy.h3 : ¬∀ (x y : IGame.{0}) [inst : IGame.Numeric.{0} x], ¬x ‖ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) _) (by
  (simp <;> omega))

-- Surreal.Cut.leftSurreal_mem_of_sSup_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.leftSurreal_mem_of_sSup_eq.h3 : ¬∀ {s : Set.{1} Surreal.Cut.{0}} {x : Surreal.{0}} [inst : Small.{0, 1} ↑s],
        Membership.mem.{1, 1} s (Surreal.Cut.leftSurreal.{0} x) := fun hc_h => absurd (@hc_h (EmptyCollection.emptyCollection.{1}) ((0 : Surreal) : Surreal.{0}) _) (by
  decide +kernel)

-- IGame.lf_miny_of_not_nonneg_of_forall_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.lf_miny_of_not_nonneg_of_forall_le.h2 : ¬∀ {x a : IGame.{0}},
        (∀ (y : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) y → LE.le.{1} y a) →
          ¬LE.le.{1} (IGame.miny.{0} a) x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  (game_cmp; done))

-- IGame.fuzzy_tiny_of_birthday_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.fuzzy_tiny_of_birthday_le.h1 : ¬∀ {x o : IGame.{0}}, LE.le.{1} (NatOrdinal.toIGame.{0} (IGame.birthday.{0} x)) o → x ‖ IGame.tiny.{0} o := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  (game_cmp; done))

-- Dyadic.upper_le_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.upper_le_of_lt.h3 : ¬∀ {x y : Dyadic}, y.den ≤ x.den → x.upper ≤ y := fun hc_h => absurd (@hc_h (Dyadic.zero) (Dyadic.zero) (by
  decide)) (by
  decide +kernel)

-- Nimber.IsGroup.toAddSubgroup_lt_toAddSubgroup, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.toAddSubgroup_lt_toAddSubgroup.h2 : ¬∀ {x y : Nimber.{0}}, Nimber.IsGroup.{0} y → Nimber.IsGroup.{0} x := fun hc_h => absurd (@hc_h (0) (1) (by
  simp)) (by
  nofun)

-- Nimber.IsGroup.toAddSubgroup_lt_toAddSubgroup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.toAddSubgroup_lt_toAddSubgroup.h3 : ¬∀ {x y : Nimber.{0}}, Nimber.IsGroup.{0} x → Nimber.IsGroup.{0} y := fun hc_h => absurd (@hc_h (1) (0) (by
  simp)) (by
  nofun)

-- IGame.sub_left_mem_moves_sub, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.sub_left_mem_moves_sub.h3 : ¬∀ {p : Player} {x y : IGame.{0}} (z : IGame.{0}),
        Membership.mem.{1, 1} (IGame.moves.{0} (Neg.neg.{0} p) (HSub.hSub.{1, 1, 1} z y)) (HSub.hSub.{1, 1, 1} z x) := fun hc_h => absurd (@hc_h (Player.left : Player) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.sub_left_mem_moves_sub_neg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.sub_left_mem_moves_sub_neg.h3 : ¬∀ {p : Player} {x y : IGame.{0}} (z : IGame.{0}),
        Membership.mem.{1, 1} (IGame.moves.{0} p (HSub.hSub.{1, 1, 1} z y)) (HSub.hSub.{1, 1, 1} z x) := fun hc_h => absurd (@hc_h (Player.left : Player) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.add_left_mem_moves_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.add_left_mem_moves_add.h3 : ¬∀ {p : Player} {x y : IGame.{0}} (z : IGame.{0}),
        Membership.mem.{1, 1} (IGame.moves.{0} p (HAdd.hAdd.{1, 1, 1} z y)) (HAdd.hAdd.{1, 1, 1} z x) := fun hc_h => absurd (@hc_h (Player.left : Player) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.add_right_mem_moves_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.add_right_mem_moves_add.h3 : ¬∀ {p : Player} {x y : IGame.{0}} (z : IGame.{0}),
        Membership.mem.{1, 1} (IGame.moves.{0} p (HAdd.hAdd.{1, 1, 1} y z)) (HAdd.hAdd.{1, 1, 1} x z) := fun hc_h => absurd (@hc_h (Player.left : Player) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- Nimber.coeff_C_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.coeff_C_lt.h2 : ¬∀ {x y : Nimber.{0}} (k : ℕ), LT.lt.{1} ((AddMonoidAlgebra.coeff.{1, 0} (Polynomial.C.{1} y)) k) x := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- Surreal.Cut.Fits.le_leftSurreal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.Fits.le_leftSurreal.h3 : ¬∀ {x : Surreal.{0}} {y : Surreal.Cut.{0}} {z : Surreal.Cut.{0}}, LE.le.{1} y (Surreal.Cut.leftSurreal.{0} x) := fun hc_h => absurd (@hc_h ((1 : Surreal) : Surreal.{0}) (Top.top.{1}) (Bot.bot.{1})) (by
  simp)

-- IGame.mem_grundyAux_image_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.mem_grundyAux_image_of_lt.h3 : ¬∀ {p : Player} {x : IGame.{0}} {o : Nimber.{0}},
        Membership.mem.{1, 1} (Set.image.{1, 1} (IGame.grundyAux.{0} p) (IGame.moves.{0} p x)) o := fun hc_h => absurd (@hc_h (Player.left : Player) ((0 : IGame) : IGame.{0}) (0)) (by
  simp)

-- Nimber.IsField.leastNoRoots_eq_of_not_perfectField, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.leastNoRoots_eq_of_not_perfectField.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- IGame.mem_moves_nim_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.mem_moves_nim_of_lt.h3 : ¬∀ {a b : Nimber.{0}} (p : Player), Membership.mem.{1, 1} (IGame.moves.{0} p (IGame.nim.{0} b)) (IGame.nim.{0} a) := fun hc_h => absurd (@hc_h (0) (0) (Player.left : Player)) (by
  simp)

-- IGame.lf_ordinalSum_iff_of_forall_wsubposition, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.lf_ordinalSum_iff_of_forall_wsubposition.h3 : ¬∀ {x y z : IGame.{0}}, ¬LE.le.{1} (IGame.ordinalSum.{0} x y) z ↔ ¬LE.le.{1} x z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.ordinalSum_lf_ordinalSum_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.ordinalSum_lf_ordinalSum_right.h3 : ¬∀ (x : IGame.{0}) {y z : IGame.{0}}, ¬LE.le.{1} (IGame.ordinalSum.{0} x z) (IGame.ordinalSum.{0} x y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.ordinalSum_fuzzy_ordinalSum_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.ordinalSum_fuzzy_ordinalSum_right.h3 : ¬∀ (x : IGame.{0}) {y z : IGame.{0}}, IGame.ordinalSum.{0} x y ‖ IGame.ordinalSum.{0} x z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.lt_ordinalSum_iff_of_forall_wsubposition, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.lt_ordinalSum_iff_of_forall_wsubposition.h3 : ¬∀ {x y z : IGame.{0}}, LT.lt.{1} z (IGame.ordinalSum.{0} x y) ↔ LT.lt.{1} z x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.sub_congr_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.sub_congr_left.h3 : ¬∀ {a b c : IGame.{0}}, HSub.hSub.{1, 1, 1} a c ≈ HSub.hSub.{1, 1, 1} b c := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- IGame.Numeric.mul_inv_cancel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_inv_cancel.h2 : ¬∀ {x : IGame.{0}} [inst : IGame.Numeric.{0} x], HMul.hMul.{1, 1, 1} x (Inv.inv.{1} x) ≈ 1 := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _) (by
  (game_cmp; done))

-- Surreal.ratCast_toDyadic, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.ratCast_toDyadic.h2 : ¬∀ (x : IGame.{0}) [inst : IGame.Short.{0} x], IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) _) (by
  simp)

-- NatOrdinal.of_omega0_opow_add', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.of_omega0_opow_add'.h2 : ¬∀ {x y : Ordinal.{0}},
        Eq.{2} (NatOrdinal.of.{0} (HAdd.hAdd.{1, 1, 1} (HPow.hPow.{1, 1, 1} Ordinal.omega0.{0} x) y))
          (HAdd.hAdd.{1, 1, 1} (Wpow.wpow.{1} (NatOrdinal.of.{0} x)) (NatOrdinal.of.{0} y)) := fun hc_h => absurd (@hc_h ((0 : Ordinal) : Ordinal.{0}) (Ordinal.omega0 : Ordinal.{0})) (by
  simp)

-- Nimber.IsGroup.groupClosure_le_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.groupClosure_le_iff.h2 : ¬∀ {x y : Nimber.{0}}, LE.le.{1} (Nimber.groupClosure.{0} y) x ↔ LE.le.{1} y x := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Dyadic.eq_upper_of_mem_moves_right_toIGame, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.eq_upper_of_mem_moves_right_toIGame.h2 : ¬∀ {x : Dyadic} {y : IGame.{0}}, Eq.{2} y ↑x.upper := fun hc_h => absurd (@hc_h (Dyadic.zero) ((0 : IGame) : IGame.{0})) (by
  (simp <;> decide))

-- Nimber.eq_oeval_of_lt_opow_omega0, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.eq_oeval_of_lt_opow_omega0.h2 : ¬∀ {x y : Nimber.{0}},
        ∃ (p : Polynomial.{1} Nimber.{0}),
          (∀ (k : ℕ), LT.lt.{1} ((AddMonoidAlgebra.coeff.{1, 0} p) k) x) ∧ Eq.{2} (Nimber.oeval.{0} x p) y := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- IGame.Impartial.fuzzy_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.fuzzy_zero.h1 : ¬∀ {x : IGame.{0}} (p : Player), x ‖ 0 ↔ ∃ (y : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} p x) y ∧ y ≈ 0 := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) (Player.left : Player)) (by
  (simp <;> game_cmp <;> done))

-- Surreal.Cut.birthday_lt_sSup_birthday, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.birthday_lt_sSup_birthday.h2 : Not
      (∀ {a : Surreal.{0}} {s : Set.{1} Surreal.{0}},
        @LT.lt.{1} (WithTop.{1} NatOrdinal.{0})
          (@Preorder.toLT.{1} (WithTop.{1} NatOrdinal.{0})
            (@WithTop.instPreorder.{1} NatOrdinal.{0}
              (@PartialOrder.toPreorder.{1} NatOrdinal.{0} NatOrdinal.instPartialOrder.{0})))
          (@WithTop.some.{1} NatOrdinal.{0} a.birthday)
          (@SupSet.sSup.{1} (WithTop.{1} NatOrdinal.{0})
            (@WithTop.instSupSet.{1} NatOrdinal.{0}
              (@Preorder.toLE.{1} NatOrdinal.{0}
                (@PartialOrder.toPreorder.{1} NatOrdinal.{0} NatOrdinal.instPartialOrder.{0}))
              (@ConditionallyCompletePartialOrderSup.toSupSet.{1} NatOrdinal.{0}
                (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{1} NatOrdinal.{0}
                  (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{1} NatOrdinal.{0}
                    (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{1} NatOrdinal.{0}
                      (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{1} NatOrdinal.{0}
                        NatOrdinal.instConditionallyCompleteLinearOrderBot.{0}))))))
            (@Set.image.{1, 1} Surreal.{0} (WithTop.{1} NatOrdinal.{0})
              (fun (x : Surreal.{0}) =>
                @HAdd.hAdd.{1, 1, 1} (WithTop.{1} NatOrdinal.{0}) (WithTop.{1} NatOrdinal.{0}) (WithTop.{1} NatOrdinal.{0})
                  (@instHAdd.{1} (WithTop.{1} NatOrdinal.{0}) (@WithTop.add.{1} NatOrdinal.{0} NatOrdinal.instAdd.{0}))
                  (@WithTop.some.{1} NatOrdinal.{0} x.birthday)
                  (@OfNat.ofNat.{1} (WithTop.{1} NatOrdinal.{0}) (nat_lit 1)
                    (@One.toOfNat1.{1} (WithTop.{1} NatOrdinal.{0})
                      (@WithTop.one.{1} NatOrdinal.{0} instOneNatOrdinal.{0}))))
              s))) := fun hc_h => absurd (@hc_h ((1 : Surreal) : Surreal.{0}) (({0} : Set Surreal) : Set.{1} Surreal.{0})) (by
  simp)

-- Nimber.IsAlgClosed.not_perfectField_fieldClosure_succ_pow_two_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsAlgClosed.not_perfectField_fieldClosure_succ_pow_two_pow.h1 : ¬∀ {t : Nimber.{0}} (n : ℕ), Nimber.IsAlgClosed.{0} t := fun hc_h => absurd (@hc_h (1) (0)) (by
  nofun)

-- IGame.Impartial.sub_mk, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.sub_mk.h1 : ¬∀ (y : IGame.{0}) (x : Game.{0}),
        Eq.{2} (HSub.hSub.{1, 1, 1} x (Game.mk.{0} y)) (HAdd.hAdd.{1, 1, 1} x (Game.mk.{0} y)) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((1 : Game) : Game.{0})) (by
  norm_num)

-- IGame.Impartial.equiv_iff_add_equiv_zero', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.equiv_iff_add_equiv_zero'.h2 : ¬∀ {x y : IGame.{0}}, x ≈ y ↔ HAdd.hAdd.{1, 1, 1} x y ≈ 0 := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  (simp <;> game_cmp <;> done))

-- SignExpansion.apply_of_length_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignExpansion.apply_of_length_le.h2 : ¬∀ {x : SignExpansion.{0}} {o : NatOrdinal.{0}}, Eq.{1} (x o) 0 := fun hc_h => absurd (@hc_h (Bot.bot.{1}) (0)) (by
  decide +kernel)

-- Surreal.wlog_eq_of_wpow_veq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.wlog_eq_of_wpow_veq.h2 : ¬∀ {x y : Surreal.{0}}, Eq.{2} (Surreal.wlog.{0} x) y := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0})) (by
  simp)

-- SignExpansion.neg_lt_neg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignExpansion.neg_lt_neg.h2 : ¬∀ {x y : SignExpansion.{0}}, LT.lt.{1} (Neg.neg.{1} y) (Neg.neg.{1} x) := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Surreal.Cut.rightSurreal_mem_of_sSup_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.rightSurreal_mem_of_sSup_eq.h2 : ¬∀ {s : Set.{1} Surreal.Cut.{0}} {x : Surreal.{0}}, Membership.mem.{1, 1} s (Surreal.Cut.rightSurreal.{0} x) := fun hc_h => absurd (@hc_h (EmptyCollection.emptyCollection.{1}) ((0 : Surreal) : Surreal.{0})) (by
  decide +kernel)

-- Surreal.wlog_eq_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.wlog_eq_iff.h2 : ¬∀ {x y : Surreal.{0}}, Eq.{2} (Surreal.wlog.{0} x) y ↔ ValuativeRel.veq.{1} (Wpow.wpow.{1} y) x := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) ((0 : Surreal) : Surreal.{0})) (by
  simp)

-- Surreal.leadingCoeff_add_eq_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.leadingCoeff_add_eq_right.h2 : ¬∀ {x y : Surreal.{0}}, Eq.{1} (Surreal.leadingCoeff.{0} (HAdd.hAdd.{1, 1, 1} y x)) (Surreal.leadingCoeff.{0} x) := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0})) (by
  simp)

-- IGame.Fits.neg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Fits.neg.h2 : ¬∀ {x y : IGame.{0}}, IGame.Fits.{0} (Neg.neg.{1} x) (Neg.neg.{1} y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  (simp <;> game_cmp <;> done))

-- Surreal.leadingTerm_add_eq_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.leadingTerm_add_eq_left.h2 : ¬∀ {x y : Surreal.{0}}, Eq.{2} (Surreal.leadingTerm.{0} (HAdd.hAdd.{1, 1, 1} x y)) (Surreal.leadingTerm.{0} x) := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0})) (by
  simp)

-- NatOrdinal.of_omega0_opow_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.of_omega0_opow_add.h2 : ¬∀ {x y : Ordinal.{0}},
        Eq.{2} (NatOrdinal.of.{0} (HAdd.hAdd.{1, 1, 1} (HPow.hPow.{1, 1, 1} Ordinal.omega0.{0} x) y))
          (HAdd.hAdd.{1, 1, 1} (Wpow.wpow.{1} (NatOrdinal.of.{0} x)) (NatOrdinal.of.{0} y)) := fun hc_h => absurd (@hc_h ((0 : Ordinal) : Ordinal.{0}) (Ordinal.omega0 : Ordinal.{0})) (by
  simp)

-- IGame.Short.ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Short.ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nimber.IsAlgClosed.omega0_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsAlgClosed.omega0_le.h1 : ¬∀ {x : Nimber.{0}}, LE.le.{1} (Nimber.of.{0} Ordinal.omega0.{0}) x := fun hc_h => absurd (@hc_h (1)) (by
  simp)

-- Surreal.Cut.leftGame_mk_of_numeric, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.leftGame_mk_of_numeric.h1 : ¬∀ (x : IGame.{0}), IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0})) (by
  simp)

-- IGame.Impartial.add_self_equiv, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.add_self_equiv.h1 : ¬∀ (x : IGame.{0}), HAdd.hAdd.{1, 1, 1} x x ≈ 0 := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- SignExpansion.Small.length_lt_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignExpansion.Small.length_lt_top.h1 : ¬∀ {x : SignExpansion.{0}}, LT.lt.{1} (SignExpansion.length.{0} x) Top.top.{1} := fun hc_h => absurd (@hc_h (Bot.bot.{1})) (by
  simp)

-- IGame.fuzzy_miny_toIGame_birthday, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.fuzzy_miny_toIGame_birthday.h1 : ¬∀ {x : IGame.{0}}, x ‖ IGame.miny.{0} (NatOrdinal.toIGame.{0} (IGame.birthday.{0} x)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- Nimber.natDegree_leastNoRoots_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.natDegree_leastNoRoots_pos.h1 : ¬∀ {x : Nimber.{0}}, Ne.{2} (Nimber.leastNoRoots.{0} x) Top.top.{1} := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Nimber.IsGroup.neZero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.neZero.h1 : ¬∀ {x : Nimber.{0}}, NeZero.{1} x := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- SignExpansion.Small.length_ne_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignExpansion.Small.length_ne_top.h1 : ¬∀ (x : SignExpansion.{0}), Ne.{2} (SignExpansion.length.{0} x) Top.top.{1} := fun hc_h => absurd (@hc_h (Bot.bot.{1})) (by
  simp)

-- Nimber.IsGroup.closure_Iio, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.closure_Iio.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsGroup.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- Nimber.coe_toSubring, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.coe_toSubring.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsRing.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- Surreal.wpow_wlog_veq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.wpow_wlog_veq.h1 : ¬∀ {x : Surreal.{0}}, ValuativeRel.veq.{1} (Wpow.wpow.{1} (Surreal.wlog.{0} x)) x := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0})) (by
  simp)

-- pos_of_mem_powers, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.pos_of_mem_powers.h1 : ¬∀ {n : ℕ}, 0 < n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nimber.IsField.closure_Iio, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.closure_Iio.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- Dyadic.den_upper_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.den_upper_lt.h1 : ¬∀ {x : Dyadic}, x.upper.den < x.den := fun hc_h => absurd (@hc_h (Dyadic.zero)) (by
  simp)

-- Dyadic.den_add_self_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.den_add_self_lt.h1 : ¬∀ {x : Dyadic}, (x + x).den < x.den := fun hc_h => absurd (@hc_h (Dyadic.zero)) (by
  decide +kernel)

-- Nimber.leastNoRoots_ne_zero', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.leastNoRoots_ne_zero'.h1 : ¬∀ {x : Nimber.{0}}, Ne.{2} (Nimber.leastNoRoots.{0} x) Top.top.{1} := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Surreal.mk_lt_mk_sub_leadingTerm, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.mk_lt_mk_sub_leadingTerm.h1 : ¬∀ {x : Surreal.{0}},
        LT.lt.{1} (ArchimedeanClass.mk.{1} x) (ArchimedeanClass.mk.{1} (HSub.hSub.{1, 1, 1} x (Surreal.leadingTerm.{0} x))) := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0})) (by
  simp)

-- Surreal.birthday_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.birthday_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nimber.IsAlgClosed.ringClosure_eq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsAlgClosed.ringClosure_eq.h1 : ¬∀ {t : Nimber.{0}},
        Eq.{2} (Nimber.ringClosure.{0} (Order.succ.{1} t))
          (Nimber.of.{0} (HPow.hPow.{1, 1, 1} (Nimber.val.{0} t) Ordinal.omega0.{0})) := fun hc_h => absurd (@hc_h (1)) (by
  simp)

