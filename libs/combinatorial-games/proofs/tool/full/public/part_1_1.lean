module
public import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- IGame.Numeric.mulOption_congr₄, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mulOption_congr₄.h10 : ¬∀ {x y a b₁ b₂ : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} a]
        [inst : IGame.Numeric.{0} b₁] [inst : IGame.Numeric.{0} b₂],
        IGame.mulOption.{0} x y a b₁ ≈ IGame.mulOption.{0} x y a b₂ := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _ _ _) (by
  (game_cmp; done))

-- Order.enum_le_of_strictMono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Order.enum_le_of_strictMono.h5 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : WellFoundedLT α] [inst_2 : IsRegularCardinalOrder α] {s : Set α}
        {x y : α} {f : ↑(Set.Iio x) → ↑s}, StrictMono f → y < x → IsCofinal s := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) _ _ ({n : ℕ | n = 0}) (1) (0) (fun (a : ↑(Set.Iio 1)) => (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n = 0} })) (by
  decide) (by
  decide)) (by
  simp)

-- Order.enum_le_of_strictMono, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Order.enum_le_of_strictMono.h10 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : WellFoundedLT α] [inst_2 : IsRegularCardinalOrder α] {s : Set α},
        IsCofinal s → ∀ {x y : α} {f : ↑(Set.Iio x) → ↑s}, StrictMono f → y < x := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) _ _ ({x : ℕ | True}) (by
  simp) (0) (0) (fun (a : ↑(Set.Iio 0)) => (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {x : ℕ | True} })) (by
  decide)) (by
  decide +kernel)

-- IGame.Numeric.mul_right_cancel, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_right_cancel.h6 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        HMul.hMul.{1, 1, 1} y x ≈ HMul.hMul.{1, 1, 1} z x → y ≈ z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _ (by
  simp)) (by
  (game_cmp; done))

-- IGame.Numeric.mul_right_cancel, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_right_cancel.h7 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        ¬x ≈ 0 → y ≈ z := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _ (by
  (game_cmp; done))) (by
  (game_cmp; done))

-- IGame.Numeric.mul_wpow_lt_mul_wpow_of_neg', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_wpow_lt_mul_wpow_of_neg'.h6 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] (r : Dyadic) {s : Dyadic},
        LT.lt.{1} y x → LT.lt.{1} (HMul.hMul.{1, 1, 1} (↑r) (Wpow.wpow.{1} x)) (HMul.hMul.{1, 1, 1} (↑s) (Wpow.wpow.{1} y)) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ (Dyadic.zero) (Dyadic.zero) (by
  simp)) (by
  simp)

-- IGame.Numeric.mul_lt_mul_iff_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_lt_mul_iff_left.h6 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        LT.lt.{1} (HMul.hMul.{1, 1, 1} y x) (HMul.hMul.{1, 1, 1} z x) ↔ LT.lt.{1} y z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _) (by
  simp)

-- IGame.Numeric.mul_le_mul_iff_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_le_mul_iff_left.h6 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        LE.le.{1} (HMul.hMul.{1, 1, 1} y x) (HMul.hMul.{1, 1, 1} z x) ↔ LE.le.{1} y z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ _) (by
  simp)

-- InitialSeg.le_of_strictMono, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.InitialSeg.le_of_strictMono.h7 : ¬∀ {α β : Type} [inst : LinearOrder α] [inst_1 : LinearOrder β] [inst_2 : WellFoundedLT α] (f : α ≤i β) {g : α → β}
        (x : α), f x ≤ g x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instLinearOrder) _ (Inhabited.default) (fun _ => 0 : ℕ → ℕ) (1)) (by
  decide +kernel)

-- IGame.Numeric.mul_nonneg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_nonneg.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y],
        LE.le.{1} 0 y → LE.le.{1} 0 (HMul.hMul.{1, 1, 1} x y) := fun hc_h => absurd (@hc_h ((-1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ (by
  simp)) (by
  simp)

-- IGame.Numeric.mul_nonneg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_nonneg.h5 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y],
        LE.le.{1} 0 x → LE.le.{1} 0 (HMul.hMul.{1, 1, 1} x y) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((-1 : IGame) : IGame.{0}) _ _ (by
  simp)) (by
  simp)

-- IGame.Numeric.mul_nonneg_of_nonpos_of_nonpos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_nonneg_of_nonpos_of_nonpos.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y],
        LE.le.{1} y 0 → LE.le.{1} 0 (HMul.hMul.{1, 1, 1} x y) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((-1 : IGame) : IGame.{0}) _ _ (by
  simp)) (by
  simp)

-- IGame.Numeric.mul_nonneg_of_nonpos_of_nonpos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_nonneg_of_nonpos_of_nonpos.h5 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y],
        LE.le.{1} x 0 → LE.le.{1} 0 (HMul.hMul.{1, 1, 1} x y) := fun hc_h => absurd (@hc_h ((-1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ (by
  simp)) (by
  simp)

-- Ordinal.enum_lt_of_lt_ord_cof, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordinal.enum_lt_of_lt_ord_cof.h5 : ¬∀ {s : Set.{1} Ordinal.{0}} (hs : IsCofinal.{1} s) {x y : Ordinal.{0}},
        (∀ (a : Ordinal.{0}),
            LT.lt.{1} a x → ∃ (b : Ordinal.{0}), Membership.mem.{1, 1} s b ∧ Membership.mem.{1, 1} (Set.Ico.{1} a x) b) →
          LT.lt.{1} (↑((Order.enum.{1} s hs) y)) x := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Top.top.{1}) hc_k0 ((0 : Ordinal) : Ordinal.{0}) ((0 : Ordinal) : Ordinal.{0}) hc_k1) (by
  simp)

-- Surreal.trunc_eq_of_birthday_le_of_forall_lt_gt_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.trunc_eq_of_birthday_le_of_forall_lt_gt_iff.h3 : ¬∀ {x y : Surreal.{0}} {o : NatOrdinal.{0}},
        (∀ (z : Surreal.{0}), LT.lt.{1} (Surreal.birthday.{0} z) o → (LT.lt.{1} y z ↔ LT.lt.{1} x z)) →
          (∀ (z : Surreal.{0}), LT.lt.{1} (Surreal.birthday.{0} z) o → (LT.lt.{1} z y ↔ LT.lt.{1} z x)) →
            Eq.{2} ((Surreal.trunc.{0} o) x) y := fun hc_h => absurd (@hc_h ((1 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0}) (0) (by
  simp) (by
  simp)) (by
  simp)

-- IGame.Numeric.mul_nonpos_of_nonpos_of_nonneg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_nonpos_of_nonpos_of_nonneg.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y],
        LE.le.{1} 0 y → LE.le.{1} (HMul.hMul.{1, 1, 1} x y) 0 := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ (by
  simp)) (by
  simp)

-- IGame.Small.lt_numeric_of_pos_of_forall_of_nonempty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Small.lt_numeric_of_pos_of_forall_of_nonempty.h2 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} y],
        (∀ (p : Player) (y : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} p x) y → IGame.Small.{0} y) →
          Set.Nonempty.{1} (IGame.moves.{0} Player.right x) → LT.lt.{1} x y := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) _ (by
  simp) (by
  simp)) (by
  simp)

-- IGame.Small.lt_numeric_of_pos_of_forall_of_nonempty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Small.lt_numeric_of_pos_of_forall_of_nonempty.h5 : ¬∀ {x y : IGame.{0}},
        LT.lt.{1} 0 y →
          ∀ [inst : IGame.Numeric.{0} y],
            (∀ (p : Player) (y : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} p x) y → IGame.Small.{0} y) →
              LT.lt.{1} x y := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  simp) _ (by
  simp)) (by
  simp)

-- IGame.Numeric.mul_pos_of_neg_of_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_pos_of_neg_of_neg.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y],
        LT.lt.{1} y 0 → LT.lt.{1} 0 (HMul.hMul.{1, 1, 1} x y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((-1 : IGame) : IGame.{0}) _ _ (by
  simp)) (by
  simp)

-- IGame.Numeric.mul_pos_of_neg_of_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_pos_of_neg_of_neg.h5 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y],
        LT.lt.{1} x 0 → LT.lt.{1} 0 (HMul.hMul.{1, 1, 1} x y) := fun hc_h => absurd (@hc_h ((-1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ (by
  simp)) (by
  simp)

-- Nimber.leastNoRoots_le_of_not_isRoot, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.leastNoRoots_le_of_not_isRoot.h3 : ¬∀ {x : Nimber.{0}} {p : Polynomial.{1} Nimber.{0}},
        LT.lt.{0} 0 (Polynomial.degree.{1} p) →
          (∀ (r : Nimber.{0}), LT.lt.{1} r x → ¬Polynomial.IsRoot.{1} p r) → LE.le.{1} (Nimber.leastNoRoots.{0} x) ↑p := fun hc_h => absurd (@hc_h (0) ((Polynomial.X : Polynomial Nimber) : Polynomial.{1} Nimber.{0}) (by
  simp) (by
  simp)) (by
  simp)

-- IGame.Small.numeric_lt_of_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Small.numeric_lt_of_neg.h4 : ¬∀ (x : IGame.{0}) {y : IGame.{0}} [inst : IGame.Small.{0} x] [inst : IGame.Numeric.{0} y], LT.lt.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _) (by
  simp)

-- IGame.Numeric.mul_pos_iff_of_pos_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_pos_iff_of_pos_right.h4 : ¬∀ {a b : IGame.{0}} [inst : IGame.Numeric.{0} a] [inst : IGame.Numeric.{0} b],
        LT.lt.{1} 0 (HMul.hMul.{1, 1, 1} a b) ↔ LT.lt.{1} 0 a := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _) (by
  simp)

-- Nimber.IsField.opow_log_eq_of_isGroup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.opow_log_eq_of_isGroup.h3 : ¬∀ {x y : Nimber.{0}},
        Nimber.IsField.{0} x →
          (∀ (z w : Nimber.{0}), LT.lt.{1} z x → LT.lt.{1} w y → LT.lt.{1} (HMul.hMul.{1, 1, 1} z w) y) →
            Eq.{2}
              (Nimber.of.{0}
                (HPow.hPow.{1, 1, 1} (Nimber.val.{0} x) (Ordinal.log.{0} (Nimber.val.{0} x) (Nimber.val.{0} y))))
              y := fun hc_h => absurd (@hc_h (Nimber.of 2 : Nimber.{0}) (0) (by
  simp) (by
  simp)) (by
  simp)

-- Nimber.IsField.inv_lt', hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Nimber.IsField.inv_lt'.h3.gneg.{u_1} : ∀ {x : Nimber.{u_1}},
      Nimber.IsField.{u_1} x →
        ∀ ⦃y : Nimber.{u_1}⦄, ¬Ne.{u_1 + 2} y 0 → LT.lt.{u_1 + 1} y x → LT.lt.{u_1 + 1} (Inv.inv.{u_1 + 1} y) x := by
  (intros; simp_all; done)
theorem HypCheckProof.Nimber.IsField.inv_lt'.h3.{u_1} : ∀ {x : Nimber.{u_1}},
      Nimber.IsField.{u_1} x → ∀ ⦃y : Nimber.{u_1}⦄, LT.lt.{u_1 + 1} y x → LT.lt.{u_1 + 1} (Inv.inv.{u_1 + 1} y) x := by
  intro hc_x0 hc_x1 hc_x2 hc_x4
  exact Classical.byCases (fun hc_h => @Nimber.IsField.inv_lt' hc_x0 hc_x1 hc_x2 hc_h hc_x4) (fun hc_hn => @HypCheckProof.Nimber.IsField.inv_lt'.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4)

-- Dyadic.mkRat_lt_mkRat, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.mkRat_lt_mkRat.h3.der : ∀ {m n : Int} {k : Nat},
      @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k →
        @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k := by
  (intros; assumption)
theorem HypCheckProof.Dyadic.mkRat_lt_mkRat.h3 : ∀ {m n : Int} {k : Nat}
      (h₂ :
        @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k),
      Iff
        (@LT.lt Dyadic Dyadic.instLT (@Dyadic.mkRat m k (@HypCheckProof.Dyadic.mkRat_lt_mkRat.h3.der m n k h₂))
          (@Dyadic.mkRat n k h₂))
        (@LT.lt Int Int.instLTInt m n) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Dyadic.mkRat_lt_mkRat hc_x0 hc_x1 hc_x2 (@HypCheckProof.Dyadic.mkRat_lt_mkRat.h3.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x3

-- Dyadic.mkRat_lt_mkRat, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.mkRat_lt_mkRat.h4.der : ∀ {m n : Int} {k : Nat},
      @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k →
        @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k := by
  (intros; assumption)
theorem HypCheckProof.Dyadic.mkRat_lt_mkRat.h4 : ∀ {m n : Int} {k : Nat}
      (h₁ :
        @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k),
      Iff
        (@LT.lt Dyadic Dyadic.instLT (@Dyadic.mkRat m k h₁)
          (@Dyadic.mkRat n k (@HypCheckProof.Dyadic.mkRat_lt_mkRat.h4.der m n k h₁)))
        (@LT.lt Int Int.instLTInt m n) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Dyadic.mkRat_lt_mkRat hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Dyadic.mkRat_lt_mkRat.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- IGame.Fits.congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Fits.congr.h4 : ¬∀ {x y z : IGame.{0}}, x ≈ y → IGame.Fits.{0} y z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  rfl)) (by
  (simp <;> game_cmp <;> done))

-- IGame.Impartial.fuzzy_iff_exists_equiv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.fuzzy_iff_exists_equiv.h2 : ¬∀ {x y : IGame.{0}} [hy : IGame.Impartial.{0} y] (p : Player),
        x ‖ y ↔
          (∃ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} p x) z ∧ z ≈ y) ∨
            ∃ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} (Neg.neg.{0} p) y) z ∧ x ≈ z := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ (Player.left : Player)) (by
  (simp <;> game_cmp <;> done))

-- IGame.Impartial.fuzzy_iff_exists_equiv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.fuzzy_iff_exists_equiv.h3 : ¬∀ {x y : IGame.{0}} [hx : IGame.Impartial.{0} x] (p : Player),
        x ‖ y ↔
          (∃ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} p x) z ∧ z ≈ y) ∨
            ∃ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} (Neg.neg.{0} p) y) z ∧ x ≈ z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ (Player.right : Player)) (by
  (simp <;> game_cmp <;> done))

-- SignExpansion.apply_eq_zero_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignExpansion.apply_eq_zero_of_le.h4 : ¬∀ {x : SignExpansion.{0}} {o o' : NatOrdinal.{0}}, LE.le.{1} o o' → Eq.{1} (x o') 0 := fun hc_h => absurd (@hc_h (Bot.bot.{1}) (0) (0) (by
  rfl)) (by
  decide +kernel)

-- Surreal.round_eq_of_forall_birthday_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.round_eq_of_forall_birthday_le.h3 : ¬∀ {x y r : Surreal.{0}},
        (∀ (z : Surreal.{0}),
            Membership.mem.{1, 1} (Set.Ioo.{1} (HSub.hSub.{1, 1, 1} x r) (HAdd.hAdd.{1, 1, 1} x r)) z →
              LE.le.{1} (Surreal.birthday.{0} y) (Surreal.birthday.{0} z)) →
          Eq.{2} (Surreal.round.{0} x r) y := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0}) ((0 : Surreal) : Surreal.{0}) (by
  simp)) (by
  simp)

-- Surreal.round_eq_of_forall_birthday_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.round_eq_of_forall_birthday_le.h4 : ¬∀ {x y r : Surreal.{0}},
        Membership.mem.{1, 1} (Set.Ioo.{1} (HSub.hSub.{1, 1, 1} x r) (HAdd.hAdd.{1, 1, 1} x r)) y →
          Eq.{2} (Surreal.round.{0} x r) y := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0}) ((2 : Surreal) : Surreal.{0}) (by
  grind)) (by
  simp)

-- Surreal.mk_eq_mk', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.mk_eq_mk'.h2 : ¬∀ {x y : IGame.{0}} {x_1 : IGame.Numeric.{0} y}, IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  simp)

-- Surreal.mk_eq_mk', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.mk_eq_mk'.h3 : ¬∀ {x y : IGame.{0}} {x : IGame.Numeric.{0} x}, IGame.Numeric.{0} y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) (by
  simp)) (by
  simp)

-- gf_iff_fuzzy_of_neg_equiv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.gf_iff_fuzzy_of_neg_equiv.h2 : ¬∀ {x y : IGame.{0}}, Neg.neg.{1} y ≈ y → (¬LE.le.{1} x y ↔ x ‖ y) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  (simp <;> game_cmp <;> done))

-- gf_iff_fuzzy_of_neg_equiv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.gf_iff_fuzzy_of_neg_equiv.h3 : ¬∀ {x y : IGame.{0}}, Neg.neg.{1} x ≈ x → (¬LE.le.{1} x y ↔ x ‖ y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((-1 : IGame) : IGame.{0}) (by
  simp)) (by
  (simp <;> game_cmp <;> done))

-- IGame.Numeric.lt_or_ge, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.lt_or_ge.h2 : ¬∀ (x y : IGame.{0}) [inst : IGame.Numeric.{0} y], LT.lt.{1} x y ∨ LE.le.{1} y x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.lt_or_ge, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.lt_or_ge.h3 : ¬∀ (x y : IGame.{0}) [inst : IGame.Numeric.{0} x], LT.lt.{1} x y ∨ LE.le.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) _) (by
  (simp <;> omega))

-- IGame.Numeric.sub, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.sub.h2 : ¬∀ (x y : IGame.{0}) [inst : IGame.Numeric.{0} y], IGame.Numeric.{0} (HSub.hSub.{1, 1, 1} x y) := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.sub, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.sub.h3 : ¬∀ (x y : IGame.{0}) [inst : IGame.Numeric.{0} x], IGame.Numeric.{0} (HSub.hSub.{1, 1, 1} x y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) _) (by
  simp)

-- IGame.tiny_lf_of_not_nonpos_of_forall_neg_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.tiny_lf_of_not_nonpos_of_forall_neg_le.h2 : ¬∀ {x a : IGame.{0}},
        (∀ (y : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) y → LE.le.{1} (Neg.neg.{1} y) a) →
          ¬LE.le.{1} x (IGame.tiny.{0} a) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  (game_cmp; done))

-- dvd_iff_le_of_mem_powers, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.dvd_iff_le_of_mem_powers.h2 : ¬∀ {m n : ℕ}, n ∈ Submonoid.powers 2 → (m ∣ n ↔ m ≤ n) := fun hc_h => absurd (@hc_h (0) (1) (by
  simp)) (by
  decide +kernel)

-- dvd_iff_le_of_mem_powers, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.dvd_iff_le_of_mem_powers.h3 : ¬∀ {m n : ℕ}, m ∈ Submonoid.powers 2 → (m ∣ n ↔ m ≤ n) := fun hc_h => absurd (@hc_h (1) (0) (by
  simp)) (by
  decide +kernel)

-- Dyadic.le_lower_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.le_lower_of_lt.h2 : ¬∀ {x y : Dyadic}, x < y → x ≤ y.lower := fun hc_h => absurd (@hc_h (Dyadic.half : Dyadic) ((1 : Dyadic) : Dyadic) (by
  decide)) (by
  decide +kernel)

-- Dyadic.le_lower_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.le_lower_of_lt.h3 : ¬∀ {x y : Dyadic}, x.den ≤ y.den → x ≤ y.lower := fun hc_h => absurd (@hc_h (Dyadic.zero) (Dyadic.zero) (by
  decide)) (by
  decide +kernel)

-- IGame.Small.surreal_lt_of_neg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Small.surreal_lt_of_neg.h3 : ¬∀ (x : IGame.{0}) [inst : IGame.Small.{0} x] {y : Surreal.{0}}, LT.lt.{1} (Surreal.toGame.{0} y) (Game.mk.{0} x) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _ ((0 : Surreal) : Surreal.{0})) (by
  simp)

-- Nimber.IsRing.toSubring_lt_toSubring, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.toSubring_lt_toSubring.h2 : ¬∀ {x y : Nimber.{0}}, Nimber.IsRing.{0} y → Nimber.IsRing.{0} x := fun hc_h => absurd (@hc_h (0) (Nimber.of 2 : Nimber.{0}) (by
  simp)) (by
  nofun)

-- Nimber.IsRing.toSubring_lt_toSubring, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.toSubring_lt_toSubring.h3 : ¬∀ {x y : Nimber.{0}}, Nimber.IsRing.{0} x → Nimber.IsRing.{0} y := fun hc_h => absurd (@hc_h (Nimber.of 2 : Nimber.{0}) (0) (by
  simp)) (by
  nofun)

-- Nimber.IsGroup.exists_mul_of_not_isRing, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.exists_mul_of_not_isRing.h1 : ¬∀ {x : Nimber.{0}},
        ¬Nimber.IsRing.{0} x →
          Ne.{2} x 1 →
            ∃ (y : Nimber.{0}), LT.lt.{1} y x ∧ ∃ (z : Nimber.{0}), LT.lt.{1} z x ∧ Eq.{2} (HMul.hMul.{1, 1, 1} y z) x := fun hc_h => absurd (@hc_h (0) (by
  aesop) (by
  simp)) (by
  simp)

-- Nimber.IsGroup.exists_mul_of_not_isRing, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.exists_mul_of_not_isRing.h3 : ¬∀ {x : Nimber.{0}},
        Nimber.IsGroup.{0} x →
          ¬Nimber.IsRing.{0} x →
            ∃ (y : Nimber.{0}), LT.lt.{1} y x ∧ ∃ (z : Nimber.{0}), LT.lt.{1} z x ∧ Eq.{2} (HMul.hMul.{1, 1, 1} y z) x := fun hc_h => absurd (@hc_h (1) (by
  simp) (by
  aesop)) (by
  simp)

-- Nimber.polynomial_eq_zero_of_le_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.polynomial_eq_zero_of_le_one.h3 : ¬∀ {x : Nimber.{0}} {p : Polynomial.{1} Nimber.{0}}, LE.le.{1} x 1 → Eq.{2} p 0 := fun hc_h => absurd (@hc_h (0) ((Polynomial.X : Polynomial Nimber) : Polynomial.{1} Nimber.{0}) (by
  simp)) (by
  simp)

-- Player.const_of_left_eq_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Player.const_of_left_eq_right.h2 : ¬∀ {α : Type} {f : Player → α} (p q : Player), f p = f q := fun hc_h => absurd (@hc_h (ℕ) (fun (a : Player) => if a = Player.left then 0 else 1) (Player.left : Player) (Player.right : Player)) (by
  decide +kernel)

-- IGame.toDyadic_neg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.toDyadic_neg.h2 : ¬∀ (x : IGame.{0}) [inst : IGame.Short.{0} x], IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) _) (by
  simp)

-- IGame.rightStop_of_numeric, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.rightStop_of_numeric.h2 : ¬∀ (x : IGame.{0}) [inst : IGame.Short.{0} x], IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) _) (by
  simp)

-- IGame.sub_congr_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.sub_congr_right.h3 : ¬∀ {a b c : IGame.{0}}, HSub.hSub.{1, 1, 1} c a ≈ HSub.hSub.{1, 1, 1} c b := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- Nimber.oeval_lt_pow_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.oeval_lt_pow_iff.h3 : ¬∀ {x : Nimber.{0}} {p : Polynomial.{1} Nimber.{0}} {n : ℕ},
        LT.lt.{1} (Nimber.oeval.{0} x p) (Nimber.of.{0} (HPow.hPow.{1, 0, 1} (Nimber.val.{0} x) n)) ↔
          LT.lt.{0} (Polynomial.degree.{1} p) ↑n := fun hc_h => absurd (@hc_h (0) (AddMonoidAlgebra.ofCoeff.{1, 0} Bot.bot.{1}) (1)) (by
  (simp <;> decide))

-- Nimber.Lex.mul_leadingCoeff_inv_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.Lex.mul_leadingCoeff_inv_lt.h1 : ¬∀ {p : Polynomial.{1} Nimber.{0}},
        ¬Polynomial.Monic.{1} p →
          LT.lt.{1} (HMul.hMul.{1, 1, 1} p (Polynomial.C.{1} (Inv.inv.{1} (Polynomial.leadingCoeff.{1} p)))) p := fun hc_h => absurd (@hc_h (AddMonoidAlgebra.ofCoeff.{1, 0} 0) (by
  simp)) (by
  simp)

-- Nimber.Lex.mul_leadingCoeff_inv_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.Lex.mul_leadingCoeff_inv_lt.h2 : ¬∀ {p : Polynomial.{1} Nimber.{0}},
        Ne.{2} p 0 → LT.lt.{1} (HMul.hMul.{1, 1, 1} p (Polynomial.C.{1} (Inv.inv.{1} (Polynomial.leadingCoeff.{1} p)))) p := fun hc_h => absurd (@hc_h ((Polynomial.X : Polynomial Nimber) : Polynomial.{1} Nimber.{0}) (by
  simp)) (by
  simp)

-- IGame.rightStop_of_small, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.rightStop_of_small.h1 : ¬∀ (x : IGame.{0}) [inst : IGame.Short.{0} x], Eq.{1} (IGame.rightStop.{0} x) 0 := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.add_congr_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.add_congr_right.h3 : ¬∀ {a b c : IGame.{0}}, HAdd.hAdd.{1, 1, 1} c a ≈ HAdd.hAdd.{1, 1, 1} c b := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- Nimber.IsField.perfectField_of_le_algClosure_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.perfectField_of_le_algClosure_zero.h1 : ¬∀ {x : Nimber.{0}}, LE.le.{1} x (Nimber.algClosure.{0} 0) → Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0) (by
  simp)) (by
  nofun)

-- Nimber.add_trichotomy, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.add_trichotomy.h3 : ¬∀ {a b c : Nimber.{0}},
        LT.lt.{1} (HAdd.hAdd.{1, 1, 1} b c) a ∨
          LT.lt.{1} (HAdd.hAdd.{1, 1, 1} c a) b ∨ LT.lt.{1} (HAdd.hAdd.{1, 1, 1} a b) c := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- IGame.grundyAux_le_of_notMem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.grundyAux_le_of_notMem.h3 : ¬∀ {p : Player} {x : IGame.{0}} {o : Nimber.{0}}, LE.le.{1} (IGame.grundyAux.{0} p x) o := fun hc_h => absurd (@hc_h (Player.left : Player) (IGame.star : IGame.{0}) (0)) (by
  simp)

-- IGame.ordinalSum_le_iff_of_forall_wsubposition, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.ordinalSum_le_iff_of_forall_wsubposition.h3 : ¬∀ {x y z : IGame.{0}}, LE.le.{1} (IGame.ordinalSum.{0} x y) z ↔ LE.le.{1} x z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- Nimber.exists_add_of_not_isGroup, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.exists_add_of_not_isGroup.h1 : ¬∀ {x : Nimber.{0}},
        Ne.{2} x 0 →
          ∃ (y : Nimber.{0}), LT.lt.{1} y x ∧ ∃ (z : Nimber.{0}), LT.lt.{1} z x ∧ Eq.{2} (HAdd.hAdd.{1, 1, 1} y z) x := fun hc_h => absurd (@hc_h (1) (by
  simp)) (by
  simp)

-- Nimber.exists_add_of_not_isGroup, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.exists_add_of_not_isGroup.h2 : ¬∀ {x : Nimber.{0}},
        ¬Nimber.IsGroup.{0} x →
          ∃ (y : Nimber.{0}), LT.lt.{1} y x ∧ ∃ (z : Nimber.{0}), LT.lt.{1} z x ∧ Eq.{2} (HAdd.hAdd.{1, 1, 1} y z) x := fun hc_h => absurd (@hc_h (0) (by
  aesop)) (by
  simp)

-- Surreal.Cut.leftSurreal_mem_of_sInf_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.leftSurreal_mem_of_sInf_eq.h2 : ¬∀ {s : Set.{1} Surreal.Cut.{0}} {x : Surreal.{0}}, Membership.mem.{1, 1} s (Surreal.Cut.leftSurreal.{0} x) := fun hc_h => absurd (@hc_h (EmptyCollection.emptyCollection.{1}) ((0 : Surreal) : Surreal.{0})) (by
  decide +kernel)

-- Surreal.Cut.ext, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.ext.h2 : ¬∀ {c d : Surreal.Cut.{0}}, Eq.{2} c d := fun hc_h => absurd (@hc_h (Bot.bot.{1}) (Top.top.{1})) (by
  simp)

-- IGame.birthday_le_of_wsubposition, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.birthday_le_of_wsubposition.h2 : ¬∀ {x y : IGame.{0}}, LE.le.{1} (IGame.birthday.{0} y) (IGame.birthday.{0} x) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  simp)

-- Nimber.IsField.lt_fieldClosure_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.lt_fieldClosure_iff.h2 : ¬∀ {x y : Nimber.{0}}, LT.lt.{1} x (Nimber.fieldClosure.{0} y) ↔ LT.lt.{1} x y := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Nimber.IsField.fieldClosure_le_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.fieldClosure_le_iff.h2 : ¬∀ {x y : Nimber.{0}}, LE.le.{1} (Nimber.fieldClosure.{0} y) x ↔ LE.le.{1} y x := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- Nimber.coeff_X_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.coeff_X_lt.h1 : ¬∀ {x : Nimber.{0}} (k : ℕ), LT.lt.{1} ((AddMonoidAlgebra.coeff.{1, 0} Polynomial.X.{1}) k) x := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- IGame.wpow_mem_moves_right_wpow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.wpow_mem_moves_right_wpow.h2 : ¬∀ {x y : IGame.{0}}, Membership.mem.{1, 1} (IGame.moves.{0} Player.right (Wpow.wpow.{1} x)) (Wpow.wpow.{1} y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.wpow_mem_moves_left_wpow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.wpow_mem_moves_left_wpow.h2 : ¬∀ {x y : IGame.{0}}, Membership.mem.{1, 1} (IGame.moves.{0} Player.left (Wpow.wpow.{1} x)) (Wpow.wpow.{1} y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.fits_of_equiv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.fits_of_equiv.h2 : ¬∀ {x y : IGame.{0}}, IGame.Fits.{0} x y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  (simp <;> game_cmp <;> done))

-- Surreal.round_of_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.round_of_pos.h2 : ¬∀ {x : Surreal.{0}} {r : Surreal.{0}}, LT.lt.{1} 0 r := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) ((0 : Surreal) : Surreal.{0})) (by
  simp)

-- Nimber.IsRing.ringClosure_eq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.ringClosure_eq.h1 : ¬∀ {x : Nimber.{0}}, Eq.{2} (Nimber.ringClosure.{0} x) x := fun hc_h => absurd (@hc_h (1)) (by
  simp)

-- Nimber.IsAlgClosed.fieldClosure_succ_pow_two, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsAlgClosed.fieldClosure_succ_pow_two.h1 : ¬∀ {t : Nimber.{0}}, Eq.{2} (HPow.hPow.{1, 0, 1} (Nimber.fieldClosure.{0} (Order.succ.{1} t)) 2) t := fun hc_h => absurd (@hc_h (1)) (by
  (simp <;> decide))

-- Nimber.IsGroup.one_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.one_le.h1 : ¬∀ {x : Nimber.{0}}, LE.le.{1} 1 x := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Surreal.mk_inv, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.mk_inv.h1 : ¬∀ (x : IGame.{0}), IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0})) (by
  simp)

-- IGame.Impartial.equiv_neg, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.equiv_neg.h1 : ¬∀ (x : IGame.{0}), x ≈ Neg.neg.{1} x := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- Real.toSurreal_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Real.toSurreal_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Surreal.mk_wlog, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.mk_wlog.h1 : ¬∀ (x : IGame.{0}), IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0})) (by
  simp)

-- Nimber.degree_leastNoRoots_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.degree_leastNoRoots_pos.h1 : ¬∀ {x : Nimber.{0}}, Ne.{2} (Nimber.leastNoRoots.{0} x) Top.top.{1} := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Dyadic.odd_num, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.odd_num.h1 : ¬∀ {x : Dyadic}, Odd x.num := fun hc_h => absurd (@hc_h (Dyadic.zero)) (by
  decide +kernel)

-- IGame.fuzzy_tiny_toIGame_birthday, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.fuzzy_tiny_toIGame_birthday.h1 : ¬∀ {x : IGame.{0}}, x ‖ IGame.tiny.{0} (NatOrdinal.toIGame.{0} (IGame.birthday.{0} x)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- Nimber.coe_toSubfield, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.coe_toSubfield.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- Surreal.IsOmnific.lt_one_iff_nonpos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.IsOmnific.lt_one_iff_nonpos.h1 : ¬∀ {x : Surreal.{0}}, LT.lt.{1} x 1 ↔ LE.le.{1} x 0 := fun hc_h => absurd (@hc_h (((1/2 : ℚ) : Surreal) : Surreal.{0})) (by
  norm_num)

-- IGame.switch_fuzzy_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.switch_fuzzy_zero.h1 : ¬∀ {x : IGame.{0}}, IGame.switch.{0} x ‖ 0 := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0})) (by
  (game_cmp; done))

