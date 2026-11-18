module
public import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- IGame.Numeric.mulOption_congr₃, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mulOption_congr₃.h10 : ¬∀ {x y a₁ a₂ b : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} a₁]
        [inst : IGame.Numeric.{0} a₂] [inst : IGame.Numeric.{0} b],
        IGame.mulOption.{0} x y a₁ b ≈ IGame.mulOption.{0} x y a₂ b := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _ _ _) (by
  (game_cmp; done))

-- Surreal.birthday_ofSets_lt_of_btwn, hypothesis 5: removable
/- FAILED: 2:0: unused universe parameter 'u' | 11:17: unsolved goals
s t : Set Surreal
z : Surreal
inst : Small.{u, u + 1} ↑s
inst_1 : Small.{u, u + 1} ↑t
hL : ∀ x ∈ s, x < z
hR : ∀ y ∈ t, z < y
x y : Surreal
a : x ∈ s
a_1 : y ∈ t
⊢ x < y | 2:0: unused universe parameter 'u' | 47:30: unsolved goals
s t : Set Surreal
z : Surreal
inst : Small.{u, u + 1} ↑s
inst_1 : Small.{u, u + 1} ↑t
hL : ∀ x ∈ s, x < z
hR : ∀ y ∈ t, z < y
x y : Surreal
a : x ∈ s
a_1 : y ∈ t
⊢ x < y | 2:0: unused universe parameter 'u' | 2:0: unused universe parameter 'u' | 2:0: unused universe parameter 'u'
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn.h5.der.{u} : ∀ {s t : Set Surreal} {z : Surreal} [inst : Small ↑s] [inst : Small ↑t],
      (∀ x ∈ s, x < z) → (∀ y ∈ t, z < y) → ∀ x ∈ s, ∀ y ∈ t, x < y := by
  (intros; grind)
theorem HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn.h5.{u} : ∀ {s t : Set Surreal} {z : Surreal} [inst : Small ↑s] [inst_1 : Small ↑t] (hL : ∀ x ∈ s, x < z) (hR : ∀ y ∈ t, z < y),
      !{s | t} ≠ z → !{s | t}.birthday < z.birthday := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7
  exact @Surreal.birthday_ofSets_lt_of_btwn hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6) hc_x5 hc_x6 hc_x7
-/

-- Surreal.birthday_ofSets_lt_of_btwn, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn.h8 : ¬∀ {s t : Set.{1} Surreal.{0}} {z : Surreal.{0}} [inst : Small.{0, 1} ↑s] [inst_1 : Small.{0, 1} ↑t]
        {H :
          ∀ (x : Surreal.{0}), Membership.mem.{1, 1} s x → ∀ (y : Surreal.{0}), Membership.mem.{1, 1} t y → LT.lt.{1} x y},
        (∀ (x : Surreal.{0}), Membership.mem.{1, 1} s x → LT.lt.{1} x z) →
          (∀ (y : Surreal.{0}), Membership.mem.{1, 1} t y → LT.lt.{1} z y) →
            LT.lt.{1} (Surreal.birthday.{0} !{s | t}) (Surreal.birthday.{0} z) := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h ((∅ : Set Surreal) : Set.{1} Surreal.{0}) ((∅ : Set Surreal) : Set.{1} Surreal.{0}) ((0 : Surreal) : Surreal.{0}) _ _ hc_k0 hc_k1 hc_k2) (by
  simp)

-- IGame.Numeric.div_lt_iff', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.div_lt_iff'.h6 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        LT.lt.{1} (HDiv.hDiv.{1, 1, 1} x y) z ↔ LT.lt.{1} x (HMul.hMul.{1, 1, 1} y z) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _) (by
  simp)

-- IGame.Numeric.mul_congr_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_congr_left.h6 : ¬∀ {x₁ x₂ y : IGame.{0}} [inst : IGame.Numeric.{0} x₁] [inst : IGame.Numeric.{0} x₂] [inst : IGame.Numeric.{0} y],
        HMul.hMul.{1, 1, 1} x₁ y ≈ HMul.hMul.{1, 1, 1} x₂ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _) (by
  (game_cmp; done))

-- GameGraph.impartial_toIGame, hypothesis 2: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.GameGraph.impartial_toIGame.h2.der.{u, v} : ∀ {α : Type v} {c : GameGraph.{v} α}
      [Hr : ∀ (a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.right a))]
      [inst : @GameGraph.WellFounded.{v} α c],
      @Eq.{v + 1} (α → Set.{v} α) (@GameGraph.moves.{v} α c Player.left) (@GameGraph.moves.{v} α c Player.right) →
        ∀ (a a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.left a)) := by
  (intros; simp_all; done)
theorem HypCheckProof.GameGraph.impartial_toIGame.h2.{u, v} : ∀ {α : Type v} {c : GameGraph.{v} α}
      [Hr : ∀ (a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.right a))]
      [inst : @GameGraph.WellFounded.{v} α c]
      (h : @Eq.{v + 1} (α → Set.{v} α) (@GameGraph.moves.{v} α c Player.left) (@GameGraph.moves.{v} α c Player.right))
      (a : α),
      (@GameGraph.toIGame.{u, v} α c (@HypCheckProof.GameGraph.impartial_toIGame.h2.der.{u, v} α c Hr inst h a) Hr inst
          a).Impartial := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @GameGraph.impartial_toIGame hc_x0 hc_x1 (@HypCheckProof.GameGraph.impartial_toIGame.h2.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x2 hc_x3 hc_x4 hc_x5

-- GameGraph.impartial_toIGame, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.GameGraph.impartial_toIGame.h3.der.{u, v} : ∀ {α : Type v} {c : GameGraph.{v} α}
      [Hl : ∀ (a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.left a))]
      [inst : @GameGraph.WellFounded.{v} α c],
      @Eq.{v + 1} (α → Set.{v} α) (@GameGraph.moves.{v} α c Player.left) (@GameGraph.moves.{v} α c Player.right) →
        ∀ (a a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.right a)) := by
  (intros; simp_all; done)
theorem HypCheckProof.GameGraph.impartial_toIGame.h3.{u, v} : ∀ {α : Type v} {c : GameGraph.{v} α}
      [Hl : ∀ (a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.left a))]
      [inst : @GameGraph.WellFounded.{v} α c]
      (h : @Eq.{v + 1} (α → Set.{v} α) (@GameGraph.moves.{v} α c Player.left) (@GameGraph.moves.{v} α c Player.right))
      (a : α),
      (@GameGraph.toIGame.{u, v} α c Hl (@HypCheckProof.GameGraph.impartial_toIGame.h3.der.{u, v} α c Hl inst h a) inst
          a).Impartial := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @GameGraph.impartial_toIGame hc_x0 hc_x1 hc_x2 (@HypCheckProof.GameGraph.impartial_toIGame.h3.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x3 hc_x4 hc_x5

-- IGame.Numeric.mul_le_mul_left_of_neg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_le_mul_left_of_neg.h6 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        LE.le.{1} (HMul.hMul.{1, 1, 1} z x) (HMul.hMul.{1, 1, 1} z y) ↔ LE.le.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ _) (by
  simp)

-- IGame.Numeric.wpow_lt_mul_wpow', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.wpow_lt_mul_wpow'.h5 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] {r : Dyadic},
        LT.lt.{1} x y → LT.lt.{1} (Wpow.wpow.{1} x) (HMul.hMul.{1, 1, 1} (↑r) (Wpow.wpow.{1} y)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ (Dyadic.zero) (by
  simp)) (by
  simp)

-- IGame.Numeric.wpow_lt_mul_wpow', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.wpow_lt_mul_wpow'.h6 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] {r : Dyadic},
        LT.lt.{0} 0 r → LT.lt.{1} (Wpow.wpow.{1} x) (HMul.hMul.{1, 1, 1} (↑r) (Wpow.wpow.{1} y)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ ((1 : Dyadic) : Dyadic) (by
  decide)) (by
  simp)

-- IGame.Numeric.mul_le_mul_right_of_neg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_le_mul_right_of_neg.h6 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        LE.le.{1} (HMul.hMul.{1, 1, 1} x z) (HMul.hMul.{1, 1, 1} y z) ↔ LE.le.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ _) (by
  simp)

-- IGame.mulOption_mem_moves_mul, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.mulOption_mem_moves_mul.h6 : ¬∀ {px py : Player} {x y a b : IGame.{0}},
        Membership.mem.{1, 1} (IGame.moves.{0} py y) b →
          Membership.mem.{1, 1} (IGame.moves.{0} (HMul.hMul.{0, 0, 0} px py) (HMul.hMul.{1, 1, 1} x y))
            (IGame.mulOption.{0} x y a b) := fun hc_h => absurd (@hc_h (Player.left : Player) (Player.left : Player) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  simp)

-- IGame.mulOption_mem_moves_mul, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.mulOption_mem_moves_mul.h7 : ¬∀ {px py : Player} {x y a b : IGame.{0}},
        Membership.mem.{1, 1} (IGame.moves.{0} px x) a →
          Membership.mem.{1, 1} (IGame.moves.{0} (HMul.hMul.{0, 0, 0} px py) (HMul.hMul.{1, 1, 1} x y))
            (IGame.mulOption.{0} x y a b) := fun hc_h => absurd (@hc_h (Player.left : Player) (Player.left : Player) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  simp)

-- IGame.Numeric.left_lt_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.left_lt_right.h5 : ¬∀ {x y z : IGame.{0}} [h : IGame.Numeric.{0} x],
        Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) y → LT.lt.{1} y z := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ (by
  simp)) (by
  simp)

-- Nimber.mul_ne_of_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.mul_ne_of_ne.h4 : ¬∀ {a b a' b' : Nimber.{0}},
        Ne.{2} b' b →
          Ne.{2}
            (HAdd.hAdd.{1, 1, 1} (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b) (HMul.hMul.{1, 1, 1} a b'))
              (HMul.hMul.{1, 1, 1} a' b'))
            (HMul.hMul.{1, 1, 1} a b) := fun hc_h => absurd (@hc_h (0) (0) (0) (1) (by
  simp)) (by
  simp)

-- Nimber.mul_ne_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.mul_ne_of_ne.h5 : ¬∀ {a b a' b' : Nimber.{0}},
        Ne.{2} a' a →
          Ne.{2}
            (HAdd.hAdd.{1, 1, 1} (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b) (HMul.hMul.{1, 1, 1} a b'))
              (HMul.hMul.{1, 1, 1} a' b'))
            (HMul.hMul.{1, 1, 1} a b) := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (by
  simp)) (by
  simp)

-- NatOrdinal.mul_add_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.mul_add_lt.h4 : ¬∀ {a b a' b' : NatOrdinal.{0}},
        LT.lt.{1} b' b →
          LT.lt.{1} (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b) (HMul.hMul.{1, 1, 1} a b'))
            (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b) (HMul.hMul.{1, 1, 1} a' b')) := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (by
  simp)) (by
  simp)

-- NatOrdinal.mul_add_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.mul_add_lt.h5 : ¬∀ {a b a' b' : NatOrdinal.{0}},
        LT.lt.{1} a' a →
          LT.lt.{1} (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b) (HMul.hMul.{1, 1, 1} a b'))
            (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b) (HMul.hMul.{1, 1, 1} a' b')) := fun hc_h => absurd (@hc_h (1) (0) (0) (0) (by
  simp)) (by
  simp)

-- IGame.Fits.surrealBirthday_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Fits.surrealBirthday_le.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst_1 : IGame.Numeric.{0} y],
        LE.le.{1} (Surreal.birthday.{0} (Surreal.mk.{0} y)) (Surreal.birthday.{0} (Surreal.mk.{0} x)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _) (by
  simp)

-- IGame.Small.numeric_le_of_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Small.numeric_le_of_neg.h4 : ¬∀ (x : IGame.{0}) [self : IGame.Small.{0} x] {y : IGame.{0}} [inst : IGame.Numeric.{0} y], LE.le.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _ ((1 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Fits.gameBirthday_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Fits.gameBirthday_lt.h3 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x],
        ¬x ≈ y → LT.lt.{1} (Game.birthday.{0} (Game.mk.{0} y)) (Surreal.birthday.{0} (Surreal.mk.{0} x)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ (by
  (game_cmp; done))) (by
  simp)

-- IGame.Fits.gameBirthday_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Fits.gameBirthday_lt.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x],
        IGame.Fits.{0} x y → LT.lt.{1} (Game.birthday.{0} (Game.mk.{0} y)) (Surreal.birthday.{0} (Surreal.mk.{0} x)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ (by
  simp)) (by
  simp)

-- Surreal.birthday_ofSets_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.birthday_ofSets_le.h4 : ¬∀ {s t : Set.{1} Surreal.{0}} [inst : Small.{0, 1} ↑s] [inst : Small.{0, 1} ↑t] (x : Surreal.{0}),
        Membership.mem.{1, 1} s x → ∀ (y : Surreal.{0}), Membership.mem.{1, 1} t y → LT.lt.{1} x y := fun hc_h => absurd (@hc_h (({0} : Set Surreal) : Set.{1} Surreal.{0}) (({0} : Set Surreal) : Set.{1} Surreal.{0}) _ _) (by
  simp)

-- Nimber.oeval_lt_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.oeval_lt_pow.h3 : ¬∀ {x : Nimber.{0}} {p : Polynomial.{1} Nimber.{0}} {n : ℕ},
        LT.lt.{0} (Polynomial.degree.{1} p) ↑n →
          LT.lt.{1} (Nimber.oeval.{0} x p) (Nimber.of.{0} (HPow.hPow.{1, 0, 1} (Nimber.val.{0} x) n)) := fun hc_h => absurd (@hc_h (0) (AddMonoidAlgebra.ofCoeff.{1, 0} 0) (1) (by
  decide)) (by
  simp)

-- NatOrdinal.add_lt_wpow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.add_lt_wpow.h3 : ¬∀ {x y z : NatOrdinal.{0}}, LT.lt.{1} y (Wpow.wpow.{1} z) → LT.lt.{1} (HAdd.hAdd.{1, 1, 1} x y) (Wpow.wpow.{1} z) := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  simp)) (by
  simp)

-- NatOrdinal.add_lt_wpow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.add_lt_wpow.h4 : ¬∀ {x y z : NatOrdinal.{0}}, LT.lt.{1} x (Wpow.wpow.{1} z) → LT.lt.{1} (HAdd.hAdd.{1, 1, 1} x y) (Wpow.wpow.{1} z) := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  simp)) (by
  simp)

-- Dyadic.mkRat_add_mkRat_self, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.mkRat_add_mkRat_self.h3.der : ∀ {m n : Int} {k : Nat},
      @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k →
        @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k := by
  (intros; assumption)
theorem HypCheckProof.Dyadic.mkRat_add_mkRat_self.h3 : ∀ {m n : Int} {k : Nat}
      (h₂ :
        @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k),
      @Eq Dyadic
        (@HAdd.hAdd Dyadic Dyadic Dyadic (@instHAdd Dyadic Dyadic.instAdd)
          (@Dyadic.mkRat m k (@HypCheckProof.Dyadic.mkRat_add_mkRat_self.h3.der m n k h₂)) (@Dyadic.mkRat n k h₂))
        (@Dyadic.mkRat (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) m n) k
          (@HypCheckProof.Dyadic.mkRat_add_mkRat_self.h3.der m n k h₂)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Dyadic.mkRat_add_mkRat_self hc_x0 hc_x1 hc_x2 (@HypCheckProof.Dyadic.mkRat_add_mkRat_self.h3.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x3

-- Dyadic.mkRat_add_mkRat_self, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.mkRat_add_mkRat_self.h4.der : ∀ {m n : Int} {k : Nat},
      @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k →
        @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k := by
  (intros; assumption)
theorem HypCheckProof.Dyadic.mkRat_add_mkRat_self.h4 : ∀ {m n : Int} {k : Nat}
      (h₁ :
        @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k),
      @Eq Dyadic
        (@HAdd.hAdd Dyadic Dyadic Dyadic (@instHAdd Dyadic Dyadic.instAdd) (@Dyadic.mkRat m k h₁)
          (@Dyadic.mkRat n k (@HypCheckProof.Dyadic.mkRat_add_mkRat_self.h4.der m n k h₁)))
        (@Dyadic.mkRat (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) m n) k h₁) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Dyadic.mkRat_add_mkRat_self hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Dyadic.mkRat_add_mkRat_self.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- Dyadic.mkRat_le_mkRat, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.mkRat_le_mkRat.h3.der : ∀ {m n : Int} {k : Nat},
      @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k →
        @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k := by
  (intros; assumption)
theorem HypCheckProof.Dyadic.mkRat_le_mkRat.h3 : ∀ {m n : Int} {k : Nat}
      (h₂ :
        @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k),
      Iff
        (@LE.le Dyadic Dyadic.instLE (@Dyadic.mkRat m k (@HypCheckProof.Dyadic.mkRat_le_mkRat.h3.der m n k h₂))
          (@Dyadic.mkRat n k h₂))
        (@LE.le Int Int.instLEInt m n) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Dyadic.mkRat_le_mkRat hc_x0 hc_x1 hc_x2 (@HypCheckProof.Dyadic.mkRat_le_mkRat.h3.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x3

-- Dyadic.mkRat_le_mkRat, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.mkRat_le_mkRat.h4.der : ∀ {m n : Int} {k : Nat},
      @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k →
        @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k := by
  (intros; assumption)
theorem HypCheckProof.Dyadic.mkRat_le_mkRat.h4 : ∀ {m n : Int} {k : Nat}
      (h₁ :
        @Membership.mem Nat (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid))
          (@SetLike.instMembership (@Submonoid Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)) Nat
            (@Submonoid.instSetLike Nat (@Monoid.toMulOneClass Nat Nat.instMonoid)))
          (@Submonoid.powers Nat Nat.instMonoid (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) k),
      Iff
        (@LE.le Dyadic Dyadic.instLE (@Dyadic.mkRat m k h₁)
          (@Dyadic.mkRat n k (@HypCheckProof.Dyadic.mkRat_le_mkRat.h4.der m n k h₁)))
        (@LE.le Int Int.instLEInt m n) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Dyadic.mkRat_le_mkRat hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Dyadic.mkRat_le_mkRat.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- IGame.Impartial.fuzzy_of_mem_moves, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.fuzzy_of_mem_moves.h1 : ¬∀ {x y : IGame.{0}} {p : Player}, Membership.mem.{1, 1} (IGame.moves.{0} p x) y → y ‖ x := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (Player.left : Player) (by
  simp)) (by
  (game_cmp; done))

-- IGame.Impartial.fuzzy_of_mem_moves, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.fuzzy_of_mem_moves.h4 : ¬∀ {x : IGame.{0}} [hx : IGame.Impartial.{0} x] {y : IGame.{0}} {p : Player}, y ‖ x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _ ((0 : IGame) : IGame.{0}) (Player.left : Player)) (by
  simp)

-- IGame.mul_wpow_mem_moves_left_wpow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.mul_wpow_mem_moves_left_wpow.h4 : ¬∀ {x y : IGame.{0}} {r : Dyadic},
        LE.le.{0} 0 r →
          Membership.mem.{1, 1} (IGame.moves.{0} Player.left (Wpow.wpow.{1} x)) (HMul.hMul.{1, 1, 1} (↑r) (Wpow.wpow.{1} y)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : Dyadic) : Dyadic) (by
  decide)) (by
  simp)

-- Surreal.mem_range_wpow_of_forall_mk_ne_mk, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.mem_range_wpow_of_forall_mk_ne_mk.h2 : Not
      (∀ {x : IGame.{0}} [inst : x.Numeric],
        (∀ (y : IGame.{0})
            (hy :
              @Membership.mem.{1, 1} IGame.{0} (Set.{1} IGame.{0}) (@Set.instMembership.{1} IGame.{0})
                (IGame.moves.{0} Player.left x) y),
            @LT.lt.{1} IGame.{0} (@Preorder.toLT.{1} IGame.{0} IGame.instPreorder.{0})
                (@OfNat.ofNat.{1} IGame.{0} (nat_lit 0) (@Zero.toOfNat0.{1} IGame.{0} IGame.instZero.{0})) y →
              @Ne.{2}
                (@ArchimedeanClass.{1} Surreal.{0}
                  (@Ring.toAddCommGroup.{1} Surreal.{0}
                    (@DivisionRing.toRing.{1} Surreal.{0} (@Field.toDivisionRing.{1} Surreal.{0} Surreal.instField.{0})))
                  Surreal.instLinearOrder.{0} Surreal.instIsOrderedAddMonoid.{0})
                (@ArchimedeanClass.mk.{1} Surreal.{0}
                  (@Ring.toAddCommGroup.{1} Surreal.{0}
                    (@DivisionRing.toRing.{1} Surreal.{0} (@Field.toDivisionRing.{1} Surreal.{0} Surreal.instField.{0})))
                  Surreal.instLinearOrder.{0} Surreal.instIsOrderedAddMonoid.{0}
                  (@Surreal.mk.{0} y (@IGame.Numeric.of_mem_moves.{0} x y Player.left inst hy)))
                (@ArchimedeanClass.mk.{1} Surreal.{0}
                  (@Ring.toAddCommGroup.{1} Surreal.{0}
                    (@DivisionRing.toRing.{1} Surreal.{0} (@Field.toDivisionRing.{1} Surreal.{0} Surreal.instField.{0})))
                  Surreal.instLinearOrder.{0} Surreal.instIsOrderedAddMonoid.{0} (@Surreal.mk.{0} x inst))) →
          (∀ (y : IGame.{0})
              (hy :
                @Membership.mem.{1, 1} IGame.{0} (Set.{1} IGame.{0}) (@Set.instMembership.{1} IGame.{0})
                  (IGame.moves.{0} Player.right x) y),
              @Ne.{2}
                (@ArchimedeanClass.{1} Surreal.{0}
                  (@Ring.toAddCommGroup.{1} Surreal.{0}
                    (@DivisionRing.toRing.{1} Surreal.{0} (@Field.toDivisionRing.{1} Surreal.{0} Surreal.instField.{0})))
                  Surreal.instLinearOrder.{0} Surreal.instIsOrderedAddMonoid.{0})
                (@ArchimedeanClass.mk.{1} Surreal.{0}
                  (@Ring.toAddCommGroup.{1} Surreal.{0}
                    (@DivisionRing.toRing.{1} Surreal.{0} (@Field.toDivisionRing.{1} Surreal.{0} Surreal.instField.{0})))
                  Surreal.instLinearOrder.{0} Surreal.instIsOrderedAddMonoid.{0}
                  (@Surreal.mk.{0} y (@IGame.Numeric.of_mem_moves.{0} x y Player.right inst hy)))
                (@ArchimedeanClass.mk.{1} Surreal.{0}
                  (@Ring.toAddCommGroup.{1} Surreal.{0}
                    (@DivisionRing.toRing.{1} Surreal.{0} (@Field.toDivisionRing.{1} Surreal.{0} Surreal.instField.{0})))
                  Surreal.instLinearOrder.{0} Surreal.instIsOrderedAddMonoid.{0} (@Surreal.mk.{0} x inst))) →
            @Membership.mem.{1, 1} Surreal.{0} (Set.{1} Surreal.{0}) (@Set.instMembership.{1} Surreal.{0})
              (@Set.range.{1, 2} Surreal.{0} Surreal.{0} fun (x : Surreal.{0}) =>
                @Wpow.wpow.{1} Surreal.{0} Surreal.instWpow.{0} x)
              (@Surreal.mk.{0} x inst)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _ (by
  simp) (by
  simp)) (by
  simp)

-- Surreal.Cut.left_lt_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.left_lt_right.h3 : ¬∀ {x : Surreal.Cut.{0}} {y z : Surreal.{0}}, Membership.mem.{1, 1} (Surreal.Cut.right.{0} x) z → LT.lt.{1} y z := fun hc_h => absurd (@hc_h (Bot.bot.{1}) ((0 : Surreal) : Surreal.{0}) ((0 : Surreal) : Surreal.{0}) (by
  simp)) (by
  simp)

-- Surreal.Cut.left_lt_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.left_lt_right.h4 : ¬∀ {x : Surreal.Cut.{0}} {y z : Surreal.{0}}, Membership.mem.{1, 1} (Surreal.Cut.left.{0} x) y → LT.lt.{1} y z := fun hc_h => absurd (@hc_h (Top.top.{1}) ((0 : Surreal) : Surreal.{0}) ((0 : Surreal) : Surreal.{0}) (by
  simp)) (by
  simp)

-- IGame.Fits.gameBirthday_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Fits.gameBirthday_le.h3 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x],
        LE.le.{1} (Game.birthday.{0} (Game.mk.{0} y)) (Surreal.birthday.{0} (Surreal.mk.{0} x)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Impartial.le_comm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.le_comm.h2 : ¬∀ {x y : IGame.{0}} [inst : IGame.Impartial.{0} y], LE.le.{1} x y ↔ LE.le.{1} y x := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Impartial.le_comm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.le_comm.h3 : ¬∀ {x y : IGame.{0}} [inst : IGame.Impartial.{0} x], LE.le.{1} x y ↔ LE.le.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _) (by
  simp)

-- le_iff_equiv_of_neg_equiv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.le_iff_equiv_of_neg_equiv.h2 : ¬∀ {x y : IGame.{0}}, Neg.neg.{1} y ≈ y → (LE.le.{1} x y ↔ x ≈ y) := fun hc_h => absurd (@hc_h ((-1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  (simp <;> game_cmp <;> done))

-- le_iff_equiv_of_neg_equiv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.le_iff_equiv_of_neg_equiv.h3 : ¬∀ {x y : IGame.{0}}, Neg.neg.{1} x ≈ x → (LE.le.{1} x y ↔ x ≈ y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  simp)) (by
  (simp <;> game_cmp <;> done))

-- IGame.Impartial.grundy_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.grundy_eq.h3 : ¬∀ {x : IGame.{0}} [inst : IGame.Impartial.{0} x] {o : Nimber.{0}}, Eq.{2} (IGame.Impartial.grundy.{0} x) o := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _ (1)) (by
  simp)

-- IGame.le_miny_of_neg_of_forall_le_neg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.le_miny_of_neg_of_forall_le_neg.h2 : ¬∀ {x a : IGame.{0}},
        (∀ (y : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) y →
              ∀ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) z → LE.le.{1} z a) →
          LE.le.{1} x (IGame.miny.{0} a) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  (game_cmp; done))

-- IGame.fuzzy_miny_of_birthday_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.fuzzy_miny_of_birthday_le.h1 : ¬∀ {x o : IGame.{0}}, LE.le.{1} (NatOrdinal.toIGame.{0} (IGame.birthday.{0} x)) o → x ‖ IGame.miny.{0} o := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  (game_cmp; done))

-- IGame.toIGame_equiv_iff_eq_toDyadic, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.toIGame_equiv_iff_eq_toDyadic.h2 : ¬∀ {x : IGame.{0}} [inst : IGame.Short.{0} x] {y : Dyadic}, IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) _ (Dyadic.zero)) (by
  simp)

-- IGame.equiv_toIGame_iff_toDyadic_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.equiv_toIGame_iff_toDyadic_eq.h2 : ¬∀ {x : IGame.{0}} [inst : IGame.Short.{0} x] {y : Dyadic}, IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) _ (Dyadic.zero)) (by
  simp)

-- SignType.orderingEquiv_symm_cmp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignType.orderingEquiv_symm_cmp.h3 : ¬∀ {α : Type} [inst : AddGroup α] [inst_1 : LinearOrder α] (x y : α),
        SignType.orderingEquiv.symm (cmp x y) = SignType.sign (x - y) := fun hc_h => absurd (@hc_h (Fin 2) ((Fin.addCommGroup 2).toAddGroup) (Fin.instLinearOrder) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Nimber.IsRing.toSubring_le_toSubring, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.toSubring_le_toSubring.h2 : ¬∀ {x y : Nimber.{0}}, Nimber.IsRing.{0} y → Nimber.IsRing.{0} x := fun hc_h => absurd (@hc_h (0) (Nimber.of 2 : Nimber.{0}) (by
  simp)) (by
  nofun)

-- Nimber.IsRing.toSubring_le_toSubring, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.toSubring_le_toSubring.h3 : ¬∀ {x y : Nimber.{0}}, Nimber.IsRing.{0} x → Nimber.IsRing.{0} y := fun hc_h => absurd (@hc_h (Nimber.of 2 : Nimber.{0}) (0) (by
  simp)) (by
  nofun)

-- Nimber.IsGroup.add_eq_of_lt', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.add_eq_of_lt'.h3 : ¬∀ {x y : Ordinal.{0}},
        Nimber.IsGroup.{0} (Nimber.of.{0} x) →
          Eq.{2} (HAdd.hAdd.{1, 1, 1} x y) (Nimber.val.{0} (HAdd.hAdd.{1, 1, 1} (Nimber.of.{0} x) (Nimber.of.{0} y))) := fun hc_h => absurd (@hc_h ((1 : Ordinal) : Ordinal.{0}) ((1 : Ordinal) : Ordinal.{0}) (by
  simp)) (by
  norm_num)

-- Surreal.wlog_lt_wlog_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.wlog_lt_wlog_iff.h2 : ¬∀ {x y : Surreal.{0}}, Ne.{2} y 0 → (LT.lt.{1} (Surreal.wlog.{0} x) (Surreal.wlog.{0} y) ↔ ValuativeRel.vlt.{1} x y) := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0}) (by
  simp)) (by
  simp)

-- IGame.sub_right_mem_moves_sub, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.sub_right_mem_moves_sub.h3 : ¬∀ {p : Player} {x y : IGame.{0}} (z : IGame.{0}),
        Membership.mem.{1, 1} (IGame.moves.{0} p (HSub.hSub.{1, 1, 1} y z)) (HSub.hSub.{1, 1, 1} x z) := fun hc_h => absurd (@hc_h (Player.left : Player) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.toIGame_toDyadic_equiv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.toIGame_toDyadic_equiv.h2 : ¬∀ (x : IGame.{0}) [inst : IGame.Short.{0} x], IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) _) (by
  simp)

-- Surreal.Cut.infRight_mem_of_short, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.infRight_mem_of_short.h2 : ¬∀ {x : IGame.{0}} [inst : IGame.Short.{0} x],
        ∃ (y : IGame.{0}),
          Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) y ∧
            Eq.{2} (Surreal.Cut.leftGame.{0} (Game.mk.{0} y)) (Surreal.Cut.infRight.{0} x) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.zsmul_congr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.zsmul_congr.h3 : ¬∀ {n : ℤ} {a b : IGame.{0}}, HSMul.hSMul.{0, 1, 1} n a ≈ HSMul.hSMul.{0, 1, 1} n b := fun hc_h => absurd (@hc_h (1) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  (simp <;> game_cmp <;> done))

-- Nimber.IsField.sq_lt_self_of_not_perfectField, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.sq_lt_self_of_not_perfectField.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- IGame.nsmul_congr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.nsmul_congr.h3 : ¬∀ {n : ℕ} {a b : IGame.{0}}, HSMul.hSMul.{0, 1, 1} n a ≈ HSMul.hSMul.{0, 1, 1} n b := fun hc_h => absurd (@hc_h (1) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  (simp <;> game_cmp <;> done))

-- NatOrdinal.wpow_mul_natCast_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.wpow_mul_natCast_lt.h2 : ¬∀ {x y : NatOrdinal.{0}} (n : ℕ), LT.lt.{1} (HMul.hMul.{1, 1, 1} (Wpow.wpow.{1} x) ↑n) (Wpow.wpow.{1} y) := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- IGame.add_congr_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.add_congr_left.h3 : ¬∀ {a b c : IGame.{0}}, HAdd.hAdd.{1, 1, 1} a c ≈ HAdd.hAdd.{1, 1, 1} b c := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- IGame.ordinalSum_le_ordinalSum_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.ordinalSum_le_ordinalSum_right.h3 : ¬∀ (x : IGame.{0}) {y z : IGame.{0}}, LE.le.{1} (IGame.ordinalSum.{0} x y) (IGame.ordinalSum.{0} x z) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.ordinalSum_lf_iff_of_forall_wsubposition, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.ordinalSum_lf_iff_of_forall_wsubposition.h3 : ¬∀ {x y z : IGame.{0}}, ¬LE.le.{1} z (IGame.ordinalSum.{0} x y) ↔ ¬LE.le.{1} z x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  simp)

-- Nimber.exists_of_lt_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.exists_of_lt_mul.h3 : ¬∀ {a b c : Nimber.{0}},
        ∃ (a' : Nimber.{0}),
          LT.lt.{1} a' a ∧
            ∃ (b' : Nimber.{0}),
              LT.lt.{1} b' b ∧
                Eq.{2}
                  (HAdd.hAdd.{1, 1, 1} (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b) (HMul.hMul.{1, 1, 1} a b'))
                    (HMul.hMul.{1, 1, 1} a' b'))
                  c := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- Surreal.Cut.Fits.rightSurreal_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.Fits.rightSurreal_le.h3 : ¬∀ {x : Surreal.{0}} {y : Surreal.Cut.{0}} {z : Surreal.Cut.{0}}, LE.le.{1} (Surreal.Cut.rightSurreal.{0} x) z := fun hc_h => absurd (@hc_h ((1 : Surreal) : Surreal.{0}) (Bot.bot.{1}) (Bot.bot.{1})) (by
  (simp <;> omega))

-- NatOrdinal.lt_wpow_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.lt_wpow_iff.h2 : ¬∀ {x y : NatOrdinal.{0}},
        LT.lt.{1} y (Wpow.wpow.{1} x) ↔
          ∃ (z : NatOrdinal.{0}), LT.lt.{1} z x ∧ ∃ (n : ℕ), LT.lt.{1} y (HMul.hMul.{1, 1, 1} (Wpow.wpow.{1} z) ↑n) := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Nimber.val_toAddSubgroup_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.val_toAddSubgroup_lt.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsGroup.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- Nimber.val_toSubfield_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.val_toSubfield_lt.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- Nimber.val_toSubring_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.val_toSubring_lt.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsRing.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- Nimber.leastNoRoots_ne_X_pow', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.leastNoRoots_ne_X_pow'.h1 : ¬∀ (x : Nimber.{0}) (n : ℕ), Ne.{2} (Nimber.leastNoRoots.{0} x) Top.top.{1} := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Nimber.opow_natDegree_le_oeval, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.opow_natDegree_le_oeval.h2 : ¬∀ (x : Nimber.{0}) {p : Polynomial.{1} Nimber.{0}},
        LE.le.{1} (Nimber.of.{0} (HPow.hPow.{1, 0, 1} (Nimber.val.{0} x) (Polynomial.natDegree.{1} p)))
          (Nimber.oeval.{0} x p) := fun hc_h => absurd (@hc_h (0) (AddMonoidAlgebra.ofCoeff.{1, 0} 0)) (by
  simp)

-- IGame.eq_natCast_of_mem_moves_left_natCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.eq_natCast_of_mem_moves_left_natCast.h2 : ¬∀ {n : ℕ} {x : IGame.{0}}, ∃ (m : ℕ), LT.lt.{0} m n ∧ Eq.{2} (↑m) x := fun hc_h => absurd (@hc_h (0) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.neg_congr, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.neg_congr.h2 : ¬∀ {x y : IGame.{0}}, Neg.neg.{1} x ≈ Neg.neg.{1} y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- Nimber.coeff_zero_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.coeff_zero_lt.h1 : ¬∀ {x : Nimber.{0}} (k : ℕ), LT.lt.{1} ((AddMonoidAlgebra.coeff.{1, 0} 0) k) x := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Nimber.sqrt_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.sqrt_eq.h2 : ¬∀ {x y : Nimber.{0}}, Eq.{2} (Nimber.sqrt.{0} y) x := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- Nimber.of_omega0_opow_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.of_omega0_opow_add.h2 : ¬∀ {x y : Ordinal.{0}},
        Eq.{2} (Nimber.of.{0} (HAdd.hAdd.{1, 1, 1} (HPow.hPow.{1, 1, 1} Ordinal.omega0.{0} x) y))
          (HAdd.hAdd.{1, 1, 1} (Nimber.of.{0} (HPow.hPow.{1, 1, 1} Ordinal.omega0.{0} x)) (Nimber.of.{0} y)) := fun hc_h => absurd (@hc_h ((0 : Ordinal) : Ordinal.{0}) (Ordinal.omega0 : Ordinal.{0})) (by
  simp)

-- IGame.Impartial.sub_equiv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.sub_equiv.h2 : ¬∀ (x y : IGame.{0}), HSub.hSub.{1, 1, 1} x y ≈ HAdd.hAdd.{1, 1, 1} x y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- Surreal.leadingTerm_add_eq_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.leadingTerm_add_eq_right.h2 : ¬∀ {x y : Surreal.{0}}, Eq.{2} (Surreal.leadingTerm.{0} (HAdd.hAdd.{1, 1, 1} y x)) (Surreal.leadingTerm.{0} x) := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0})) (by
  simp)

-- Surreal.leadingCoeff_add_eq_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.leadingCoeff_add_eq_left.h2 : ¬∀ {x y : Surreal.{0}}, Eq.{1} (Surreal.leadingCoeff.{0} (HAdd.hAdd.{1, 1, 1} x y)) (Surreal.leadingCoeff.{0} x) := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0})) (by
  simp)

-- IGame.Numeric.zsmul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.zsmul.h2 : ¬∀ (n : ℤ) (x : IGame.{0}), IGame.Numeric.{0} (HSMul.hSMul.{0, 1, 1} n x) := fun hc_h => absurd (@hc_h (1) (IGame.star : IGame.{0})) (by
  simp)

-- Surreal.Cut.fits_supLeft_infRight, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.fits_supLeft_infRight.h2 : ¬∀ {x : IGame.{0}} {y : IGame.{0}}, IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- Nimber.IsGroup.groupClosure_eq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.groupClosure_eq.h1 : ¬∀ {x : Nimber.{0}}, Eq.{2} (Nimber.groupClosure.{0} x) x := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Dyadic.isSome_precision_eq_true_of_den_ne_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.isSome_precision_eq_true_of_den_ne_one.h1 : ¬∀ {x : Dyadic}, x.precision.isSome = Bool.true := fun hc_h => absurd (@hc_h (Dyadic.zero)) (by
  decide +kernel)

-- IGame.moves_left_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.moves_left_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nimber.one_le_natDegree_leastNoRoots, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.one_le_natDegree_leastNoRoots.h1 : ¬∀ {x : Nimber.{0}}, Ne.{2} (Nimber.leastNoRoots.{0} x) Top.top.{1} := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Nimber.IsGroup.zero_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.zero_lt.h1 : ¬∀ {x : Nimber.{0}}, LT.lt.{1} 0 x := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Dyadic.intCast_num_eq_self_of_den_eq_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.intCast_num_eq_self_of_den_eq_one.h1 : ¬∀ {x : Dyadic}, ↑x.num = x := fun hc_h => absurd (@hc_h (Dyadic.half : Dyadic)) (by
  decide +kernel)

-- Surreal.mk_div_wpow_wlog_of_ne_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.mk_div_wpow_wlog_of_ne_zero.h1 : ¬∀ {x : Surreal.{0}}, Eq.{2} (ArchimedeanClass.mk.{1} (HDiv.hDiv.{1, 1, 1} x (Wpow.wpow.{1} (Surreal.wlog.{0} x)))) 0 := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0})) (by
  simp)

-- IGame.birthday_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.birthday_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Surreal.mk_wpow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.mk_wpow.h1 : ¬∀ (x : IGame.{0}), IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0})) (by
  simp)

-- Nimber.IsRing.closure_Iio, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.closure_Iio.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsRing.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- Nimber.IsGroup.ne_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.ne_zero.h1 : ¬∀ {x : Nimber.{0}}, Ne.{2} x 0 := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- ne_zero_of_mem_powers, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ne_zero_of_mem_powers.h1 : ¬∀ {n : ℕ}, n ≠ 0 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Dyadic.mkRat_one, hypothesis 1: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Dyadic.mkRat_one.h1.der : ∀ (m : ℤ), 1 ∈ Submonoid.powers 2 := by
  (intros; solve_by_elim)
theorem HypCheckProof.Dyadic.mkRat_one.h1 : ∀ (m : ℤ), Dyadic.mkRat m (HypCheckProof.Dyadic.mkRat_one.h1.der m) = ↑m := by
  intro hc_x0
  exact @Dyadic.mkRat_one hc_x0 (@HypCheckProof.Dyadic.mkRat_one.h1.der hc_x0)

-- IGame.Dicotic.eq_zero_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Dicotic.eq_zero_iff.h1 : ¬∀ {x : IGame.{0}}, Eq.{2} x 0 ↔ ∃ (p : Player), Eq.{2} (IGame.moves.{0} p x) EmptyCollection.emptyCollection.{1} := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0})) (by
  simp)

-- NatOrdinal.bddAbove_of_small, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.bddAbove_of_small.h1 : ¬∀ (s : Set.{1} NatOrdinal.{0}), BddAbove.{1} s := fun hc_h => absurd (@hc_h (Top.top.{1})) (by
  simp)

-- Surreal.Cut.rightGame_mk_of_numeric, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.rightGame_mk_of_numeric.h1 : ¬∀ (x : IGame.{0}), IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0})) (by
  simp)

-- Nimber.IsAlgClosed.toIsField, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsAlgClosed.toIsField.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- Nimber.IsAlgClosed.transcendental, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsAlgClosed.transcendental.h1 : ¬∀ {t : Nimber.{0}}, Nimber.IsAlgClosed.{0} t := fun hc_h => absurd (@hc_h (1)) (by
  nofun)

