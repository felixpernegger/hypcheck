module
public import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- IsClub.exists_between_closure, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsClub.exists_between_closure.h10 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : WellFoundedLT α] [inst_2 : NoMaxOrder α] [inst_3 : SuccOrder α]
        {s : Set α},
        IsClub s → ∀ {x : α}, (∃ y ∈ s, y ≤ x) → ∀ {c : α → α}, (∀ (x : α), c x ∈ s) → ∃ l ∈ s, l ≤ x ∧ x < c (Order.succ l) := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) _ _ (Nat.instSuccOrder) ({x : ℕ | True}) (by
  simp) (0) (by
  simp) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- IGame.Numeric.mul_lt_mul_iff_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_lt_mul_iff_right.h6 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        LT.lt.{1} (HMul.hMul.{1, 1, 1} x y) (HMul.hMul.{1, 1, 1} x z) ↔ LT.lt.{1} y z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _) (by
  simp)

-- GameGraph.neg_toIGame, hypothesis 2: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.GameGraph.neg_toIGame.h2.der.{u, v} : ∀ {α : Type v} {c : GameGraph.{v} α}
      [Hr : ∀ (a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.right a))]
      [inst : @GameGraph.WellFounded.{v} α c],
      @Eq.{v + 1} (α → Set.{v} α) (@GameGraph.moves.{v} α c Player.left) (@GameGraph.moves.{v} α c Player.right) →
        ∀ (a a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.left a)) := by
  (intros; simp_all; done)
theorem HypCheckProof.GameGraph.neg_toIGame.h2.{u, v} : ∀ {α : Type v} {c : GameGraph.{v} α}
      [Hr : ∀ (a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.right a))]
      [inst : @GameGraph.WellFounded.{v} α c]
      (h : @Eq.{v + 1} (α → Set.{v} α) (@GameGraph.moves.{v} α c Player.left) (@GameGraph.moves.{v} α c Player.right))
      (a : α),
      @Eq.{u + 2} IGame.{u}
        (@Neg.neg.{u + 1} IGame.{u} IGame.instNeg.{u}
          (@GameGraph.toIGame.{u, v} α c (@HypCheckProof.GameGraph.neg_toIGame.h2.der.{u, v} α c Hr inst h a) Hr inst a))
        (@GameGraph.toIGame.{u, v} α c (@HypCheckProof.GameGraph.neg_toIGame.h2.der.{u, v} α c Hr inst h a) Hr inst a) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @GameGraph.neg_toIGame hc_x0 hc_x1 (@HypCheckProof.GameGraph.neg_toIGame.h2.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x2 hc_x3 hc_x4 hc_x5

-- GameGraph.neg_toIGame, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.GameGraph.neg_toIGame.h3.der.{u, v} : ∀ {α : Type v} {c : GameGraph.{v} α}
      [Hl : ∀ (a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.left a))]
      [inst : @GameGraph.WellFounded.{v} α c],
      @Eq.{v + 1} (α → Set.{v} α) (@GameGraph.moves.{v} α c Player.left) (@GameGraph.moves.{v} α c Player.right) →
        ∀ (a a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.right a)) := by
  (intros; simp_all; done)
theorem HypCheckProof.GameGraph.neg_toIGame.h3.{u, v} : ∀ {α : Type v} {c : GameGraph.{v} α}
      [Hl : ∀ (a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.left a))]
      [inst : @GameGraph.WellFounded.{v} α c]
      (h : @Eq.{v + 1} (α → Set.{v} α) (@GameGraph.moves.{v} α c Player.left) (@GameGraph.moves.{v} α c Player.right))
      (a : α),
      @Eq.{u + 2} IGame.{u}
        (@Neg.neg.{u + 1} IGame.{u} IGame.instNeg.{u}
          (@GameGraph.toIGame.{u, v} α c Hl (@HypCheckProof.GameGraph.neg_toIGame.h3.der.{u, v} α c Hl inst h a) inst a))
        (@GameGraph.toIGame.{u, v} α c Hl (@HypCheckProof.GameGraph.neg_toIGame.h3.der.{u, v} α c Hl inst h a) inst a) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @GameGraph.neg_toIGame hc_x0 hc_x1 hc_x2 (@HypCheckProof.GameGraph.neg_toIGame.h3.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x3 hc_x4 hc_x5

-- IGame.Numeric.div_lt_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.div_lt_iff.h6 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        LT.lt.{1} (HDiv.hDiv.{1, 1, 1} x y) z ↔ LT.lt.{1} x (HMul.hMul.{1, 1, 1} z y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _) (by
  simp)

-- Surreal.birthday_ofSets_le_of_btwn', hypothesis 4: removable
/- FAILED: 2:0: unused universe parameter 'u' | 14:42: unsolved goals
st : Player → Set Surreal
z : Surreal
inst : Small.{u, u + 1} ↑(st Player.left)
inst_1 : Small.{u, u + 1} ↑(st Player.right)
hL : ∀ x ∈ st Player.left, x < z
hR : ∀ y ∈ st Player.right, z < y
x : Surreal
a : x ∈ st Player.left
y : Surreal
a_1 : y ∈ st Player.right
⊢ x < y | 2:0: unused universe parameter 'u' | 52:8: unsolved goals
st : Player → Set Surreal
z : Surreal
inst : Small.{u, u + 1} ↑(st Player.left)
inst_1 : Small.{u, u + 1} ↑(st Player.right)
hL : ∀ x ∈ st Player.left, x < z
hR : ∀ y ∈ st Player.right, z < y
x : Surreal
a : x ∈ st Player.left
y : Surreal
a_1 : y ∈ st Player.right
⊢ x < y | 2:0: unused universe parameter 'u' | 2:0: unused universe parameter 'u' | 2:0: unused universe parameter 'u'
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Surreal.birthday_ofSets_le_of_btwn'.h4.der.{u} : ∀ {st : Player → Set Surreal} {z : Surreal} [inst : Small ↑(st Player.left)] [inst : Small ↑(st Player.right)],
      (∀ x ∈ st Player.left, x < z) → (∀ y ∈ st Player.right, z < y) → ∀ x ∈ st Player.left, ∀ y ∈ st Player.right, x < y := by
  (intros; grind)
theorem HypCheckProof.Surreal.birthday_ofSets_le_of_btwn'.h4.{u} : ∀ {st : Player → Set Surreal} {z : Surreal} [inst : Small ↑(st Player.left)] [inst_1 : Small ↑(st Player.right)]
      (hL : ∀ x ∈ st Player.left, x < z) (hR : ∀ y ∈ st Player.right, z < y), !{st}.birthday ≤ z.birthday := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Surreal.birthday_ofSets_le_of_btwn' hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Surreal.birthday_ofSets_le_of_btwn'.h4.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x4 hc_x5
-/

-- GameGraph.neg_toLGame, hypothesis 2: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.GameGraph.neg_toLGame.h2.der.{u, v} : ∀ {α : Type v} {c : GameGraph.{v} α}
      [Hr : ∀ (a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.right a))],
      @Eq.{v + 1} (α → Set.{v} α) (@GameGraph.moves.{v} α c Player.left) (@GameGraph.moves.{v} α c Player.right) →
        ∀ (a a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.left a)) := by
  (intros; simp_all; done)
theorem HypCheckProof.GameGraph.neg_toLGame.h2.{u, v} : ∀ {α : Type v} {c : GameGraph.{v} α}
      [Hr : ∀ (a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.right a))]
      (h : @Eq.{v + 1} (α → Set.{v} α) (@GameGraph.moves.{v} α c Player.left) (@GameGraph.moves.{v} α c Player.right))
      (a : α),
      @Eq.{u + 2} LGame.{u}
        (@Neg.neg.{u + 1} LGame.{u} LGame.instNeg.{u}
          (@GameGraph.toLGame.{u, v} α c (@HypCheckProof.GameGraph.neg_toLGame.h2.der.{u, v} α c Hr h a) Hr a))
        (@GameGraph.toLGame.{u, v} α c (@HypCheckProof.GameGraph.neg_toLGame.h2.der.{u, v} α c Hr h a) Hr a) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @GameGraph.neg_toLGame hc_x0 hc_x1 (@HypCheckProof.GameGraph.neg_toLGame.h2.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4) hc_x2 hc_x3 hc_x4

-- GameGraph.neg_toLGame, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.GameGraph.neg_toLGame.h3.der.{u, v} : ∀ {α : Type v} {c : GameGraph.{v} α}
      [Hl : ∀ (a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.left a))],
      @Eq.{v + 1} (α → Set.{v} α) (@GameGraph.moves.{v} α c Player.left) (@GameGraph.moves.{v} α c Player.right) →
        ∀ (a a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.right a)) := by
  (intros; simp_all; done)
theorem HypCheckProof.GameGraph.neg_toLGame.h3.{u, v} : ∀ {α : Type v} {c : GameGraph.{v} α}
      [Hl : ∀ (a : α), Small.{u, v} (@Set.Elem.{v} α (@GameGraph.moves.{v} α c Player.left a))]
      (h : @Eq.{v + 1} (α → Set.{v} α) (@GameGraph.moves.{v} α c Player.left) (@GameGraph.moves.{v} α c Player.right))
      (a : α),
      @Eq.{u + 2} LGame.{u}
        (@Neg.neg.{u + 1} LGame.{u} LGame.instNeg.{u}
          (@GameGraph.toLGame.{u, v} α c Hl (@HypCheckProof.GameGraph.neg_toLGame.h3.der.{u, v} α c Hl h a) a))
        (@GameGraph.toLGame.{u, v} α c Hl (@HypCheckProof.GameGraph.neg_toLGame.h3.der.{u, v} α c Hl h a) a) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @GameGraph.neg_toLGame hc_x0 hc_x1 hc_x2 (@HypCheckProof.GameGraph.neg_toLGame.h3.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4) hc_x3 hc_x4

-- IGame.equiv_of_forall_lf, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.equiv_of_forall_lf.h2 : ¬∀ {x y : IGame.{0}},
        (∀ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) a → ¬LE.le.{1} a y) →
          (∀ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) b → ¬LE.le.{1} x b) →
            (∀ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) b → ¬LE.le.{1} b x) → x ≈ y := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp) (by
  simp) (by
  simp)) (by
  (game_cmp; done))

-- IGame.equiv_of_forall_lf, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.equiv_of_forall_lf.h3 : ¬∀ {x y : IGame.{0}},
        (∀ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) a → ¬LE.le.{1} y a) →
          (∀ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) b → ¬LE.le.{1} x b) →
            (∀ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) b → ¬LE.le.{1} b x) → x ≈ y := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  simp) (by
  simp) (by
  simp)) (by
  (game_cmp; done))

-- IGame.equiv_of_forall_lf, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.equiv_of_forall_lf.h4 : ¬∀ {x y : IGame.{0}},
        (∀ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) a → ¬LE.le.{1} y a) →
          (∀ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) a → ¬LE.le.{1} a y) →
            (∀ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) b → ¬LE.le.{1} b x) → x ≈ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  simp) (by
  simp) (by
  simp)) (by
  (game_cmp; done))

-- IGame.equiv_of_forall_lf, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.equiv_of_forall_lf.h5 : ¬∀ {x y : IGame.{0}},
        (∀ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) a → ¬LE.le.{1} y a) →
          (∀ (a : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) a → ¬LE.le.{1} a y) →
            (∀ (b : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) b → ¬LE.le.{1} x b) → x ≈ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((-1 : IGame) : IGame.{0}) (by
  simp) (by
  simp) (by
  simp)) (by
  (game_cmp; done))

-- IGame.Numeric.mul_nonpos_of_nonneg_of_nonpos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_nonpos_of_nonneg_of_nonpos.h5 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y],
        LE.le.{1} 0 x → LE.le.{1} (HMul.hMul.{1, 1, 1} x y) 0 := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ (by
  simp)) (by
  simp)

-- Nimber.eq_oeval_of_lt_oeval, hypothesis 3: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Nimber.eq_oeval_of_lt_oeval.h3.gneg.{u_1} : ∀ {x y : Nimber.{u_1}} {p : Polynomial.{u_1 + 1} Nimber.{u_1}},
      ¬Ne.{u_1 + 2} x 0 →
        (∀ (k : ℕ), LT.lt.{u_1 + 1} ((AddMonoidAlgebra.coeff.{u_1 + 1, 0} p) k) x) →
          LT.lt.{u_1 + 1} y (Nimber.oeval.{u_1} x p) →
            ∃ (q : Polynomial.{u_1 + 1} Nimber.{u_1}),
              LT.lt.{u_1 + 1} q p ∧
                (∀ (k : ℕ), LT.lt.{u_1 + 1} ((AddMonoidAlgebra.coeff.{u_1 + 1, 0} q) k) x) ∧
                  Eq.{u_1 + 2} (Nimber.oeval.{u_1} x q) y := by
  (intros; simp_all; done)
theorem HypCheckProof.Nimber.eq_oeval_of_lt_oeval.h3.{u_1} : ∀ {x y : Nimber.{u_1}} {p : Polynomial.{u_1 + 1} Nimber.{u_1}},
      (∀ (k : ℕ), LT.lt.{u_1 + 1} ((AddMonoidAlgebra.coeff.{u_1 + 1, 0} p) k) x) →
        LT.lt.{u_1 + 1} y (Nimber.oeval.{u_1} x p) →
          ∃ (q : Polynomial.{u_1 + 1} Nimber.{u_1}),
            LT.lt.{u_1 + 1} q p ∧
              (∀ (k : ℕ), LT.lt.{u_1 + 1} ((AddMonoidAlgebra.coeff.{u_1 + 1, 0} q) k) x) ∧
                Eq.{u_1 + 2} (Nimber.oeval.{u_1} x q) y := by
  intro hc_x0 hc_x1 hc_x2 hc_x4 hc_x5
  exact Classical.byCases (fun hc_h => @Nimber.eq_oeval_of_lt_oeval hc_x0 hc_x1 hc_x2 hc_h hc_x4 hc_x5) (fun hc_hn => @HypCheckProof.Nimber.eq_oeval_of_lt_oeval.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4 hc_x5)

-- Surreal.birthday_ofSets_singleton_lt_of_birthday_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.birthday_ofSets_singleton_lt_of_birthday_eq.h3 : ¬∀ {o : NatOrdinal.{0}} {x y : Surreal.{0}},
        Eq.{2} (Surreal.birthday.{0} y) o → LT.lt.{1} x y → Eq.{2} (Surreal.birthday.{0} x) o := fun hc_h => absurd (@hc_h _ ((0 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0}) rfl (by
  simp)) (by
  simp)

-- Surreal.birthday_ofSets_singleton_lt_of_birthday_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.birthday_ofSets_singleton_lt_of_birthday_eq.h4 : ¬∀ {o : NatOrdinal.{0}} {x y : Surreal.{0}},
        Eq.{2} (Surreal.birthday.{0} x) o → LT.lt.{1} x y → Eq.{2} (Surreal.birthday.{0} y) o := fun hc_h => absurd (@hc_h _ ((0 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0}) rfl (by
  simp)) (by
  simp)

-- Surreal.birthday_ofSets_singleton_lt_of_birthday_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.birthday_ofSets_singleton_lt_of_birthday_eq.h5 : ¬∀ {o : NatOrdinal.{0}} {x y : Surreal.{0}},
        Eq.{2} (Surreal.birthday.{0} x) o → Eq.{2} (Surreal.birthday.{0} y) o → LT.lt.{1} x y := fun hc_h => absurd (@hc_h _ ((0 : Surreal) : Surreal.{0}) ((0 : Surreal) : Surreal.{0}) rfl (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- IGame.Numeric.mul_wpow_lt_wpow', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_wpow_lt_wpow'.h5 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] (r : Dyadic),
        LT.lt.{1} (HMul.hMul.{1, 1, 1} (↑r) (Wpow.wpow.{1} x)) (Wpow.wpow.{1} y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ ((1 : Dyadic) : Dyadic)) (by
  simp)

-- IGame.add_congr, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.add_congr.h2 : ¬∀ {a b c d : IGame.{0}}, c ≈ d → HAdd.hAdd.{1, 1, 1} a c ≈ HAdd.hAdd.{1, 1, 1} b d := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  rfl)) (by
  (game_cmp; done))

-- IGame.add_congr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.add_congr.h5 : ¬∀ {a b : IGame.{0}}, a ≈ b → ∀ {c d : IGame.{0}}, HAdd.hAdd.{1, 1, 1} a c ≈ HAdd.hAdd.{1, 1, 1} b d := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  rfl) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- Nimber.exists_root_of_lt_leastNoRoots, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.exists_root_of_lt_leastNoRoots.h3 : ¬∀ {x : Nimber.{0}} {p : Polynomial.{1} Nimber.{0}},
        Ne.{1} (Polynomial.degree.{1} p) 0 →
          LT.lt.{1} (↑p) (Nimber.leastNoRoots.{0} x) → ∃ (r : Nimber.{0}), LT.lt.{1} r x ∧ Polynomial.IsRoot.{1} p r := fun hc_h => absurd (@hc_h (0) (AddMonoidAlgebra.ofCoeff.{1, 0} 0) (by
  decide) (by
  aesop)) (by
  simp)

-- IGame.rightStop_congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.rightStop_congr.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Short.{0} x] [inst_1 : IGame.Short.{0} y],
        Eq.{1} (IGame.rightStop.{0} x) (IGame.rightStop.{0} y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _) (by
  simp)

-- IGame.Numeric.equiv_inv_of_mul_eq_one, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.equiv_inv_of_mul_eq_one.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y], x ≈ Inv.inv.{1} y := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _) (by
  (simp <;> game_cmp <;> done))

-- IGame.Small.le_numeric_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Small.le_numeric_of_pos.h1 : ¬∀ (x : IGame.{0}) {y : IGame.{0}} [inst : IGame.Numeric.{0} y], LT.lt.{1} 0 y → LE.le.{1} x y := fun hc_h => absurd (@hc_h ((2 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ (by
  simp)) (by
  (game_cmp; done))

-- IGame.Small.le_numeric_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Small.le_numeric_of_pos.h4 : ¬∀ (x : IGame.{0}) [self : IGame.Small.{0} x] {y : IGame.{0}} [inst : IGame.Numeric.{0} y], LE.le.{1} x y := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) _ ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.exists_between, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.exists_between.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y],
        ∃ (z : IGame.{0}), IGame.Numeric.{0} z ∧ LT.lt.{1} x z ∧ LT.lt.{1} z y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _) (by
  nofun)

-- Nimber.add_le_of_forall_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.add_le_of_forall_ne.h3 : ¬∀ {a b c : Nimber.{0}},
        (∀ (b' : Nimber.{0}), LT.lt.{1} b' b → Ne.{2} (HAdd.hAdd.{1, 1, 1} a b') c) → LE.le.{1} (HAdd.hAdd.{1, 1, 1} a b) c := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  simp)) (by
  simp)

-- Nimber.add_le_of_forall_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.add_le_of_forall_ne.h4 : ¬∀ {a b c : Nimber.{0}},
        (∀ (a' : Nimber.{0}), LT.lt.{1} a' a → Ne.{2} (HAdd.hAdd.{1, 1, 1} a' b) c) → LE.le.{1} (HAdd.hAdd.{1, 1, 1} a b) c := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  simp)) (by
  simp)

-- IGame.lf_of_right_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.lf_of_right_le.h4 : ¬∀ {x y z : IGame.{0}}, LE.le.{1} z y → ¬LE.le.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  rfl)) (by
  simp)

-- IGame.Impartial.equiv_iff_forall_fuzzy, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.equiv_iff_forall_fuzzy.h2 : ¬∀ {x y : IGame.{0}} [hy : IGame.Impartial.{0} y] (p : Player),
        x ≈ y ↔
          (∀ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} p x) z → z ‖ y) ∧
            ∀ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} (Neg.neg.{0} p) y) z → x ‖ z := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ (Player.right : Player)) (by
  (simp <;> game_cmp <;> done))

-- IGame.Impartial.equiv_iff_forall_fuzzy, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.equiv_iff_forall_fuzzy.h3 : ¬∀ {x y : IGame.{0}} [hx : IGame.Impartial.{0} x] (p : Player),
        x ≈ y ↔
          (∀ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} p x) z → z ‖ y) ∧
            ∀ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} (Neg.neg.{0} p) y) z → x ‖ z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ (Player.left : Player)) (by
  (simp <;> game_cmp <;> done))

-- IGame.natCast_mul_wpow_mem_moves_right_wpow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.natCast_mul_wpow_mem_moves_right_wpow.h4 : ¬∀ {x y : IGame.{0}} {n : ℕ},
        LT.lt.{0} 0 n →
          Membership.mem.{1, 1} (IGame.moves.{0} Player.right (Wpow.wpow.{1} x))
            (HMul.hMul.{1, 1, 1} (↑n) (Wpow.wpow.{1} y)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (1) (by
  decide)) (by
  simp)

-- IGame.Numeric.le_total, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.le_total.h2 : ¬∀ (x y : IGame.{0}) [inst : IGame.Numeric.{0} y], LE.le.{1} x y ∨ LE.le.{1} y x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.le_total, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.le_total.h3 : ¬∀ (x y : IGame.{0}) [inst : IGame.Numeric.{0} x], LE.le.{1} x y ∨ LE.le.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) _) (by
  (simp <;> omega))

-- IGame.Numeric.le_or_gt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.le_or_gt.h2 : ¬∀ (x y : IGame.{0}) [inst : IGame.Numeric.{0} y], LE.le.{1} x y ∨ LT.lt.{1} y x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.le_or_gt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.le_or_gt.h3 : ¬∀ (x y : IGame.{0}) [inst : IGame.Numeric.{0} x], LE.le.{1} x y ∨ LT.lt.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) _) (by
  (simp <;> omega))

-- IGame.Numeric.add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.add.h2 : ¬∀ (x y : IGame.{0}) [inst : IGame.Numeric.{0} y], IGame.Numeric.{0} (HAdd.hAdd.{1, 1, 1} x y) := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.add.h3 : ¬∀ (x y : IGame.{0}) [inst : IGame.Numeric.{0} x], IGame.Numeric.{0} (HAdd.hAdd.{1, 1, 1} x y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.lt_or_equiv_or_gt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.lt_or_equiv_or_gt.h2 : ¬∀ (x y : IGame.{0}) [inst : IGame.Numeric.{0} y], LT.lt.{1} x y ∨ x ≈ y ∨ LT.lt.{1} y x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.lt_or_equiv_or_gt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.lt_or_equiv_or_gt.h3 : ¬∀ (x y : IGame.{0}) [inst : IGame.Numeric.{0} x], LT.lt.{1} x y ∨ x ≈ y ∨ LT.lt.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul.h2 : ¬∀ (x y : IGame.{0}) [hy : IGame.Numeric.{0} y], IGame.Numeric.{0} (HMul.hMul.{1, 1, 1} x y) := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((1 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul.h3 : ¬∀ (x y : IGame.{0}) [hx : IGame.Numeric.{0} x], IGame.Numeric.{0} (HMul.hMul.{1, 1, 1} x y) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) _) (by
  simp)

-- IGame.le_of_forall_moves_right_lf, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.le_of_forall_moves_right_lf.h2 : ¬∀ {x y : IGame.{0}},
        (∀ (z : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) z →
              ∃ (w : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) w ∧ LE.le.{1} z w) →
          LE.le.{1} x y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) (by
  simp)) (by
  (simp <;> omega))

-- IGame.le_of_forall_moves_right_lf, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.le_of_forall_moves_right_lf.h3 : ¬∀ {x y : IGame.{0}},
        (∀ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) z → ¬LE.le.{1} z x) → LE.le.{1} x y := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  simp)

-- Surreal.Cut.rightSurreal_mem_of_sInf_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.rightSurreal_mem_of_sInf_eq.h3 : ¬∀ {s : Set.{1} Surreal.Cut.{0}} {x : Surreal.{0}} [inst : Small.{0, 1} ↑s],
        Membership.mem.{1, 1} s (Surreal.Cut.rightSurreal.{0} x) := fun hc_h => absurd (@hc_h (EmptyCollection.emptyCollection.{1}) ((0 : Surreal) : Surreal.{0}) _) (by
  decide +kernel)

-- IGame.lt_miny_toIGame_of_birthday_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.lt_miny_toIGame_of_birthday_le.h1 : ¬∀ {x : IGame.{0}} {o : NatOrdinal.{0}},
        LE.le.{1} (IGame.birthday.{0} x) o → LT.lt.{1} x (IGame.miny.{0} (NatOrdinal.toIGame.{0} o)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (0) (by
  simp)) (by
  (game_cmp; done))

-- Nimber.IsField.toSubfield_lt_toSubfield, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.toSubfield_lt_toSubfield.h2 : ¬∀ {x y : Nimber.{0}}, Nimber.IsField.{0} y → Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0) (Nimber.of 2 : Nimber.{0}) (by
  simp)) (by
  nofun)

-- Nimber.IsField.toSubfield_lt_toSubfield, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.toSubfield_lt_toSubfield.h3 : ¬∀ {x y : Nimber.{0}}, Nimber.IsField.{0} x → Nimber.IsField.{0} y := fun hc_h => absurd (@hc_h (Nimber.of 2 : Nimber.{0}) (0) (by
  simp)) (by
  nofun)

-- SignExpansion.succ_apply_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignExpansion.succ_apply_of_lt.h3 : ¬∀ {x : SignExpansion.{0}} [inst : SignExpansion.Small.{0} x] {o : NatOrdinal.{0}},
        Eq.{1} ((SignExpansion.succ.{0} x) o) (x o) := fun hc_h => absurd (@hc_h (0) (@SignExpansion.Small.mk (@OfNat.ofNat SignExpansion (nat_lit 0) (@Zero.toOfNat0 SignExpansion SignExpansion.instZero)) (by (try dsimp only);   (intros; simp_all; done))) (1)) (by
  simp)

-- le_comm_of_neg_equiv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.le_comm_of_neg_equiv.h2 : ¬∀ {x y : IGame.{0}}, Neg.neg.{1} y ≈ y → (LE.le.{1} x y ↔ LE.le.{1} y x) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  simp)

-- le_comm_of_neg_equiv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.le_comm_of_neg_equiv.h3 : ¬∀ {x y : IGame.{0}}, Neg.neg.{1} x ≈ x → (LE.le.{1} x y ↔ LE.le.{1} y x) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  simp)) (by
  simp)

-- Nimber.coeff_X_pow_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.coeff_X_pow_lt.h2 : ¬∀ {x : Nimber.{0}} (n k : ℕ), LT.lt.{1} ((AddMonoidAlgebra.coeff.{1, 0} (HPow.hPow.{1, 0, 1} Polynomial.X.{1} n)) k) x := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- Surreal.Cut.exists_birthday_lt_of_mem_Ioo, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.exists_birthday_lt_of_mem_Ioo.h3 : ¬∀ {x y z : Surreal.Cut.{0}},
        ∃ (a : Surreal.{0}), LT.lt.{1} (↑(Surreal.birthday.{0} a)) (Surreal.Cut.birthday.{0} y) ∧ Surreal.Cut.Fits.{0} a x z := fun hc_h => absurd (@hc_h (Bot.bot.{1}) (Bot.bot.{1}) (Bot.bot.{1})) (by
  simp)

-- IGame.leftStop_of_small, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.leftStop_of_small.h1 : ¬∀ (x : IGame.{0}) [inst : IGame.Short.{0} x], Eq.{1} (IGame.leftStop.{0} x) 0 := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.mk_of_lf, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mk_of_lf.h1 : ¬∀ {x : IGame.{0}},
        (∀ (p : Player) (y : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} p x) y → IGame.Numeric.{0} y) →
          IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) (by
  simp)) (by
  simp)

-- IGame.grundyAux_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.grundyAux_ne.h3 : ¬∀ {p : Player} {x y : IGame.{0}}, Ne.{2} (IGame.grundyAux.{0} p y) (IGame.grundyAux.{0} p x) := fun hc_h => absurd (@hc_h (Player.left : Player) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.Dicotic.moves_eq_empty_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Dicotic.moves_eq_empty_iff.h1 : ¬∀ {x : IGame.{0}} (p q : Player),
        Eq.{2} (IGame.moves.{0} p x) EmptyCollection.emptyCollection.{1} ↔
          Eq.{2} (IGame.moves.{0} q x) EmptyCollection.emptyCollection.{1} := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) (Player.left : Player) (Player.right : Player)) (by
  simp)

-- Game.ratCast_toDyadic, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Game.ratCast_toDyadic.h2 : ¬∀ (x : IGame.{0}) [inst : IGame.Short.{0} x], IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) _) (by
  simp)

-- Nimber.lt_add_cases, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.lt_add_cases.h3 : ¬∀ {a b c : Nimber.{0}}, LT.lt.{1} (HAdd.hAdd.{1, 1, 1} a c) b ∨ LT.lt.{1} (HAdd.hAdd.{1, 1, 1} a b) c := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- Nimber.exists_of_lt_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.exists_of_lt_add.h3 : ¬∀ {a b c : Nimber.{0}},
        (∃ (a' : Nimber.{0}), LT.lt.{1} a' a ∧ Eq.{2} (HAdd.hAdd.{1, 1, 1} a' b) c) ∨
          ∃ (b' : Nimber.{0}), LT.lt.{1} b' b ∧ Eq.{2} (HAdd.hAdd.{1, 1, 1} a b') c := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- Nimber.mul_le_of_forall_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.mul_le_of_forall_ne.h3 : ¬∀ {a b c : Nimber.{0}}, LE.le.{1} (HMul.hMul.{1, 1, 1} a b) c := fun hc_h => absurd (@hc_h (1) (1) (0)) (by
  simp)

-- IGame.ordinalSum_lt_iff_of_forall_wsubposition, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.ordinalSum_lt_iff_of_forall_wsubposition.h3 : ¬∀ {x y z : IGame.{0}}, LT.lt.{1} (IGame.ordinalSum.{0} x y) z ↔ LT.lt.{1} x z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  simp)

-- IGame.ordinalSum_right_congr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.ordinalSum_right_congr.h3 : ¬∀ (x : IGame.{0}) {y z : IGame.{0}}, IGame.ordinalSum.{0} x y ≈ IGame.ordinalSum.{0} x z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- IGame.ordinalSum_lt_ordinalSum_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.ordinalSum_lt_ordinalSum_right.h3 : ¬∀ (x : IGame.{0}) {y z : IGame.{0}}, LT.lt.{1} (IGame.ordinalSum.{0} x y) (IGame.ordinalSum.{0} x z) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- Polynomial.self_sub_X_pow_of_monic, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Polynomial.self_sub_X_pow_of_monic.h3 : ¬∀ {R : Type} [inst : Ring R] {p : Polynomial R}, p - Polynomial.X ^ p.natDegree = p.eraseLead := fun hc_h => absurd (@hc_h (ℤ) (Int.instRing) (AddMonoidAlgebra.ofCoeff 0)) (by
  simp)

-- IGame.equiv_one_of_fits, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.equiv_one_of_fits.h1 : ¬∀ {x : IGame.{0}}, ¬x ≈ 0 → x ≈ 1 := fun hc_h => absurd (@hc_h ((2 : IGame) : IGame.{0}) (by
  (game_cmp; done))) (by
  (game_cmp; done))

-- Nimber.IsRing.inv_lt_self_of_not_isField, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.inv_lt_self_of_not_isField.h1 : ¬∀ {x : Nimber.{0}}, ¬Nimber.IsField.{0} x → LT.lt.{1} (Inv.inv.{1} x) x := fun hc_h => absurd (@hc_h (0) (by
  aesop)) (by
  simp)

-- Nimber.mem_toSubring_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.mem_toSubring_iff.h2 : ¬∀ {x : Nimber.{0}} {y : Nimber.{0}}, Nimber.IsRing.{0} x := fun hc_h => absurd (@hc_h (0) (0)) (by
  nofun)

-- IGame.birthday_lt_of_subposition, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.birthday_lt_of_subposition.h2 : ¬∀ {x y : IGame.{0}}, LT.lt.{1} (IGame.birthday.{0} y) (IGame.birthday.{0} x) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- Dyadic.den_mkRat_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.den_mkRat_le.h2 : ¬∀ (x : ℤ) {n : ℕ}, (mkRat x n).den ≤ n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Dyadic.den_ne_one_of_den_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.den_ne_one_of_den_lt.h2 : ¬∀ {x : Dyadic} {y : Dyadic}, y.den ≠ 1 := fun hc_h => absurd (@hc_h (Dyadic.zero) (Dyadic.zero)) (by
  decide +kernel)

-- IGame.Subposition.not_wsubposition, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Subposition.not_wsubposition.h2 : ¬∀ {x y : IGame.{0}}, ¬IGame.WSubposition.{0} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.left_lf, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.left_lf.h2 : ¬∀ {x y : IGame.{0}}, ¬LE.le.{1} x y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.not_wsubposition_of_subposition, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.not_wsubposition_of_subposition.h2 : ¬∀ {x y : IGame.{0}}, ¬IGame.WSubposition.{0} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- Polynomial.exists_gt_of_forall_coeff_gt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Polynomial.exists_gt_of_forall_coeff_gt.h2 : ¬∀ {s : Set.{1} Nimber.{0}} {p : Polynomial.{1} Nimber.{0}},
        ∃ (a : Nimber.{0}), Membership.mem.{1, 1} s a ∧ ∀ (k : ℕ), LT.lt.{1} ((AddMonoidAlgebra.coeff.{1, 0} p) k) a := fun hc_h => absurd (@hc_h (EmptyCollection.emptyCollection.{1}) (AddMonoidAlgebra.ofCoeff.{1, 0} 0)) (by
  simp)

-- IGame.ext, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.ext.h2 : ¬∀ {x y : IGame.{0}}, Eq.{2} x y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  simp)

-- Dyadic.eq_lower_of_mem_moves_left_toIGame, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.eq_lower_of_mem_moves_left_toIGame.h2 : ¬∀ {x : Dyadic} {y : IGame.{0}}, Eq.{2} y ↑x.lower := fun hc_h => absurd (@hc_h (Dyadic.zero) ((0 : IGame) : IGame.{0})) (by
  (simp <;> decide))

-- Nimber.oeval_eq_zero_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.oeval_eq_zero_iff.h2 : ¬∀ {x : Nimber.{0}} {p : Polynomial.{1} Nimber.{0}}, Eq.{2} (Nimber.oeval.{0} x p) 0 ↔ Eq.{2} p 0 := fun hc_h => absurd (@hc_h (0) ((Polynomial.X : Polynomial Nimber) : Polynomial.{1} Nimber.{0})) (by
  simp)

-- Nimber.Lex.lt_of_degree_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.Lex.lt_of_degree_lt.h2 : ¬∀ {p q : Polynomial.{1} Nimber.{0}}, LT.lt.{1} p q := fun hc_h => absurd (@hc_h (AddMonoidAlgebra.ofCoeff.{1, 0} 0) (AddMonoidAlgebra.ofCoeff.{1, 0} 0)) (by
  decide +kernel)

-- Nimber.IsField.lt_algClosure_iff_isAlgebraic, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.lt_algClosure_iff_isAlgebraic.h2 : ¬∀ {x : Nimber.{0}} {y : Nimber.{0}}, Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0) (0)) (by
  nofun)

-- IGame.AntisymmRel.Fits, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.AntisymmRel.Fits.h2 : ¬∀ {x y : IGame.{0}}, IGame.Fits.{0} x y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  (simp <;> game_cmp <;> done))

-- IGame.Numeric.nsmul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.nsmul.h2 : ¬∀ (n : ℕ) (x : IGame.{0}), IGame.Numeric.{0} (HSMul.hSMul.{0, 1, 1} n x) := fun hc_h => absurd (@hc_h (1) (IGame.star : IGame.{0})) (by
  simp)

-- Surreal.mk_zsmul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.mk_zsmul.h2 : ¬∀ (n : ℤ) (x : IGame.{0}), IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (0) (IGame.star : IGame.{0})) (by
  simp)

-- Surreal.mk_nsmul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.mk_nsmul.h2 : ¬∀ (n : ℕ) (x : IGame.{0}), IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (0) (IGame.star : IGame.{0})) (by
  simp)

-- Nimber.IsRing.toIsGroup, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.toIsGroup.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsGroup.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- IGame.zero_mem_moves_left_inv, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.zero_mem_moves_left_inv.h1 : ¬∀ {x : IGame.{0}}, Membership.mem.{1, 1} (IGame.moves.{0} Player.left (Inv.inv.{1} x)) 0 := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0})) (by
  simp)

-- Nimber.IsField.perfectField_iff_leastNoRoots, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.perfectField_iff_leastNoRoots.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- Dyadic.birthday_of_den_eq_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.birthday_of_den_eq_one.h1 : ¬∀ {x : Dyadic}, x.birthday = x.num.natAbs := fun hc_h => absurd (@hc_h (Dyadic.half : Dyadic)) (by
  decide +kernel)

-- Nimber.card_ringClosure, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.card_ringClosure.h1 : ¬∀ {x : Nimber.{0}},
        Eq.{2} (Ordinal.card.{0} (Nimber.val.{0} (Nimber.ringClosure.{0} x))) (Ordinal.card.{0} (Nimber.val.{0} x)) := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Nimber.IsField.not_perfectField_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.not_perfectField_iff.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- Nimber.IsAlgClosed.perfectField_fieldClosure_succ_pow_omega0, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsAlgClosed.perfectField_fieldClosure_succ_pow_omega0.h1 : ¬∀ {t : Nimber.{0}}, Nimber.IsAlgClosed.{0} t := fun hc_h => absurd (@hc_h (1)) (by
  nofun)

-- Nimber.IsGroup.pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.pos.h1 : ¬∀ {x : Nimber.{0}}, LT.lt.{1} 0 x := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Game.birthday_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Game.birthday_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- IGame.moves_right_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.moves_right_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- IGame.Impartial.mk_add_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.mk_add_self.h1 : ¬∀ (x : IGame.{0}), Eq.{2} (HAdd.hAdd.{1, 1, 1} (Game.mk.{0} x) (Game.mk.{0} x)) 0 := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0})) (by
  norm_num)

-- Nimber.coe_toAddSubgroup, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.coe_toAddSubgroup.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsGroup.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- IGame.lt_miny_toIGame_birthday, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.lt_miny_toIGame_birthday.h1 : ¬∀ {x : IGame.{0}}, LT.lt.{1} x (IGame.miny.{0} (NatOrdinal.toIGame.{0} (IGame.birthday.{0} x))) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- IGame.inv_nonneg, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.inv_nonneg.h1 : ¬∀ {x : IGame.{0}}, ¬LE.le.{1} (Inv.inv.{1} x) 0 := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0})) (by
  simp)

-- Nimber.IsRing.one_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.one_lt.h1 : ¬∀ {x : Nimber.{0}}, LT.lt.{1} 1 x := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Nimber.exists_isGroup_add_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.exists_isGroup_add_lt.h1 : ¬∀ {x : Nimber.{0}}, ∃ (y : Nimber.{0}), LE.le.{1} y x ∧ Nimber.IsGroup.{0} y ∧ LT.lt.{1} (HAdd.hAdd.{1, 1, 1} x y) y := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- IGame.toDyadic_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.toDyadic_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Surreal.mk_neg, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.mk_neg.h1 : ¬∀ (x : IGame.{0}), IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0})) (by
  simp)

-- Nimber.coeff_leastNoRoots_zero_ne, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.coeff_leastNoRoots_zero_ne.h1 : ¬∀ {x : Nimber.{0}}, Ne.{2} (Nimber.leastNoRoots.{0} x) Top.top.{1} := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- IGame.switch_equiv_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.switch_equiv_zero.h1 : ¬∀ {x : IGame.{0}}, IGame.switch.{0} x ≈ 0 := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0})) (by
  (simp <;> omega))

-- Surreal.toGame_mk, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.toGame_mk.h1 : ¬∀ (x : IGame.{0}), IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0})) (by
  simp)

-- Surreal.IsOmnific.one_le_iff_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.IsOmnific.one_le_iff_pos.h1 : ¬∀ {x : Surreal.{0}}, LE.le.{1} 1 x ↔ LT.lt.{1} 0 x := fun hc_h => absurd (@hc_h (((1/2 : ℚ) : Surreal) : Surreal.{0})) (by
  norm_num)

