module
public import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow', hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_wpow_add_mul_wpow_lt_mul_wpow'.h9 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z]
        (r s : Dyadic) {t : Dyadic},
        LT.lt.{1} x z →
          LT.lt.{1} y z →
            LT.lt.{1}
              (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} (↑r) (Wpow.wpow.{1} x))
                (HMul.hMul.{1, 1, 1} (↑s) (Wpow.wpow.{1} y)))
              (HMul.hMul.{1, 1, 1} (↑t) (Wpow.wpow.{1} z)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _ (Dyadic.zero) (Dyadic.zero) (Dyadic.zero) (by
  simp) (by
  simp)) (by
  simp)

-- IGame.Numeric.mul_lt_mul, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_lt_mul.h8 : ¬∀ {a b c d : IGame.{0}} [inst : IGame.Numeric.{0} a] [inst : IGame.Numeric.{0} b] [inst : IGame.Numeric.{0} c]
        [inst : IGame.Numeric.{0} d],
        LE.le.{1} c d → LT.lt.{1} 0 c → LE.le.{1} 0 b → LT.lt.{1} (HMul.hMul.{1, 1, 1} a c) (HMul.hMul.{1, 1, 1} b d) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _ _ (by
  rfl) (by
  simp) (by
  rfl)) (by
  simp)

-- IGame.Numeric.mul_lt_mul, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_lt_mul.h9 : ¬∀ {a b c d : IGame.{0}} [inst : IGame.Numeric.{0} a] [inst : IGame.Numeric.{0} b] [inst : IGame.Numeric.{0} c]
        [inst : IGame.Numeric.{0} d],
        LT.lt.{1} a b → LT.lt.{1} 0 c → LE.le.{1} 0 b → LT.lt.{1} (HMul.hMul.{1, 1, 1} a c) (HMul.hMul.{1, 1, 1} b d) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ _ _ (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- IGame.Numeric.mul_lt_mul, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_lt_mul.h10 : ¬∀ {a b c d : IGame.{0}} [inst : IGame.Numeric.{0} a] [inst : IGame.Numeric.{0} b] [inst : IGame.Numeric.{0} c]
        [inst : IGame.Numeric.{0} d],
        LT.lt.{1} a b → LE.le.{1} c d → LE.le.{1} 0 b → LT.lt.{1} (HMul.hMul.{1, 1, 1} a c) (HMul.hMul.{1, 1, 1} b d) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ _ _ (by
  simp) (by
  rfl) (by
  simp)) (by
  simp)

-- IGame.Numeric.mulOption_congr₂, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mulOption_congr₂.h10 : ¬∀ {x y₁ y₂ a b : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y₁] [inst : IGame.Numeric.{0} y₂]
        [inst : IGame.Numeric.{0} a] [inst : IGame.Numeric.{0} b],
        IGame.mulOption.{0} x y₁ a b ≈ IGame.mulOption.{0} x y₂ a b := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ _ _ _) (by
  (game_cmp; done))

-- Surreal.ofSets_eq_of_forall_birthday_le, hypothesis 5: removable
/- FAILED: 2:0: unused universe parameter 'u' | 20:17: unsolved goals
s t : Set Surreal
z : Surreal
inst : Small.{u, u + 1} ↑s
inst_1 : Small.{u, u + 1} ↑t
hL : ∀ x ∈ s, x < z
hR : ∀ y ∈ t, z < y
h : ∀ (w : Surreal), (∀ x ∈ s, x < w) → (∀ y ∈ t, w < y) → z.birthday ≤ w.birthday
x y : Surreal
a : x ∈ s
a_1 : y ∈ t
⊢ x < y | 2:0: unused universe parameter 'u' | 86:30: unsolved goals
s t : Set Surreal
z : Surreal
inst : Small.{u, u + 1} ↑s
inst_1 : Small.{u, u + 1} ↑t
hL : ∀ x ∈ s, x < z
hR : ∀ y ∈ t, z < y
h : ∀ (w : Surreal), (∀ x ∈ s, x < w) → (∀ y ∈ t, w < y) → z.birthday ≤ w.birthday
x y : Surreal
a : x ∈ s
a_1 : y ∈ t
⊢ x < y | 2:0: unused universe parameter 'u' | 2:0: unused universe parameter 'u' | 2:0: unused universe parameter 'u'
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Surreal.ofSets_eq_of_forall_birthday_le.h5.der.{u} : ∀ {s t : Set Surreal} {z : Surreal} [inst : Small ↑s] [inst : Small ↑t],
      (∀ x ∈ s, x < z) →
        (∀ y ∈ t, z < y) →
          (∀ (w : Surreal), (∀ x ∈ s, x < w) → (∀ y ∈ t, w < y) → z.birthday ≤ w.birthday) → ∀ x ∈ s, ∀ y ∈ t, x < y := by
  (intros; grind)
theorem HypCheckProof.Surreal.ofSets_eq_of_forall_birthday_le.h5.{u} : ∀ {s t : Set Surreal} {z : Surreal} [inst : Small ↑s] [inst_1 : Small ↑t] (hL : ∀ x ∈ s, x < z) (hR : ∀ y ∈ t, z < y)
      (h : ∀ (w : Surreal), (∀ x ∈ s, x < w) → (∀ y ∈ t, w < y) → z.birthday ≤ w.birthday), !{s | t} = z := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7
  exact @Surreal.ofSets_eq_of_forall_birthday_le hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Surreal.ofSets_eq_of_forall_birthday_le.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7) hc_x5 hc_x6 hc_x7
-/

-- Surreal.birthday_ofSets_lt_of_btwn', hypothesis 4: removable
/- FAILED: 2:0: unused universe parameter 'u' | 14:17: unsolved goals
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
⊢ x < y | 2:0: unused universe parameter 'u' | 49:30: unsolved goals
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
theorem HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn'.h4.der.{u} : ∀ {st : Player → Set Surreal} {z : Surreal} [inst : Small ↑(st Player.left)] [inst : Small ↑(st Player.right)],
      (∀ x ∈ st Player.left, x < z) → (∀ y ∈ st Player.right, z < y) → ∀ x ∈ st Player.left, ∀ y ∈ st Player.right, x < y := by
  (intros; grind)
theorem HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn'.h4.{u} : ∀ {st : Player → Set Surreal} {z : Surreal} [inst : Small ↑(st Player.left)] [inst_1 : Small ↑(st Player.right)]
      (hL : ∀ x ∈ st Player.left, x < z) (hR : ∀ y ∈ st Player.right, z < y), !{st} ≠ z → !{st}.birthday < z.birthday := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Surreal.birthday_ofSets_lt_of_btwn' hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn'.h4.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x4 hc_x5 hc_x6
-/

-- Surreal.birthday_ofSets_lt_of_btwn', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.birthday_ofSets_lt_of_btwn'.h7 : ¬∀ {st : Player → Set.{1} Surreal.{0}} {z : Surreal.{0}} [inst : Small.{0, 1} ↑(st Player.left)]
        [inst_1 : Small.{0, 1} ↑(st Player.right)]
        {H :
          ∀ (x : Surreal.{0}),
            Membership.mem.{1, 1} (st Player.left) x →
              ∀ (y : Surreal.{0}), Membership.mem.{1, 1} (st Player.right) y → LT.lt.{1} x y},
        (∀ (x : Surreal.{0}), Membership.mem.{1, 1} (st Player.left) x → LT.lt.{1} x z) →
          (∀ (y : Surreal.{0}), Membership.mem.{1, 1} (st Player.right) y → LT.lt.{1} z y) →
            LT.lt.{1} (Surreal.birthday.{0} !{st}) (Surreal.birthday.{0} z) := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (fun (a : Player) => EmptyCollection.emptyCollection.{1}) ((0 : Surreal) : Surreal.{0}) _ _ hc_k0 hc_k1 hc_k2) (by
  simp)

-- IGame.Numeric.lt_div_iff_of_neg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.lt_div_iff_of_neg.h6 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        LT.lt.{1} x (HDiv.hDiv.{1, 1, 1} y z) ↔ LT.lt.{1} y (HMul.hMul.{1, 1, 1} x z) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _) (by
  simp)

-- IGame.Numeric.mul_lt_mul_right_of_neg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_lt_mul_right_of_neg.h6 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        LT.lt.{1} (HMul.hMul.{1, 1, 1} x z) (HMul.hMul.{1, 1, 1} y z) ↔ LT.lt.{1} y x := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ _) (by
  simp)

-- IGame.Small.numeric_lt_of_neg_of_forall_of_nonempty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Small.numeric_lt_of_neg_of_forall_of_nonempty.h2 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} y],
        (∀ (p : Player) (y : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} p x) y → IGame.Small.{0} y) →
          Set.Nonempty.{1} (IGame.moves.{0} Player.left x) → LT.lt.{1} y x := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ (by
  simp) (by
  simp)) (by
  simp)

-- IGame.Impartial.fuzzy_zero_of_forall_exists, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.fuzzy_zero_of_forall_exists.h1 : ¬∀ {x : IGame.{0}} {p : Player} {y : IGame.{0}},
        Membership.mem.{1, 1} (IGame.moves.{0} p x) y →
          (∀ (z : IGame.{0}),
              Membership.mem.{1, 1} (IGame.moves.{0} p y) z →
                ∃ (w : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} p x) w ∧ z ≈ w) →
            x ‖ 0 := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) (Player.left : Player) ((0 : IGame) : IGame.{0}) (by
  simp) (by
  aesop)) (by
  (game_cmp; done))

-- IGame.Impartial.fuzzy_zero_of_forall_exists, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.fuzzy_zero_of_forall_exists.h4 : ¬∀ {x : IGame.{0}} [hx : IGame.Impartial.{0} x] {p : Player} {y : IGame.{0}},
        (∀ (z : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} p y) z →
              ∃ (w : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} p x) w ∧ z ≈ w) →
          x ‖ 0 := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _ (Player.left : Player) ((0 : IGame) : IGame.{0}) (by
  aesop)) (by
  simp)

-- IGame.Numeric.mul_neg_of_neg_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_neg_of_neg_of_pos.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y],
        LT.lt.{1} 0 y → LT.lt.{1} (HMul.hMul.{1, 1, 1} x y) 0 := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ (by
  simp)) (by
  simp)

-- IGame.Numeric.mul_neg_of_neg_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_neg_of_neg_of_pos.h5 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y],
        LT.lt.{1} x 0 → LT.lt.{1} (HMul.hMul.{1, 1, 1} x y) 0 := fun hc_h => absurd (@hc_h ((-1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ (by
  simp)) (by
  simp)

-- Surreal.trunc_eq_of_birthday_le_of_forall_le_ge_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.trunc_eq_of_birthday_le_of_forall_le_ge_iff.h3 : ¬∀ {x y : Surreal.{0}} {o : NatOrdinal.{0}},
        (∀ (z : Surreal.{0}), LT.lt.{1} (Surreal.birthday.{0} z) o → (LE.le.{1} y z ↔ LE.le.{1} x z)) →
          (∀ (z : Surreal.{0}), LT.lt.{1} (Surreal.birthday.{0} z) o → (LE.le.{1} z y ↔ LE.le.{1} z x)) →
            Eq.{2} ((Surreal.trunc.{0} o) x) y := fun hc_h => absurd (@hc_h ((1 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0}) (0) (by
  simp) (by
  simp)) (by
  simp)

-- IGame.sub_congr, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.sub_congr.h2 : ¬∀ {a b c d : IGame.{0}}, c ≈ d → HSub.hSub.{1, 1, 1} a c ≈ HSub.hSub.{1, 1, 1} b d := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  rfl)) (by
  (game_cmp; done))

-- IGame.sub_congr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.sub_congr.h5 : ¬∀ {a b : IGame.{0}}, a ≈ b → ∀ {c d : IGame.{0}}, HSub.hSub.{1, 1, 1} a c ≈ HSub.hSub.{1, 1, 1} b d := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  rfl) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- Polynomial.degree_pos_of_mem_roots, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Polynomial.degree_pos_of_mem_roots.h2 : ¬∀ {R : Type} [inst : CommRing R] {p : Polynomial R} {r : R}, IsDomain R := fun hc_h => absurd (@hc_h (Unit) (PUnit.commRing) (AddMonoidAlgebra.ofCoeff 0) (PUnit.unit)) (by
  exact fun hc_c =>
    absurd (hc_c.toNontrivial.exists_pair_ne)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Polynomial.degree_pos_of_mem_roots, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Polynomial.degree_pos_of_mem_roots.h5 : ¬∀ {R : Type} [inst : CommRing R] [inst_1 : IsDomain R] {p : Polynomial R} {r : R}, 0 < p.degree := fun hc_h => absurd (@hc_h (ℤ) (Int.instCommRing) _ (AddMonoidAlgebra.ofCoeff 0) (0)) (by
  decide +kernel)

-- NatOrdinal.mul_add_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.mul_add_le.h4 : ¬∀ {a b a' b' : NatOrdinal.{0}},
        LE.le.{1} b' b →
          LE.le.{1} (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b) (HMul.hMul.{1, 1, 1} a b'))
            (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b) (HMul.hMul.{1, 1, 1} a' b')) := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (by
  simp)) (by
  simp)

-- NatOrdinal.mul_add_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.mul_add_le.h5 : ¬∀ {a b a' b' : NatOrdinal.{0}},
        LE.le.{1} a' a →
          LE.le.{1} (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b) (HMul.hMul.{1, 1, 1} a b'))
            (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b) (HMul.hMul.{1, 1, 1} a' b')) := fun hc_h => absurd (@hc_h (1) (0) (0) (1) (by
  simp)) (by
  simp)

-- IGame.leftStop_congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.leftStop_congr.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Short.{0} x] [inst_1 : IGame.Short.{0} y],
        Eq.{1} (IGame.leftStop.{0} x) (IGame.leftStop.{0} y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _) (by
  simp)

-- IGame.lf_of_rightStop_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.lf_of_rightStop_lt.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Short.{0} x] [inst : IGame.Numeric.{0} y], ¬LE.le.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _) (by
  simp)

-- IGame.Small.lt_numeric_of_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Small.lt_numeric_of_pos.h2 : ¬∀ (x : IGame.{0}) {y : IGame.{0}} [inst : IGame.Numeric.{0} y], LT.lt.{1} 0 y → LT.lt.{1} x y := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ (by
  simp)) (by
  simp)

-- IGame.Small.lt_numeric_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Small.lt_numeric_of_pos.h4 : ¬∀ (x : IGame.{0}) {y : IGame.{0}} [inst : IGame.Small.{0} x] [inst : IGame.Numeric.{0} y], LT.lt.{1} x y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _) (by
  simp)

-- IGame.Fits.equiv_of_forall_birthday_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Fits.equiv_of_forall_birthday_le.h3 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x],
        (∀ (z : IGame.{0}),
            IGame.Numeric.{0} z → IGame.Fits.{0} z y → LE.le.{1} (IGame.birthday.{0} x) (IGame.birthday.{0} z)) →
          x ≈ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ (by
  simp)) (by
  (game_cmp; done))

-- Nimber.IsField.exists_root_subfield, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.exists_root_subfield.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- IGame.Fits.equiv_of_forall_not_fits, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Fits.equiv_of_forall_not_fits.h3 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x],
        (∀ (p : Player) (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} p x) z → ¬IGame.Fits.{0} z y) → x ≈ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ (by
  simp)) (by
  (game_cmp; done))

-- Nimber.add_lt_of_log_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.add_lt_of_log_eq.h2 : ¬∀ {a b : Ordinal.{0}},
        Ne.{2} b 0 →
          Eq.{2} (Ordinal.log.{0} 2 a) (Ordinal.log.{0} 2 b) →
            LT.lt.{1} (HAdd.hAdd.{1, 1, 1} (Nimber.of.{0} a) (Nimber.of.{0} b))
              (Nimber.of.{0} (HPow.hPow.{1, 1, 1} 2 (Ordinal.log.{0} 2 a))) := fun hc_h => absurd (@hc_h ((0 : Ordinal) : Ordinal.{0}) ((1 : Ordinal) : Ordinal.{0}) (by
  simp) (by
  simp)) (by
  simp)

-- Nimber.add_lt_of_log_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.add_lt_of_log_eq.h3 : ¬∀ {a b : Ordinal.{0}},
        Ne.{2} a 0 →
          Eq.{2} (Ordinal.log.{0} 2 a) (Ordinal.log.{0} 2 b) →
            LT.lt.{1} (HAdd.hAdd.{1, 1, 1} (Nimber.of.{0} a) (Nimber.of.{0} b))
              (Nimber.of.{0} (HPow.hPow.{1, 1, 1} 2 (Ordinal.log.{0} 2 a))) := fun hc_h => absurd (@hc_h ((1 : Ordinal) : Ordinal.{0}) ((0 : Ordinal) : Ordinal.{0}) (by
  simp) (by
  simp)) (by
  simp)

-- Surreal.round_mk_of_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.round_mk_of_pos.h2 : ¬∀ {x r : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} r], LT.lt.{1} 0 r := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _) (by
  simp)

-- Surreal.round_mk_of_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.round_mk_of_pos.h3 : ¬∀ {x r : IGame.{0}}, LT.lt.{1} 0 r → ∀ [inst : IGame.Numeric.{0} r], IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  simp) (by
  simp)) (by
  simp)

-- IGame.mul_wpow_mem_moves_right_wpow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.mul_wpow_mem_moves_right_wpow.h4 : ¬∀ {x y : IGame.{0}} {r : Dyadic},
        LT.lt.{0} 0 r →
          Membership.mem.{1, 1} (IGame.moves.{0} Player.right (Wpow.wpow.{1} x))
            (HMul.hMul.{1, 1, 1} (↑r) (Wpow.wpow.{1} y)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : Dyadic) : Dyadic) (by
  decide)) (by
  simp)

-- IGame.lf_right_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.lf_right_of_le.h4 : ¬∀ {x y z : IGame.{0}}, LE.le.{1} x y → ¬LE.le.{1} z x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  rfl)) (by
  simp)

-- IGame.lf_of_le_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.lf_of_le_left.h3 : ¬∀ {x y z : IGame.{0}}, Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) z → ¬LE.le.{1} y x := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  simp)

-- IGame.lf_of_le_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.lf_of_le_left.h4 : ¬∀ {x y z : IGame.{0}}, LE.le.{1} x z → ¬LE.le.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  rfl)) (by
  simp)

-- IGame.Impartial.grundy_moves_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.grundy_moves_ne.h4 : ¬∀ {p : Player} {x y : IGame.{0}} [inst : IGame.Impartial.{0} x], Membership.mem.{1, 1} (IGame.moves.{0} p x) y := fun hc_h => absurd (@hc_h (Player.left : Player) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- equiv_or_fuzzy_of_neg_equiv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.equiv_or_fuzzy_of_neg_equiv.h2 : ¬∀ {x y : IGame.{0}}, Neg.neg.{1} y ≈ y → x ≈ y ∨ x ‖ y := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  (simp <;> game_cmp <;> done))

-- equiv_or_fuzzy_of_neg_equiv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.equiv_or_fuzzy_of_neg_equiv.h3 : ¬∀ {x y : IGame.{0}}, Neg.neg.{1} x ≈ x → x ≈ y ∨ x ‖ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  simp)) (by
  (simp <;> game_cmp <;> done))

-- IGame.Numeric.le_iff_forall_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.le_iff_forall_lt.h3 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x],
        LE.le.{1} x y ↔
          (∀ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) z → LT.lt.{1} z y) ∧
            ∀ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) z → LT.lt.{1} x z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.up : IGame.{0}) _) (by
  (simp <;> game_cmp <;> done))

-- lf_iff_fuzzy_of_neg_equiv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.lf_iff_fuzzy_of_neg_equiv.h3 : ¬∀ {x y : IGame.{0}}, Neg.neg.{1} x ≈ x → (¬LE.le.{1} y x ↔ x ‖ y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  simp)) (by
  (simp <;> game_cmp <;> done))

-- IGame.tiny_lt_of_toIGame_birthday_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.tiny_lt_of_toIGame_birthday_le.h1 : ¬∀ {x o : IGame.{0}}, LE.le.{1} (NatOrdinal.toIGame.{0} (IGame.birthday.{0} x)) o → LT.lt.{1} (IGame.tiny.{0} o) x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  (game_cmp; done))

-- Dyadic.den_mkRat_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.den_mkRat_lt.h2 : ¬∀ {x : Dyadic} {n : ℤ}, x.den ≠ 1 → (mkRat n x.den).den < x.den := fun hc_h => absurd (@hc_h (Dyadic.half : Dyadic) (1) (by
  decide)) (by
  decide +kernel)

-- Dyadic.den_mkRat_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.den_mkRat_lt.h3 : ¬∀ {x : Dyadic} {n : ℤ}, 2 ∣ n → (mkRat n x.den).den < x.den := fun hc_h => absurd (@hc_h (Dyadic.zero) (0) (by
  decide)) (by
  decide +kernel)

-- IGame.Small.lt_surreal_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Small.lt_surreal_of_pos.h1 : ¬∀ (x : IGame.{0}) {y : Surreal.{0}}, LT.lt.{1} 0 y → LT.lt.{1} (Game.mk.{0} x) (Surreal.toGame.{0} y) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((1 : Surreal) : Surreal.{0}) (by
  simp)) (by
  simp)

-- IGame.Small.lt_surreal_of_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Small.lt_surreal_of_pos.h3 : ¬∀ (x : IGame.{0}) [inst : IGame.Small.{0} x] {y : Surreal.{0}}, LT.lt.{1} (Game.mk.{0} x) (Surreal.toGame.{0} y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _ ((0 : Surreal) : Surreal.{0})) (by
  simp)

-- IGame.le_of_forall_moves_left_lf, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.le_of_forall_moves_left_lf.h2 : ¬∀ {x y : IGame.{0}},
        (∀ (z : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) z →
              ∃ (w : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) w ∧ LE.le.{1} w z) →
          LE.le.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  simp)) (by
  simp)

-- IGame.le_of_forall_moves_left_lf, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.le_of_forall_moves_left_lf.h3 : ¬∀ {x y : IGame.{0}},
        (∀ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) z → ¬LE.le.{1} x z) → LE.le.{1} y x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  simp)

-- IGame.Impartial.gf_iff_fuzzy, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.gf_iff_fuzzy.h2 : ¬∀ {x y : IGame.{0}} [hy : IGame.Impartial.{0} y], ¬LE.le.{1} x y ↔ x ‖ y := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  (simp <;> game_cmp <;> done))

-- IGame.Impartial.gf_iff_fuzzy, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.gf_iff_fuzzy.h3 : ¬∀ {x y : IGame.{0}} [hx : IGame.Impartial.{0} x], ¬LE.le.{1} x y ↔ x ‖ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((-1 : IGame) : IGame.{0}) _) (by
  (simp <;> game_cmp <;> done))

-- IGame.Numeric.not_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.not_lt.h2 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} y], ¬LT.lt.{1} x y ↔ LE.le.{1} y x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.not_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.not_lt.h3 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x], ¬LT.lt.{1} x y ↔ LE.le.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) _) (by
  (simp <;> omega))

-- IGame.Impartial.equiv_or_fuzzy, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.equiv_or_fuzzy.h2 : ¬∀ (x y : IGame.{0}) [hy : IGame.Impartial.{0} y], x ≈ y ∨ x ‖ y := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  (simp <;> game_cmp <;> done))

-- IGame.Impartial.equiv_or_fuzzy, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.equiv_or_fuzzy.h3 : ¬∀ (x y : IGame.{0}) [hx : IGame.Impartial.{0} x], x ≈ y ∨ x ‖ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _) (by
  (simp <;> game_cmp <;> done))

-- IGame.Numeric.left_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.left_lt.h2 : ¬∀ {x y : IGame.{0}}, Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) y → LT.lt.{1} y x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  simp)

-- IGame.Numeric.left_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.left_lt.h3 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x], LT.lt.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- Surreal.Cut.supLeft_mem_of_short, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.supLeft_mem_of_short.h2 : ¬∀ {x : IGame.{0}} [inst : IGame.Short.{0} x],
        ∃ (y : IGame.{0}),
          Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) y ∧
            Eq.{2} (Surreal.Cut.rightGame.{0} (Game.mk.{0} y)) (Surreal.Cut.supLeft.{0} x) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- Nimber.IsRing.toIsField_of_X_sq_lt_leastNoRoots, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.toIsField_of_X_sq_lt_leastNoRoots.h1 : Not
      (∀ {x : Nimber.{0}},
        @LE.le.{1}
            (WithTop.{1}
              (@Polynomial.{1} Nimber.{0}
                (@CommSemiring.toSemiring.{1} Nimber.{0}
                  (@Semifield.toCommSemiring.{1} Nimber.{0} (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0})))))
            (@Preorder.toLE.{1}
              (WithTop.{1}
                (@Polynomial.{1} Nimber.{0}
                  (@CommSemiring.toSemiring.{1} Nimber.{0}
                    (@Semifield.toCommSemiring.{1} Nimber.{0} (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0})))))
              (@WithTop.instPreorder.{1}
                (@Polynomial.{1} Nimber.{0}
                  (@CommSemiring.toSemiring.{1} Nimber.{0}
                    (@Semifield.toCommSemiring.{1} Nimber.{0} (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0}))))
                (@PartialOrder.toPreorder.{1}
                  (@Polynomial.{1} Nimber.{0}
                    (@CommSemiring.toSemiring.{1} Nimber.{0}
                      (@Semifield.toCommSemiring.{1} Nimber.{0} (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0}))))
                  (@ConditionallyCompletePartialOrderSup.toPartialOrder.{1}
                    (@Polynomial.{1} Nimber.{0}
                      (@CommSemiring.toSemiring.{1} Nimber.{0}
                        (@Semifield.toCommSemiring.{1} Nimber.{0}
                          (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0}))))
                    (@ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.{1}
                      (@Polynomial.{1} Nimber.{0}
                        (@CommSemiring.toSemiring.{1} Nimber.{0}
                          (@Semifield.toCommSemiring.{1} Nimber.{0}
                            (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0}))))
                      (@ConditionallyCompleteLattice.toConditionallyCompletePartialOrder.{1}
                        (@Polynomial.{1} Nimber.{0}
                          (@CommSemiring.toSemiring.{1} Nimber.{0}
                            (@Semifield.toCommSemiring.{1} Nimber.{0}
                              (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0}))))
                        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{1}
                          (@Polynomial.{1} Nimber.{0}
                            (@CommSemiring.toSemiring.{1} Nimber.{0}
                              (@Semifield.toCommSemiring.{1} Nimber.{0}
                                (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0}))))
                          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{1}
                            (@Polynomial.{1} Nimber.{0}
                              (@CommSemiring.toSemiring.{1} Nimber.{0}
                                (@Semifield.toCommSemiring.{1} Nimber.{0}
                                  (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0}))))
                            Nimber.Lex.instConditionallyCompleteLinearOrderBotPolynomial.{0}))))))))
            (@WithTop.some.{1}
              (@Polynomial.{1} Nimber.{0}
                (@CommSemiring.toSemiring.{1} Nimber.{0}
                  (@Semifield.toCommSemiring.{1} Nimber.{0} (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0}))))
              (@HPow.hPow.{1, 0, 1}
                (@Polynomial.{1} Nimber.{0}
                  (@CommSemiring.toSemiring.{1} Nimber.{0}
                    (@Semifield.toCommSemiring.{1} Nimber.{0} (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0}))))
                Nat
                (@Polynomial.{1} Nimber.{0}
                  (@CommSemiring.toSemiring.{1} Nimber.{0}
                    (@Semifield.toCommSemiring.{1} Nimber.{0} (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0}))))
                (@instHPow.{1, 0}
                  (@Polynomial.{1} Nimber.{0}
                    (@CommSemiring.toSemiring.{1} Nimber.{0}
                      (@Semifield.toCommSemiring.{1} Nimber.{0} (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0}))))
                  Nat
                  (@NPow.toPow.{1}
                    (@Polynomial.{1} Nimber.{0}
                      (@CommSemiring.toSemiring.{1} Nimber.{0}
                        (@Semifield.toCommSemiring.{1} Nimber.{0}
                          (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0}))))
                    (@Monoid.toNPow.{1}
                      (@Polynomial.{1} Nimber.{0}
                        (@CommSemiring.toSemiring.{1} Nimber.{0}
                          (@Semifield.toCommSemiring.{1} Nimber.{0}
                            (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0}))))
                      (@Semiring.toMonoid.{1}
                        (@Polynomial.{1} Nimber.{0}
                          (@CommSemiring.toSemiring.{1} Nimber.{0}
                            (@Semifield.toCommSemiring.{1} Nimber.{0}
                              (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0}))))
                        (@AddMonoidAlgebra.semiring.{1, 0} Nimber.{0} Nat
                          (@CommSemiring.toSemiring.{1} Nimber.{0}
                            (@Semifield.toCommSemiring.{1} Nimber.{0}
                              (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0})))
                          Nat.instAddMonoid)))))
                (@Polynomial.X.{1} Nimber.{0}
                  (@CommSemiring.toSemiring.{1} Nimber.{0}
                    (@Semifield.toCommSemiring.{1} Nimber.{0} (@Field.toSemifield.{1} Nimber.{0} Nimber.instField.{0}))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            x.leastNoRoots →
          x.IsField) := fun hc_h => absurd (@hc_h (@OfNat.ofNat.{1} Nimber.{0} (nat_lit 0) (@Zero.toOfNat0.{1} Nimber.{0} instZeroNimber.{0})) (by
  simp)) (by
  nofun)

-- IGame.equiv_toIGame_toDyadic, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.equiv_toIGame_toDyadic.h2 : ¬∀ (x : IGame.{0}) [inst : IGame.Short.{0} x], IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) _) (by
  simp)

-- IGame.natCast_mul_wpow_mem_moves_left_wpow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.natCast_mul_wpow_mem_moves_left_wpow.h3 : ¬∀ {x y : IGame.{0}} (n : ℕ),
        Membership.mem.{1, 1} (IGame.moves.{0} Player.left (Wpow.wpow.{1} x)) (HMul.hMul.{1, 1, 1} (↑n) (Wpow.wpow.{1} y)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (1)) (by
  simp)

-- IGame.le_ordinalSum_iff_of_forall_wsubposition, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.le_ordinalSum_iff_of_forall_wsubposition.h3 : ¬∀ {x y z : IGame.{0}}, LE.le.{1} z (IGame.ordinalSum.{0} x y) ↔ LE.le.{1} z x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  simp)

-- IGame.Numeric.inv_mul_cancel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.inv_mul_cancel.h2 : ¬∀ {x : IGame.{0}} [inst : IGame.Numeric.{0} x], HMul.hMul.{1, 1, 1} (Inv.inv.{1} x) x ≈ 1 := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) _) (by
  (game_cmp; done))

-- Nimber.pow_le_of_forall_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.pow_le_of_forall_ne.h3 : ¬∀ {a b : Nimber.{0}} {n : ℕ}, LE.le.{1} (HPow.hPow.{1, 0, 1} a n) b := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- IGame.Impartial.equiv_iff_add_equiv_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.equiv_iff_add_equiv_zero.h2 : ¬∀ {x y : IGame.{0}}, x ≈ y ↔ HAdd.hAdd.{1, 1, 1} x y ≈ 0 := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  (simp <;> game_cmp <;> done))

-- Surreal.Cut.ext', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.ext'.h2 : ¬∀ {c d : Surreal.Cut.{0}}, Eq.{2} c d := fun hc_h => absurd (@hc_h (Bot.bot.{1}) (Top.top.{1})) (by
  simp)

-- Nimber.IsAlgClosed.sqrt_map_fieldClosure_succ_pow_two_pow_succ, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsAlgClosed.sqrt_map_fieldClosure_succ_pow_two_pow_succ.h1 : ¬∀ {t : Nimber.{0}} (n : ℕ), Nimber.IsAlgClosed.{0} t := fun hc_h => absurd (@hc_h (1) (0)) (by
  nofun)

-- IGame.eq_sub_one_of_mem_moves_left_intCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.eq_sub_one_of_mem_moves_left_intCast.h2 : ¬∀ {n : ℤ} {x : IGame.{0}}, Eq.{2} x ↑(HSub.hSub.{0, 0, 0} n 1) := fun hc_h => absurd (@hc_h (0) ((0 : IGame) : IGame.{0})) (by
  simp)

-- Surreal.leadingCoeff_sub_eq_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.leadingCoeff_sub_eq_left.h2 : ¬∀ {x y : Surreal.{0}}, Eq.{1} (Surreal.leadingCoeff.{0} (HSub.hSub.{1, 1, 1} x y)) (Surreal.leadingCoeff.{0} x) := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0})) (by
  simp)

-- Surreal.leadingTerm_sub_eq_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.leadingTerm_sub_eq_right.h2 : ¬∀ {x y : Surreal.{0}},
        Eq.{2} (Surreal.leadingTerm.{0} (HSub.hSub.{1, 1, 1} y x)) (Neg.neg.{1} (Surreal.leadingTerm.{0} x)) := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0})) (by
  simp)

-- Surreal.leadingCoeff_sub_eq_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.leadingCoeff_sub_eq_right.h2 : ¬∀ {x y : Surreal.{0}},
        Eq.{1} (Surreal.leadingCoeff.{0} (HSub.hSub.{1, 1, 1} y x)) (Neg.neg.{0} (Surreal.leadingCoeff.{0} x)) := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0})) (by
  simp)

-- SurrealHahnSeries.TermSeq.term_coe_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SurrealHahnSeries.TermSeq.term_coe_of_lt.h2 : ¬∀ {s : SurrealHahnSeries.TermSeq.{0}} {i : Ordinal.{0}}, LT.lt.{1} i (SurrealHahnSeries.TermSeq.length.{0} s) := fun hc_h => absurd (@hc_h (0) ((0 : Ordinal) : Ordinal.{0})) (by
  simp)

-- Surreal.Cut.Numeric.ne_bot, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.Numeric.ne_bot.h1 : ¬∀ (x : Surreal.Cut.{0}), Ne.{2} x Bot.bot.{1} := fun hc_h => absurd (@hc_h (Bot.bot.{1})) (by
  simp)

-- Dyadic.max_birthday_lower_birthday_upper_add_one_of_den_ne_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.max_birthday_lower_birthday_upper_add_one_of_den_ne_one.h1 : ¬∀ {x : Dyadic}, Max.max x.lower.birthday x.upper.birthday + 1 = x.birthday := fun hc_h => absurd (@hc_h (Dyadic.zero)) (by
  decide +kernel)

-- Dyadic.birthday_of_den_ne_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.birthday_of_den_ne_one.h1 : ¬∀ {x : Dyadic}, x.den ≠ 1 := fun hc_h => absurd (@hc_h (Dyadic.zero)) (by
  decide +kernel)

-- Nimber.IsAlgClosed.isAlgClosed, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsAlgClosed.isAlgClosed.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsAlgClosed.{0} x := fun hc_h => absurd (@hc_h (1)) (by
  nofun)

-- Dyadic.natAbs_num_div_den_lower_eq_natAbs_num_div_den, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.natAbs_num_div_den_lower_eq_natAbs_num_div_den.h1 : ¬∀ {x : Dyadic}, x.lower.num.natAbs / x.lower.den = x.num.natAbs / x.den := fun hc_h => absurd (@hc_h ((1 : Dyadic) : Dyadic)) (by
  decide +kernel)

-- Nimber.card_fieldClosure, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.card_fieldClosure.h1 : ¬∀ {x : Nimber.{0}},
        Eq.{2} (Ordinal.card.{0} (Nimber.val.{0} (Nimber.fieldClosure.{0} x))) (Ordinal.card.{0} (Nimber.val.{0} x)) := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Nimber.card_groupClosure, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.card_groupClosure.h1 : ¬∀ {x : Nimber.{0}},
        Eq.{2} (Ordinal.card.{0} (Nimber.val.{0} (Nimber.groupClosure.{0} x))) (Ordinal.card.{0} (Nimber.val.{0} x)) := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Surreal.Cut.Numeric.ne_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.Numeric.ne_top.h1 : ¬∀ (x : Surreal.Cut.{0}), Ne.{2} x Top.top.{1} := fun hc_h => absurd (@hc_h (Top.top.{1})) (by
  simp)

-- IGame.Dicotic.ne_zero_iff', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Dicotic.ne_zero_iff'.h1 : ¬∀ {x : IGame.{0}}, Ne.{2} x 0 ↔ ∀ (p : Player), Set.Nonempty.{1} (IGame.moves.{0} p x) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0})) (by
  simp)

-- Nimber.bddAbove_of_small, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.bddAbove_of_small.h1 : ¬∀ (s : Set.{1} Nimber.{0}), BddAbove.{1} s := fun hc_h => absurd (@hc_h (Top.top.{1})) (by
  simp)

-- IGame.tiny_toIGame_birthday_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.tiny_toIGame_birthday_lt.h1 : ¬∀ {x : IGame.{0}}, LT.lt.{1} (IGame.tiny.{0} (NatOrdinal.toIGame.{0} (IGame.birthday.{0} x))) x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- Game.confusionInterval_mk_of_numeric, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Game.confusionInterval_mk_of_numeric.h1 : ¬∀ (x : IGame.{0}), Eq.{2} (Game.confusionInterval.{0} (Game.mk.{0} x)) EmptyCollection.emptyCollection.{1} := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0})) (by
  simp)

-- NatOrdinal.two_opow_log_add, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.two_opow_log_add.h1 : ¬∀ {o : Ordinal.{0}},
        Eq.{2}
          (HAdd.hAdd.{1, 1, 1} (NatOrdinal.of.{0} (HPow.hPow.{1, 1, 1} 2 (Ordinal.log.{0} 2 o)))
            (NatOrdinal.of.{0} (HMod.hMod.{1, 1, 1} o (HPow.hPow.{1, 1, 1} 2 (Ordinal.log.{0} 2 o)))))
          (NatOrdinal.of.{0} o) := fun hc_h => absurd (@hc_h ((0 : Ordinal) : Ordinal.{0})) (by
  simp)

-- Dyadic.den_lower_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.den_lower_lt.h1 : ¬∀ {x : Dyadic}, x.lower.den < x.den := fun hc_h => absurd (@hc_h (Dyadic.zero)) (by
  simp)

-- Nimber.two_opow_log_add, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.two_opow_log_add.h1 : ¬∀ {o : Ordinal.{0}},
        Eq.{2}
          (HAdd.hAdd.{1, 1, 1} (Nimber.of.{0} (HPow.hPow.{1, 1, 1} 2 (Ordinal.log.{0} 2 o)))
            (Nimber.of.{0} (HMod.hMod.{1, 1, 1} o (HPow.hPow.{1, 1, 1} 2 (Ordinal.log.{0} 2 o)))))
          (Nimber.of.{0} o) := fun hc_h => absurd (@hc_h ((0 : Ordinal) : Ordinal.{0})) (by
  simp)

-- Dyadic.max_den_lower_upper, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.max_den_lower_upper.h1 : ¬∀ {x : Dyadic}, Max.max x.lower.den x.upper.den = x.den / 2 := fun hc_h => absurd (@hc_h (Dyadic.zero)) (by
  simp)

-- Nimber.IsRing.two_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.two_le.h1 : ¬∀ {x : Nimber.{0}}, LE.le.{1} (Nimber.of.{0} 2) x := fun hc_h => absurd (@hc_h (1)) (by
  simp)

-- NatOrdinal.not_bddAbove_compl_of_small, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.not_bddAbove_compl_of_small.h1 : ¬∀ (s : Set.{1} NatOrdinal.{0}), ¬BddAbove.{1} (Compl.compl.{1} s) := fun hc_h => absurd (@hc_h (Top.top.{1})) (by
  simp)

-- Nimber.IsField.fieldAdjoin_simple_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.fieldAdjoin_simple_self.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- Nimber.IsAlgClosed.algebraAdjoin_simple_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsAlgClosed.algebraAdjoin_simple_self.h1 : ¬∀ {t : Nimber.{0}}, Nimber.IsAlgClosed.{0} t := fun hc_h => absurd (@hc_h (1)) (by
  nofun)

-- Nimber.IsField.toIsRing, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.toIsRing.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsRing.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- IGame.Impartial.neg_equiv, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.neg_equiv.h1 : ¬∀ (x : IGame.{0}), Neg.neg.{1} x ≈ x := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- Surreal.mk_out_equiv, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.mk_out_equiv.h1 : ¬∀ (x : IGame.{0}), IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0})) (by
  simp)

