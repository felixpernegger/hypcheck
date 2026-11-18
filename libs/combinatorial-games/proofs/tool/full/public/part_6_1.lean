module
public import CombinatorialGames

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- IGame.Numeric.mul_le_mul, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_le_mul.h8 : ¬∀ {a b c d : IGame.{0}} [inst : IGame.Numeric.{0} a] [inst : IGame.Numeric.{0} b] [inst : IGame.Numeric.{0} c]
        [inst : IGame.Numeric.{0} d],
        LE.le.{1} c d → LE.le.{1} 0 c → LE.le.{1} 0 b → LE.le.{1} (HMul.hMul.{1, 1, 1} a c) (HMul.hMul.{1, 1, 1} b d) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _ _ (by
  rfl) (by
  simp) (by
  rfl)) (by
  simp)

-- IGame.Numeric.mul_le_mul, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_le_mul.h9 : ¬∀ {a b c d : IGame.{0}} [inst : IGame.Numeric.{0} a] [inst : IGame.Numeric.{0} b] [inst : IGame.Numeric.{0} c]
        [inst : IGame.Numeric.{0} d],
        LE.le.{1} a b → LE.le.{1} 0 c → LE.le.{1} 0 b → LE.le.{1} (HMul.hMul.{1, 1, 1} a c) (HMul.hMul.{1, 1, 1} b d) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ _ _ (by
  rfl) (by
  simp) (by
  simp)) (by
  simp)

-- IGame.Numeric.mulOption_congr₁, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mulOption_congr₁.h10 : ¬∀ {x₁ x₂ y a b : IGame.{0}} [inst : IGame.Numeric.{0} x₁] [inst : IGame.Numeric.{0} x₂] [inst : IGame.Numeric.{0} y]
        [inst : IGame.Numeric.{0} a] [inst : IGame.Numeric.{0} b],
        IGame.mulOption.{0} x₁ y a b ≈ IGame.mulOption.{0} x₂ y a b := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _ _ _) (by
  (game_cmp; done))

-- IGame.Numeric.mul_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_congr.h8 : ¬∀ {x₁ x₂ y₁ y₂ : IGame.{0}} [inst : IGame.Numeric.{0} x₁] [inst : IGame.Numeric.{0} x₂] [inst : IGame.Numeric.{0} y₁]
        [inst : IGame.Numeric.{0} y₂], y₁ ≈ y₂ → HMul.hMul.{1, 1, 1} x₁ y₁ ≈ HMul.hMul.{1, 1, 1} x₂ y₂ := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _ _ (by
  rfl)) (by
  (game_cmp; done))

-- IGame.Numeric.mul_congr, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_congr.h9 : ¬∀ {x₁ x₂ y₁ y₂ : IGame.{0}} [inst : IGame.Numeric.{0} x₁] [inst : IGame.Numeric.{0} x₂] [inst : IGame.Numeric.{0} y₁]
        [inst : IGame.Numeric.{0} y₂], x₁ ≈ x₂ → HMul.hMul.{1, 1, 1} x₁ y₁ ≈ HMul.hMul.{1, 1, 1} x₂ y₂ := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _ _ (by
  rfl)) (by
  (game_cmp; done))

-- NatOrdinal.mul_add_lt₃, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.mul_add_lt₃.h6 : ¬∀ {a b c a' b' c' : NatOrdinal.{0}},
        LT.lt.{1} b' b →
          LT.lt.{1} c' c →
            LT.lt.{1}
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b) c)
                    (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b') c))
                  (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b) c'))
                (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b') c'))
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b) c)
                    (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b') c))
                  (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b) c'))
                (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b') c')) := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (0) (0) (by
  simp) (by
  simp)) (by
  simp)

-- NatOrdinal.mul_add_lt₃, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.mul_add_lt₃.h7 : ¬∀ {a b c a' b' c' : NatOrdinal.{0}},
        LT.lt.{1} a' a →
          LT.lt.{1} c' c →
            LT.lt.{1}
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b) c)
                    (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b') c))
                  (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b) c'))
                (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b') c'))
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b) c)
                    (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b') c))
                  (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b) c'))
                (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b') c')) := fun hc_h => absurd (@hc_h (1) (0) (1) (0) (0) (0) (by
  simp) (by
  simp)) (by
  simp)

-- NatOrdinal.mul_add_lt₃, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.mul_add_lt₃.h8 : ¬∀ {a b c a' b' c' : NatOrdinal.{0}},
        LT.lt.{1} a' a →
          LT.lt.{1} b' b →
            LT.lt.{1}
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b) c)
                    (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b') c))
                  (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b) c'))
                (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b') c'))
              (HAdd.hAdd.{1, 1, 1}
                (HAdd.hAdd.{1, 1, 1}
                  (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b) c)
                    (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b') c))
                  (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a' b) c'))
                (HMul.hMul.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b') c')) := fun hc_h => absurd (@hc_h (1) (1) (0) (0) (0) (0) (by
  simp) (by
  simp)) (by
  simp)

-- sign_sub_lt_of_mem_Icc, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.sign_sub_lt_of_mem_Icc.h3 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : AddGroup α] {x y z : α},
        x < y → z ∈ Set.Icc x y → SignType.sign (x - z) < SignType.sign (y - z) := fun hc_h => absurd (@hc_h (Fin 2) (Fin.instLinearOrder) ((Fin.addCommGroup 2).toAddGroup) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- sign_sub_lt_of_mem_Icc, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.sign_sub_lt_of_mem_Icc.h7 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : AddGroup α] [inst_2 : AddRightMono α] {x y z : α},
        z ∈ Set.Icc x y → SignType.sign (x - z) < SignType.sign (y - z) := fun hc_h => absurd (@hc_h (ℤ) (Int.instLinearOrder) (Int.instAddGroup) _ (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- sign_sub_lt_of_mem_Icc, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.sign_sub_lt_of_mem_Icc.h8 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : AddGroup α] [inst_2 : AddRightMono α] {x y z : α},
        x < y → SignType.sign (x - z) < SignType.sign (y - z) := fun hc_h => absurd (@hc_h (ℤ) (Int.instLinearOrder) (Int.instAddGroup) _ (0) (1) (-1) (by
  decide)) (by
  decide +kernel)

-- sign_sub_eq_of_notMem_Icc, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.sign_sub_eq_of_notMem_Icc.h7 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : AddGroup α] [inst_2 : AddRightMono α] {x y z : α},
        z ∉ Set.Icc x y → SignType.sign (x - z) = SignType.sign (y - z) := fun hc_h => absurd (@hc_h (ℤ) (Int.instLinearOrder) (Int.instAddGroup) _ (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- sign_sub_eq_of_notMem_Icc, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.sign_sub_eq_of_notMem_Icc.h8 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : AddGroup α] [inst_2 : AddRightMono α] {x y z : α},
        x ≤ y → SignType.sign (x - z) = SignType.sign (y - z) := fun hc_h => absurd (@hc_h (ℤ) (Int.instLinearOrder) (Int.instAddGroup) _ (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Surreal.birthday_ofSets_le_of_btwn, hypothesis 5: removable
/- FAILED: 2:0: unused universe parameter 'u' | 11:42: unsolved goals
s t : Set Surreal
z : Surreal
inst : Small.{u, u + 1} ↑s
inst_1 : Small.{u, u + 1} ↑t
hL : ∀ x ∈ s, x < z
hR : ∀ y ∈ t, z < y
x y : Surreal
a : x ∈ s
a_1 : y ∈ t
⊢ x < y | 2:0: unused universe parameter 'u' | 50:8: unsolved goals
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
theorem HypCheckProof.Surreal.birthday_ofSets_le_of_btwn.h5.der.{u} : ∀ {s t : Set Surreal} {z : Surreal} [inst : Small ↑s] [inst : Small ↑t],
      (∀ x ∈ s, x < z) → (∀ y ∈ t, z < y) → ∀ x ∈ s, ∀ y ∈ t, x < y := by
  (intros; grind)
theorem HypCheckProof.Surreal.birthday_ofSets_le_of_btwn.h5.{u} : ∀ {s t : Set Surreal} {z : Surreal} [inst : Small ↑s] [inst_1 : Small ↑t] (hL : ∀ x ∈ s, x < z) (hR : ∀ y ∈ t, z < y),
      !{s | t}.birthday ≤ z.birthday := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Surreal.birthday_ofSets_le_of_btwn hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Surreal.birthday_ofSets_le_of_btwn.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6) hc_x5 hc_x6
-/

-- IGame.Numeric.mul_left_cancel, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_left_cancel.h6 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        HMul.hMul.{1, 1, 1} x y ≈ HMul.hMul.{1, 1, 1} x z → y ≈ z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _ (by
  simp)) (by
  (game_cmp; done))

-- IGame.Numeric.mul_left_cancel, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_left_cancel.h7 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        ¬x ≈ 0 → y ≈ z := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _ (by
  (game_cmp; done))) (by
  (game_cmp; done))

-- IGame.Numeric.mul_wpow_lt_mul_wpow_of_pos', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_wpow_lt_mul_wpow_of_pos'.h6 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] (r : Dyadic) {s : Dyadic},
        LT.lt.{1} x y → LT.lt.{1} (HMul.hMul.{1, 1, 1} (↑r) (Wpow.wpow.{1} x)) (HMul.hMul.{1, 1, 1} (↑s) (Wpow.wpow.{1} y)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ (Dyadic.zero) (Dyadic.zero) (by
  simp)) (by
  simp)

-- IGame.Numeric.mul_wpow_lt_mul_wpow_of_pos', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_wpow_lt_mul_wpow_of_pos'.h7 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] (r : Dyadic) {s : Dyadic},
        LT.lt.{0} 0 s → LT.lt.{1} (HMul.hMul.{1, 1, 1} (↑r) (Wpow.wpow.{1} x)) (HMul.hMul.{1, 1, 1} (↑s) (Wpow.wpow.{1} y)) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ ((1 : Dyadic) : Dyadic) ((1 : Dyadic) : Dyadic) (by
  decide)) (by
  simp)

-- Surreal.ofSets_eq_of_forall_birthday_le', hypothesis 4: removable
/- FAILED: 2:0: unused universe parameter 'u' | 23:17: unsolved goals
st : Player → Set Surreal
z : Surreal
inst : Small.{u, u + 1} ↑(st Player.left)
inst_1 : Small.{u, u + 1} ↑(st Player.right)
hL : ∀ x ∈ st Player.left, x < z
hR : ∀ y ∈ st Player.right, z < y
h : ∀ (w : Surreal), (∀ x ∈ st Player.left, x < w) → (∀ y ∈ st Player.right, w < y) → z.birthday ≤ w.birthday
x : Surreal
a : x ∈ st Player.left
y : Surreal
a_1 : y ∈ st Player.right
⊢ x < y | 2:0: unused universe parameter 'u' | 88:30: unsolved goals
st : Player → Set Surreal
z : Surreal
inst : Small.{u, u + 1} ↑(st Player.left)
inst_1 : Small.{u, u + 1} ↑(st Player.right)
hL : ∀ x ∈ st Player.left, x < z
hR : ∀ y ∈ st Player.right, z < y
h : ∀ (w : Surreal), (∀ x ∈ st Player.left, x < w) → (∀ y ∈ st Player.right, w < y) → z.birthday ≤ w.birthday
x : Surreal
a : x ∈ st Player.left
y : Surreal
a_1 : y ∈ st Player.right
⊢ x < y | 2:0: unused universe parameter 'u' | 2:0: unused universe parameter 'u' | 2:0: unused universe parameter 'u'
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Surreal.ofSets_eq_of_forall_birthday_le'.h4.der.{u} : ∀ {st : Player → Set Surreal} {z : Surreal} [inst : Small ↑(st Player.left)] [inst : Small ↑(st Player.right)],
      (∀ x ∈ st Player.left, x < z) →
        (∀ y ∈ st Player.right, z < y) →
          (∀ (w : Surreal), (∀ x ∈ st Player.left, x < w) → (∀ y ∈ st Player.right, w < y) → z.birthday ≤ w.birthday) →
            ∀ x ∈ st Player.left, ∀ y ∈ st Player.right, x < y := by
  (intros; grind)
theorem HypCheckProof.Surreal.ofSets_eq_of_forall_birthday_le'.h4.{u} : ∀ {st : Player → Set Surreal} {z : Surreal} [inst : Small ↑(st Player.left)] [inst_1 : Small ↑(st Player.right)]
      (hL : ∀ x ∈ st Player.left, x < z) (hR : ∀ y ∈ st Player.right, z < y)
      (h : ∀ (w : Surreal), (∀ x ∈ st Player.left, x < w) → (∀ y ∈ st Player.right, w < y) → z.birthday ≤ w.birthday),
      !{st} = z := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Surreal.ofSets_eq_of_forall_birthday_le' hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Surreal.ofSets_eq_of_forall_birthday_le'.h4.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6) hc_x4 hc_x5 hc_x6
-/

-- GameGraph.mem_moves_toLGame_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.GameGraph.mem_moves_toLGame_of_mem.h7 : ¬∀ {α : Type} {c : GameGraph.{0} α} {p : Player} [Hl : ∀ (a : α), Small.{0, 0} ↑(GameGraph.moves.{0} c Player.left a)]
        [Hr : ∀ (a : α), Small.{0, 0} ↑(GameGraph.moves.{0} c Player.right a)] {a b : α},
        Membership.mem.{1, 1} (LGame.moves.{0} p (GameGraph.toLGame.{0, 0} c a)) (GameGraph.toLGame.{0, 0} c b) := fun hc_h => absurd (@hc_h (ℕ) (GameGraph.mk.{0} fun (a : Player) (a_1 : ℕ) => Set.ofPred.{0} fun (x : ℕ) => False) (Player.left : Player) _ _ (0) (0)) (by
  simp)

-- IGame.Numeric.div_lt_iff_of_neg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.div_lt_iff_of_neg.h6 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        LT.lt.{1} (HDiv.hDiv.{1, 1, 1} x y) z ↔ LT.lt.{1} (HMul.hMul.{1, 1, 1} z y) x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ _) (by
  simp)

-- IGame.Fits.equiv_of_forall_moves_of_equiv, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Fits.equiv_of_forall_moves_of_equiv.h4 : ¬∀ {x y : IGame.{0}} (a : IGame.{0}),
        x ≈ a →
          (∀ (z : IGame.{0}),
              Membership.mem.{1, 1} (IGame.moves.{0} Player.left a) z →
                ∃ (w : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) w ∧ LE.le.{1} z w) →
            (∀ (z : IGame.{0}),
                Membership.mem.{1, 1} (IGame.moves.{0} Player.right a) z →
                  ∃ (w : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) w ∧ LE.le.{1} w z) →
              x ≈ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  rfl) (by
  simp) (by
  simp)) (by
  (game_cmp; done))

-- IGame.Numeric.mul_lt_mul_left_of_neg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_lt_mul_left_of_neg.h6 : ¬∀ {x y z : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y] [inst : IGame.Numeric.{0} z],
        LT.lt.{1} (HMul.hMul.{1, 1, 1} z x) (HMul.hMul.{1, 1, 1} z y) ↔ LT.lt.{1} y x := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ _) (by
  simp)

-- IGame.Numeric.mul_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_pos.h4 : ¬∀ {x₁ x₂ : IGame.{0}} [inst : IGame.Numeric.{0} x₁] [inst : IGame.Numeric.{0} x₂],
        LT.lt.{1} 0 x₂ → LT.lt.{1} 0 (HMul.hMul.{1, 1, 1} x₁ x₂) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _ (by
  simp)) (by
  simp)

-- IGame.Numeric.mul_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_pos.h5 : ¬∀ {x₁ x₂ : IGame.{0}} [inst : IGame.Numeric.{0} x₁] [inst : IGame.Numeric.{0} x₂],
        LT.lt.{1} 0 x₁ → LT.lt.{1} 0 (HMul.hMul.{1, 1, 1} x₁ x₂) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ (by
  simp)) (by
  simp)

-- IGame.Numeric.mul_neg_of_pos_of_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_neg_of_pos_of_neg.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y],
        LT.lt.{1} y 0 → LT.lt.{1} (HMul.hMul.{1, 1, 1} x y) 0 := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((-1 : IGame) : IGame.{0}) _ _ (by
  simp)) (by
  simp)

-- IGame.Numeric.mul_neg_of_pos_of_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_neg_of_pos_of_neg.h5 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y],
        LT.lt.{1} 0 x → LT.lt.{1} (HMul.hMul.{1, 1, 1} x y) 0 := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _ (by
  simp)) (by
  simp)

-- IGame.mem_birthdayFinset_of_mem_moves, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.mem_birthdayFinset_of_mem_moves.h4 : ¬∀ {p : Player} {x y : IGame.{0}} {n : ℕ},
        Membership.mem.{1, 1} (IGame.moves.{0} p x) y → Membership.mem.{1, 1} (IGame.birthdayFinset.{0} n) y := fun hc_h => absurd (@hc_h (Player.left : Player) ((2 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) (0) (by
  simp)) (by
  simp)

-- IGame.mem_birthdayFinset_of_mem_moves, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.mem_birthdayFinset_of_mem_moves.h5 : ¬∀ {p : Player} {x y : IGame.{0}} {n : ℕ},
        Membership.mem.{1, 1} (IGame.birthdayFinset.{0} (HAdd.hAdd.{0, 0, 0} n 1)) x →
          Membership.mem.{1, 1} (IGame.birthdayFinset.{0} n) y := fun hc_h => absurd (@hc_h (Player.left : Player) ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) (0) (by
  simp)) (by
  simp)

-- Ordinal.mul_add_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordinal.mul_add_lt.h4 : ¬∀ {a b c d : Ordinal.{0}},
        LT.lt.{1} b d → LT.lt.{1} (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b) c) (HMul.hMul.{1, 1, 1} a d) := fun hc_h => absurd (@hc_h ((0 : Ordinal) : Ordinal.{0}) ((0 : Ordinal) : Ordinal.{0}) ((0 : Ordinal) : Ordinal.{0}) ((1 : Ordinal) : Ordinal.{0}) (by
  simp)) (by
  simp)

-- Ordinal.mul_add_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordinal.mul_add_lt.h5 : ¬∀ {a b c d : Ordinal.{0}},
        LT.lt.{1} c a → LT.lt.{1} (HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} a b) c) (HMul.hMul.{1, 1, 1} a d) := fun hc_h => absurd (@hc_h ((1 : Ordinal) : Ordinal.{0}) ((0 : Ordinal) : Ordinal.{0}) ((0 : Ordinal) : Ordinal.{0}) ((0 : Ordinal) : Ordinal.{0}) (by
  simp)) (by
  simp)

-- IGame.Numeric.le_of_not_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.le_of_not_le.h2 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} y], ¬LE.le.{1} x y → LE.le.{1} y x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) _ (by
  simp)) (by
  simp)

-- IGame.Numeric.le_of_not_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.le_of_not_le.h3 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x], ¬LE.le.{1} x y → LE.le.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) _ (by
  simp)) (by
  (simp <;> omega))

-- IGame.Numeric.le_of_not_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.le_of_not_le.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst : IGame.Numeric.{0} y], LE.le.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _) (by
  simp)

-- Surreal.mk_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.mk_eq.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x] [inst_1 : IGame.Numeric.{0} y],
        Eq.{2} (Surreal.mk.{0} x) (Surreal.mk.{0} y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _) (by
  simp)

-- IGame.lt_of_lt_rightStop, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.lt_of_lt_rightStop.h4 : ¬∀ {x y : IGame.{0}} [inst : IGame.Short.{0} x] [inst : IGame.Numeric.{0} y], LT.lt.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _ _) (by
  simp)

-- IGame.Numeric.mul_pos_iff_of_pos_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.mul_pos_iff_of_pos_left.h4 : ¬∀ {a b : IGame.{0}} [inst : IGame.Numeric.{0} a] [inst : IGame.Numeric.{0} b],
        LT.lt.{1} 0 (HMul.hMul.{1, 1, 1} a b) ↔ LT.lt.{1} 0 b := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _ _) (by
  simp)

-- Surreal.ofSets_eq_mk, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.ofSets_eq_mk.h4 : ¬∀ {s t : Set.{1} Surreal.{0}} [inst : Small.{0, 1} ↑s] [inst : Small.{0, 1} ↑t] (x : Surreal.{0}),
        Membership.mem.{1, 1} s x → ∀ (y : Surreal.{0}), Membership.mem.{1, 1} t y → LT.lt.{1} x y := fun hc_h => absurd (@hc_h (({0} : Set Surreal) : Set.{1} Surreal.{0}) (({0} : Set Surreal) : Set.{1} Surreal.{0}) _ _) (by
  simp)

-- IGame.left_lf_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.left_lf_of_le.h3 : ¬∀ {x y z : IGame.{0}}, Membership.mem.{1, 1} (IGame.moves.{0} Player.left x) z → ¬LE.le.{1} y z := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  simp)

-- IGame.left_lf_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.left_lf_of_le.h4 : ¬∀ {x y z : IGame.{0}}, LE.le.{1} x y → ¬LE.le.{1} y z := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  rfl)) (by
  simp)

-- IGame.Numeric.of_mem_moves, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.of_mem_moves.h4 : ¬∀ {x y : IGame.{0}} {p : Player} [h : IGame.Numeric.{0} x], IGame.Numeric.{0} y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) (Player.left : Player) (by
  simp)) (by
  simp)

-- Nimber.IsGroup.toAddSubgroup_le_toAddSubgroup, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.toAddSubgroup_le_toAddSubgroup.h2 : ¬∀ {x y : Nimber.{0}}, Nimber.IsGroup.{0} y → Nimber.IsGroup.{0} x := fun hc_h => absurd (@hc_h (0) (1) (by
  simp)) (by
  nofun)

-- Nimber.IsGroup.toAddSubgroup_le_toAddSubgroup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.toAddSubgroup_le_toAddSubgroup.h3 : ¬∀ {x y : Nimber.{0}}, Nimber.IsGroup.{0} x → Nimber.IsGroup.{0} y := fun hc_h => absurd (@hc_h (1) (0) (by
  simp)) (by
  nofun)

-- ge_iff_equiv_of_neg_equiv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ge_iff_equiv_of_neg_equiv.h2 : ¬∀ {x y : IGame.{0}}, Neg.neg.{1} y ≈ y → (LE.le.{1} y x ↔ x ≈ y) := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  (simp <;> game_cmp <;> done))

-- ge_iff_equiv_of_neg_equiv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ge_iff_equiv_of_neg_equiv.h3 : ¬∀ {x y : IGame.{0}}, Neg.neg.{1} x ≈ x → (LE.le.{1} y x ↔ x ≈ y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((-1 : IGame) : IGame.{0}) (by
  simp)) (by
  (simp <;> game_cmp <;> done))

-- IGame.Numeric.not_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.not_le.h2 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} y], ¬LE.le.{1} x y ↔ LT.lt.{1} y x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.not_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.not_le.h3 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x], ¬LE.le.{1} x y ↔ LT.lt.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) _) (by
  (simp <;> omega))

-- IGame.Numeric.lt_iff_exists_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.lt_iff_exists_le.h2 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} y],
        LT.lt.{1} x y ↔
          (∃ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) z ∧ LE.le.{1} x z) ∨
            ∃ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) z ∧ LE.le.{1} z y := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- IGame.Numeric.lt_iff_exists_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.lt_iff_exists_le.h3 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x],
        LT.lt.{1} x y ↔
          (∃ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.left y) z ∧ LE.le.{1} x z) ∨
            ∃ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) z ∧ LE.le.{1} z y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) (IGame.star : IGame.{0}) _) (by
  simp)

-- IGame.Impartial.lf_iff_fuzzy, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.lf_iff_fuzzy.h3 : ¬∀ {x y : IGame.{0}} [hx : IGame.Impartial.{0} x], ¬LE.le.{1} y x ↔ x ‖ y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) _) (by
  (simp <;> game_cmp <;> done))

-- IGame.tiny_le_of_pos_of_forall_neg_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.tiny_le_of_pos_of_forall_neg_le.h2 : ¬∀ {x a : IGame.{0}},
        (∀ (y : IGame.{0}),
            Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) y →
              ∀ (z : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} Player.right y) z → LE.le.{1} (Neg.neg.{1} z) a) →
          LE.le.{1} (IGame.tiny.{0} a) x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  aesop)) (by
  (game_cmp; done))

-- SignType.orderingEquiv_sign_sub, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignType.orderingEquiv_sign_sub.h3 : ¬∀ {α : Type} [inst : AddGroup α] [inst_1 : LinearOrder α] (x y : α),
        SignType.orderingEquiv (SignType.sign (x - y)) = cmp x y := fun hc_h => absurd (@hc_h (Fin 2) ((Fin.addCommGroup 2).toAddGroup) (Fin.instLinearOrder) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Nimber.IsGroup.le_add_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsGroup.le_add_self.h3 : ¬∀ {x y : Nimber.{0}}, Nimber.IsGroup.{0} x → LE.le.{1} x (HAdd.hAdd.{1, 1, 1} x y) := fun hc_h => absurd (@hc_h (1) (1) (by
  simp)) (by
  simp)

-- Nimber.IsField.toSubfield_le_toSubfield, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.toSubfield_le_toSubfield.h2 : ¬∀ {x y : Nimber.{0}}, Nimber.IsField.{0} y → Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0) (Nimber.of 2 : Nimber.{0}) (by
  simp)) (by
  nofun)

-- Nimber.IsField.toSubfield_le_toSubfield, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.toSubfield_le_toSubfield.h3 : ¬∀ {x y : Nimber.{0}}, Nimber.IsField.{0} x → Nimber.IsField.{0} y := fun hc_h => absurd (@hc_h (Nimber.of 2 : Nimber.{0}) (0) (by
  simp)) (by
  nofun)

-- Nimber.Lex.X_pow_add_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.Lex.X_pow_add_le.h2 : ¬∀ {p q : Polynomial.{1} Nimber.{0}},
        LE.le.{1} q (HAdd.hAdd.{1, 1, 1} (HPow.hPow.{1, 0, 1} Polynomial.X.{1} (Polynomial.natDegree.{1} p)) p) →
          LE.le.{1} (HAdd.hAdd.{1, 1, 1} (HPow.hPow.{1, 0, 1} Polynomial.X.{1} (Polynomial.natDegree.{1} p)) q) p := fun hc_h => absurd (@hc_h (AddMonoidAlgebra.ofCoeff.{1, 0} 0) (AddMonoidAlgebra.ofCoeff.{1, 0} 0) (by
  simp)) (by
  simp)

-- Nimber.X_pow_lt_leastNoRoots_of_le_degree, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.X_pow_lt_leastNoRoots_of_le_degree.h2 : ¬∀ {x : Nimber.{0}} {n : ℕ}, Ne.{2} (Nimber.leastNoRoots.{0} x) Top.top.{1} := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Nimber.IsField.splits_subfield, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.splits_subfield.h1 : ¬∀ {x : Nimber.{0}}, Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0)) (by
  nofun)

-- Nimber.Lex.X_pow_add_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.Lex.X_pow_add_lt.h3 : ¬∀ {p q : Polynomial.{1} Nimber.{0}},
        Polynomial.Monic.{1} p →
          LT.lt.{1} (HAdd.hAdd.{1, 1, 1} (HPow.hPow.{1, 0, 1} Polynomial.X.{1} (Polynomial.natDegree.{1} p)) q) p := fun hc_h => absurd (@hc_h ((Polynomial.X : Polynomial Nimber) : Polynomial.{1} Nimber.{0}) (AddMonoidAlgebra.ofCoeff.{1, 0} 0) (by
  simp)) (by
  simp)

-- not_lt_of_neg_equiv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_lt_of_neg_equiv.h2 : ¬∀ {x y : IGame.{0}}, Neg.neg.{1} y ≈ y → ¬LT.lt.{1} x y := fun hc_h => absurd (@hc_h ((-1 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  simp)

-- not_lt_of_neg_equiv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_lt_of_neg_equiv.h3 : ¬∀ {x y : IGame.{0}}, Neg.neg.{1} x ≈ x → ¬LT.lt.{1} x y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0}) (by
  simp)) (by
  simp)

-- IGame.Numeric.lt_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.lt_right.h2 : ¬∀ {x y : IGame.{0}}, Membership.mem.{1, 1} (IGame.moves.{0} Player.right x) y → LT.lt.{1} x y := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0}) (by
  simp)) (by
  simp)

-- IGame.Numeric.lt_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.lt_right.h3 : ¬∀ {x y : IGame.{0}} [inst : IGame.Numeric.{0} x], LT.lt.{1} x y := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0}) _) (by
  simp)

-- SignExpansion.pred_apply_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SignExpansion.pred_apply_of_lt.h3 : ¬∀ {x : SignExpansion.{0}} [inst : SignExpansion.Small.{0} x] {o : NatOrdinal.{0}},
        Eq.{1} ((SignExpansion.pred.{0} x) o) (x o) := fun hc_h => absurd (@hc_h (0) (@SignExpansion.Small.mk (@OfNat.ofNat SignExpansion (nat_lit 0) (@Zero.toOfNat0 SignExpansion SignExpansion.instZero)) (by (try dsimp only);   (intros; simp_all; done))) (1)) (by
  simp)

-- Surreal.wlog_lt_wlog_of_vlt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.wlog_lt_wlog_of_vlt.h2 : ¬∀ {x y : Surreal.{0}}, ValuativeRel.vlt.{1} x y → LT.lt.{1} (Surreal.wlog.{0} x) (Surreal.wlog.{0} y) := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0}) (by
  simp)) (by
  simp)

-- Surreal.wlog_lt_wlog_of_vlt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.wlog_lt_wlog_of_vlt.h3 : ¬∀ {x y : Surreal.{0}}, Ne.{2} x 0 → LT.lt.{1} (Surreal.wlog.{0} x) (Surreal.wlog.{0} y) := fun hc_h => absurd (@hc_h ((1 : Surreal) : Surreal.{0}) ((0 : Surreal) : Surreal.{0}) (by
  simp)) (by
  simp)

-- Surreal.wlog_le_wlog_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.wlog_le_wlog_iff.h3 : ¬∀ {x y : Surreal.{0}}, Ne.{2} x 0 → (LE.le.{1} (Surreal.wlog.{0} x) (Surreal.wlog.{0} y) ↔ ValuativeRel.vle.{1} x y) := fun hc_h => absurd (@hc_h ((1 : Surreal) : Surreal.{0}) ((0 : Surreal) : Surreal.{0}) (by
  simp)) (by
  simp)

-- Maximal.isGreatest, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Maximal.isGreatest.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {P : α → Prop} {x : α}, IsGreatest {y : α | P y} x := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (fun n => n = 0 : ℕ → Prop) (1)) (by
  nofun)

-- IGame.leftStop_of_numeric, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.leftStop_of_numeric.h2 : ¬∀ (x : IGame.{0}) [inst : IGame.Short.{0} x], IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) _) (by
  simp)

-- Nimber.IsRing.leastNoRoots_eq_of_not_isField, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.leastNoRoots_eq_of_not_isField.h1 : ¬∀ {x : Nimber.{0}},
        ¬Nimber.IsField.{0} x →
          Eq.{2} (Nimber.leastNoRoots.{0} x)
            ↑(HAdd.hAdd.{1, 1, 1} (HMul.hMul.{1, 1, 1} (Polynomial.C.{1} (Inv.inv.{1} x)) Polynomial.X.{1}) 1) := fun hc_h => absurd (@hc_h (0) (by
  aesop)) (by
  simp)

-- Nimber.oeval_eq_of_natDegree_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.oeval_eq_of_natDegree_le.h2 : ¬∀ {p : Polynomial.{1} Nimber.{0}} {n : ℕ} (x : Nimber.{0}),
        Eq.{2} (Nimber.oeval.{0} x p)
          (Nimber.of.{0}
            (List.sum.{1}
              (List.map.{0, 1}
                (fun (k : ℕ) =>
                  HMul.hMul.{1, 1, 1} (HPow.hPow.{1, 0, 1} (Nimber.val.{0} x) k)
                    (Nimber.val.{0} ((AddMonoidAlgebra.coeff.{1, 0} p) k)))
                (List.reverse.{0} (List.range n))))) := fun hc_h => absurd (@hc_h ((Polynomial.X : Polynomial Nimber) : Polynomial.{1} Nimber.{0}) (0) (1)) (by
  simp)

-- Surreal.Cut.Fits.lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.Fits.lt.h3 : ¬∀ {x : Surreal.{0}} {y z : Surreal.Cut.{0}}, LT.lt.{1} y z := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) (Bot.bot.{1}) (Bot.bot.{1})) (by
  simp)

-- IGame.birthday_lt_of_mem_moves, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.birthday_lt_of_mem_moves.h3 : ¬∀ {p : Player} {x y : IGame.{0}}, LT.lt.{1} (IGame.birthday.{0} y) (IGame.birthday.{0} x) := fun hc_h => absurd (@hc_h (Player.left : Player) ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- NatOrdinal.of_omega0_opow_add_omega0_opow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.of_omega0_opow_add_omega0_opow.h2 : ¬∀ {x y : Ordinal.{0}},
        Eq.{2}
          (NatOrdinal.of.{0}
            (HAdd.hAdd.{1, 1, 1} (HPow.hPow.{1, 1, 1} Ordinal.omega0.{0} y) (HPow.hPow.{1, 1, 1} Ordinal.omega0.{0} x)))
          (HAdd.hAdd.{1, 1, 1} (Wpow.wpow.{1} (NatOrdinal.of.{0} y)) (Wpow.wpow.{1} (NatOrdinal.of.{0} x))) := fun hc_h => absurd (@hc_h ((1 : Ordinal) : Ordinal.{0}) ((0 : Ordinal) : Ordinal.{0})) (by
  simp)

-- IGame.miny_congr, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.miny_congr.h2 : ¬∀ {x y : IGame.{0}}, IGame.miny.{0} x ≈ IGame.miny.{0} y := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  (game_cmp; done))

-- Dyadic.ext, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.ext.h2 : ¬∀ {x y : Dyadic}, x = y := fun hc_h => absurd (@hc_h (Dyadic.zero) ((1 : Dyadic) : Dyadic)) (by
  decide +kernel)

-- Dyadic.den_add_le_den_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.den_add_le_den_right.h2 : ¬∀ {x y : Dyadic}, (x + y).den ≤ y.den := fun hc_h => absurd (@hc_h (Dyadic.half : Dyadic) (Dyadic.zero)) (by
  decide +kernel)

-- IGame.lf_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.lf_right.h2 : ¬∀ {x y : IGame.{0}}, ¬LE.le.{1} y x := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((0 : IGame) : IGame.{0})) (by
  simp)

-- IGame.eq_add_one_of_mem_moves_right_intCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.eq_add_one_of_mem_moves_right_intCast.h2 : ¬∀ {n : ℤ} {x : IGame.{0}}, Eq.{2} x ↑(HAdd.hAdd.{0, 0, 0} n 1) := fun hc_h => absurd (@hc_h (0) ((0 : IGame) : IGame.{0})) (by
  simp)

-- Nimber.mem_toAddSubgroup_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.mem_toAddSubgroup_iff.h2 : ¬∀ {x : Nimber.{0}} {y : Nimber.{0}}, Nimber.IsGroup.{0} x := fun hc_h => absurd (@hc_h (0) (0)) (by
  nofun)

-- Nimber.mem_toSubfield_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.mem_toSubfield_iff.h2 : ¬∀ {x : Nimber.{0}} {y : Nimber.{0}}, Nimber.IsField.{0} x := fun hc_h => absurd (@hc_h (0) (0)) (by
  nofun)

-- Nimber.IsRing.lt_ringClosure_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.lt_ringClosure_iff.h2 : ¬∀ {x y : Nimber.{0}}, LT.lt.{1} x (Nimber.ringClosure.{0} y) ↔ LT.lt.{1} x y := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Nimber.IsRing.ringClosure_le_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.ringClosure_le_iff.h2 : ¬∀ {x y : Nimber.{0}}, LE.le.{1} (Nimber.ringClosure.{0} y) x ↔ LE.le.{1} y x := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- Nimber.coeff_leastNoRoots_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.coeff_leastNoRoots_lt.h1 : ¬∀ {x : Nimber.{0}} (k : ℕ), Ne.{2} (Nimber.leastNoRoots.{0} x) Top.top.{1} := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Nimber.Lex.coeff_succ_of_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.Lex.coeff_succ_of_ne_zero.h2 : ¬∀ (p : Polynomial.{1} Nimber.{0}) {k : ℕ},
        Eq.{2} ((AddMonoidAlgebra.coeff.{1, 0} (Order.succ.{1} p)) k) ((AddMonoidAlgebra.coeff.{1, 0} p) k) := fun hc_h => absurd (@hc_h (AddMonoidAlgebra.ofCoeff.{1, 0} 0) (0)) (by
  simp)

-- Nimber.coeff_one_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.coeff_one_lt.h1 : ¬∀ {x : Nimber.{0}} (k : ℕ), LT.lt.{1} ((AddMonoidAlgebra.coeff.{1, 0} 1) k) x := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Nimber.Lex.lt_of_natDegree_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.Lex.lt_of_natDegree_lt.h2 : ¬∀ {p q : Polynomial.{1} Nimber.{0}}, LT.lt.{1} p q := fun hc_h => absurd (@hc_h (AddMonoidAlgebra.ofCoeff.{1, 0} 0) (AddMonoidAlgebra.ofCoeff.{1, 0} 0)) (by
  decide +kernel)

-- Nimber.oeval_lt_opow_omega0, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.oeval_lt_opow_omega0.h2 : ¬∀ {x : Nimber.{0}} {p : Polynomial.{1} Nimber.{0}},
        LT.lt.{1} (Nimber.oeval.{0} x p) (Nimber.of.{0} (HPow.hPow.{1, 1, 1} (Nimber.val.{0} x) Ordinal.omega0.{0})) := fun hc_h => absurd (@hc_h (0) (AddMonoidAlgebra.ofCoeff.{1, 0} 0)) (by
  simp)

-- Surreal.Cut.birthday_simplestBtwn_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.birthday_simplestBtwn_le.h2 : ¬∀ {x y : Surreal.Cut.{0}}, LT.lt.{1} x y := fun hc_h => absurd (@hc_h (Bot.bot.{1}) (Bot.bot.{1})) (by
  simp)

-- IGame.Impartial.equiv_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Impartial.equiv_zero.h1 : ¬∀ {x : IGame.{0}} (p : Player), x ≈ 0 ↔ ∀ (y : IGame.{0}), Membership.mem.{1, 1} (IGame.moves.{0} p x) y → y ‖ 0 := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0}) (Player.right : Player)) (by
  (simp <;> game_cmp <;> done))

-- Surreal.Cut.fits_simplestBtwn, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.Cut.fits_simplestBtwn.h2 : ¬∀ {x y : Surreal.Cut.{0}}, LT.lt.{1} x y := fun hc_h => absurd (@hc_h (Bot.bot.{1}) (Bot.bot.{1})) (by
  simp)

-- Game.mk_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Game.mk_eq.h2 : ¬∀ {x y : IGame.{0}}, Eq.{2} (Game.mk.{0} x) (Game.mk.{0} y) := fun hc_h => absurd (@hc_h ((0 : IGame) : IGame.{0}) ((1 : IGame) : IGame.{0})) (by
  simp)

-- Surreal.leadingTerm_sub_eq_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.leadingTerm_sub_eq_left.h2 : ¬∀ {x y : Surreal.{0}}, Eq.{2} (Surreal.leadingTerm.{0} (HSub.hSub.{1, 1, 1} x y)) (Surreal.leadingTerm.{0} x) := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0}) ((1 : Surreal) : Surreal.{0})) (by
  simp)

-- SurrealHahnSeries.TermSeq.coeffIdx_coe_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SurrealHahnSeries.TermSeq.coeffIdx_coe_of_lt.h2 : ¬∀ {s : SurrealHahnSeries.TermSeq.{0}} {i : Ordinal.{0}}, LT.lt.{1} i (SurrealHahnSeries.TermSeq.length.{0} s) := fun hc_h => absurd (@hc_h (0) ((0 : Ordinal) : Ordinal.{0})) (by
  simp)

-- NatOrdinal.mem_moves_left_toIGame_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NatOrdinal.mem_moves_left_toIGame_of_lt.h2 : ¬∀ {a b : NatOrdinal.{0}},
        Membership.mem.{1, 1} (IGame.moves.{0} Player.left (NatOrdinal.toIGame.{0} b)) (NatOrdinal.toIGame.{0} a) := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Nimber.IsField.fieldClosure_eq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsField.fieldClosure_eq.h1 : ¬∀ {x : Nimber.{0}}, Eq.{2} (Nimber.fieldClosure.{0} x) x := fun hc_h => absurd (@hc_h (1)) (by
  simp)

-- Nimber.not_bddAbove_compl_of_small, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.not_bddAbove_compl_of_small.h1 : ¬∀ (s : Set.{1} Nimber.{0}), ¬BddAbove.{1} (Compl.compl.{1} s) := fun hc_h => absurd (@hc_h (Top.top.{1})) (by
  simp)

-- IGame.Numeric.neg, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.neg.h1 : ¬∀ (x : IGame.{0}), IGame.Numeric.{0} (Neg.neg.{1} x) := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0})) (by
  simp)

-- Nimber.one_le_degree_leastNoRoots, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.one_le_degree_leastNoRoots.h1 : ¬∀ {x : Nimber.{0}}, Ne.{2} (Nimber.leastNoRoots.{0} x) Top.top.{1} := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Surreal.equiv_mk_out, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.equiv_mk_out.h1 : ¬∀ (x : IGame.{0}), IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0})) (by
  simp)

-- IGame.Numeric.ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Numeric.ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Surreal.birthday_mk_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.birthday_mk_le.h1 : ¬∀ (x : IGame.{0}), IGame.Numeric.{0} x := fun hc_h => absurd (@hc_h (IGame.star : IGame.{0})) (by
  simp)

-- IGame.Dicotic.ne_zero_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IGame.Dicotic.ne_zero_iff.h1 : ¬∀ {x : IGame.{0}}, Ne.{2} x 0 ↔ ∀ (p : Player), Ne.{2} (IGame.moves.{0} p x) EmptyCollection.emptyCollection.{1} := fun hc_h => absurd (@hc_h ((1 : IGame) : IGame.{0})) (by
  simp)

-- Nimber.IsRing.ne_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.ne_one.h1 : ¬∀ {x : Nimber.{0}}, Ne.{2} x 1 := fun hc_h => absurd (@hc_h (1)) (by
  simp)

-- Surreal.archimedeanClassMk_wpow_wlog, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.archimedeanClassMk_wpow_wlog.h1 : ¬∀ {x : Surreal.{0}}, Eq.{2} (ArchimedeanClass.mk.{1} (Wpow.wpow.{1} (Surreal.wlog.{0} x))) (ArchimedeanClass.mk.{1} x) := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0})) (by
  simp)

-- Nimber.IsRing.one_lt_val, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nimber.IsRing.one_lt_val.h1 : ¬∀ {x : Nimber.{0}}, LT.lt.{1} 1 (Nimber.val.{0} x) := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Dyadic.even_den, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dyadic.even_den.h1 : ¬∀ {x : Dyadic}, Even x.den := fun hc_h => absurd (@hc_h (Dyadic.zero)) (by
  decide +kernel)

-- Surreal.exists_wpow_veq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Surreal.exists_wpow_veq.h1 : ¬∀ {x : Surreal.{0}}, ∃ (y : Surreal.{0}), ValuativeRel.veq.{1} (Wpow.wpow.{1} y) x := fun hc_h => absurd (@hc_h ((0 : Surreal) : Surreal.{0})) (by
  simp)

