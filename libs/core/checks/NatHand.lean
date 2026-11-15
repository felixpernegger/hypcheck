/-!
Hand resolution of the 43 hypotheses in `Init.Data.Nat.*` that `HypCheck.lean` left unresolved
(after the v5 model recheck). For each hypothesis `hᵢ` of theorem `T`, this file proves either
`T'` (the theorem without `hᵢ`: removable) or `¬T'` (necessary). For dependent hypotheses
(the `*_congr` lemmas in `Init.Data.Nat.Fold`) necessity means `¬ ∀ indep, Hᵢ` (see `Methods.md`).

Run with the lean4 repo's stage1 binary: `lean checks/NatHand.lean`.
-/

open Nat.Internal.Linear in
section

/-! ## Removable (8) -/

-- `Nat.sub_mul_div_of_le` (`h₁`): `Nat.sub_mul_div` is the general version.
theorem NatHand.sub_mul_div_of_le (x n p : Nat) : (x - n * p) / n = x / n - p :=
  Nat.sub_mul_div x n p

-- `Nat.div_div_div_eq_div` (`dvd2`)
theorem NatHand.div_div_div_eq_div {a b c : Nat} (dvd : b ∣ a) : c / (a / b) / b = c / a := by
  rw [Nat.div_div_eq_div_mul, Nat.div_mul_cancel dvd]

-- `Nat.div_le_div_of_mul_le_mul` (`hdc`)
theorem NatHand.div_le_div_of_mul_le_mul {a b c d : Nat} (hd : d ≠ 0) (h : a * d ≤ c * b) :
    a / b ≤ c / d := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  calc a / b = a * d / (b * d) := (Nat.mul_div_mul_right a b hd').symm
    _ ≤ c * b / (b * d) := Nat.div_le_div_right h
    _ = c / d := by rw [Nat.mul_comm c b, Nat.mul_div_mul_left c d hb]

-- `Nat.mul_add_mul_div_of_dvd` (`hba`)
theorem NatHand.mul_add_mul_div_of_dvd_hba {a b c d : Nat} (hb : b ≠ 0) (hd : d ≠ 0) (hdc : d ∣ c) :
    (a * d + b * c) / (b * d) = a / b + c / d := by
  obtain ⟨m, rfl⟩ := hdc
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  rw [show a * d + b * (d * m) = (a + b * m) * d by
        rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm m d, ← Nat.mul_assoc, Nat.mul_comm b d,
          Nat.mul_assoc, Nat.mul_comm d (b * m)],
    Nat.mul_div_mul_right _ _ hd', Nat.mul_div_cancel_left _ hd',
    Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero hb)]

-- `Nat.mul_add_mul_div_of_dvd` (`hdc`): symmetric to `hba`.
theorem NatHand.mul_add_mul_div_of_dvd_hdc {a b c d : Nat} (hb : b ≠ 0) (hd : d ≠ 0) (hba : b ∣ a) :
    (a * d + b * c) / (b * d) = a / b + c / d := by
  have := NatHand.mul_add_mul_div_of_dvd_hba (a := c) (b := d) (c := a) (d := b) hd hb hba
  rwa [Nat.mul_comm d a, Nat.mul_comm d b, Nat.mul_comm c b, Nat.add_comm (c / d),
    Nat.add_comm (b * c)] at this

-- `Nat.mul_sub_mul_div_of_dvd` (`hba`)
theorem NatHand.mul_sub_mul_div_of_dvd {a b c d : Nat} (_hb : b ≠ 0) (hd : d ≠ 0) (hdc : d ∣ c) :
    (a * d - b * c) / (b * d) = a / b - c / d := by
  obtain ⟨m, rfl⟩ := hdc
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  rw [show a * d - b * (d * m) = (a - b * m) * d by
        rw [Nat.sub_mul, Nat.mul_assoc, Nat.mul_comm m d, ← Nat.mul_assoc, Nat.mul_comm b d,
          Nat.mul_assoc, Nat.mul_comm d (b * m)],
    Nat.mul_div_mul_right _ _ hd', Nat.mul_div_cancel_left _ hd', Nat.sub_mul_div]

-- `bitwise f` commutes with halving for every `f`; `f false false = false` is never used.
theorem NatHand.bitwise_div_two (f : Bool → Bool → Bool) (x y : Nat) :
    Nat.bitwise f x y / 2 = Nat.bitwise f (x / 2) (y / 2) := by
  rw [Nat.bitwise]
  by_cases hx : x = 0
  · subst hx; simp only [ite_true, Nat.zero_div]
    rw [Nat.bitwise]; simp only [ite_true]; split <;> simp
  by_cases hy : y = 0
  · subst hy; simp only [hx, ite_false, ite_true, Nat.zero_div]
    rw [Nat.bitwise]
    by_cases hx2 : x / 2 = 0 <;> simp only [hx2, ite_true, ite_false] <;> split <;> simp_all
  simp only [hx, hy, ite_false]
  split <;> omega

-- `Nat.bitwise_div_two_pow` (`of_false_false`)
theorem NatHand.bitwise_div_two_pow {f : Bool → Bool → Bool} {x y n : Nat} :
    (Nat.bitwise f x y) / 2 ^ n = Nat.bitwise f (x / 2 ^ n) (y / 2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ih, NatHand.bitwise_div_two,
      Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]

-- `Nat.shiftRight_bitwise_distrib` (`of_false_false`)
theorem NatHand.shiftRight_bitwise_distrib {f : Bool → Bool → Bool} {a b i : Nat} :
    (Nat.bitwise f a b) >>> i = Nat.bitwise f (a >>> i) (b >>> i) := by
  simp only [Nat.shiftRight_eq_div_pow, NatHand.bitwise_div_two_pow]

/-! ## Necessary (35) -/

-- `Nat.bitwise_mod_two_pow` (`of_false_false`): `f := fun _ _ => true`, `x = y = 2`, `n = 1`.
example : ¬ ∀ (f : Bool → Bool → Bool) (x y n : Nat),
    (Nat.bitwise f x y) % 2 ^ n = Nat.bitwise f (x % 2 ^ n) (y % 2 ^ n) := fun h => by
  have := h (fun _ _ => true) 2 2 1
  simp [Nat.bitwise] at this

-- `Nat.base_induction` (`digit`): `P := (· < 2)`, `b = 2`, `n = 2`.
example : ¬ ∀ (P : Nat → Prop) (n b : Nat), 1 < b → (∀ m, m < b → P m) → P n :=
  fun h => absurd (h (· < 2) 2 2 (by decide) (fun _ hm => hm)) (by decide)

-- `Nat.gcd.induction` (`H0`): `P m _ := 0 < m`, `m = n = 0`.
example : ¬ ∀ (P : Nat → Nat → Prop) (m n : Nat),
    (∀ m n, 0 < m → P (n % m) m → P m n) → P m n :=
  fun h => absurd (h (fun m _ => 0 < m) 0 0 (fun _ _ hm _ => hm)) (by decide)

-- `Nat.exists_coprime'` (`H`): `m = n = 0` forces `m' = n' = 0`, and `gcd 0 0 = 0`.
example : ¬ ∀ m n : Nat, ∃ g m' n', 0 < g ∧ Nat.Coprime m' n' ∧ m = m' * g ∧ n = n' * g := by
  intro h
  obtain ⟨g, m', n', hg, hc, hm, hn⟩ := h 0 0
  have : m' = 0 := by rcases Nat.mul_eq_zero.mp hm.symm with h | h <;> omega
  have : n' = 0 := by rcases Nat.mul_eq_zero.mp hn.symm with h | h <;> omega
  subst m' n'
  simp [Nat.Coprime] at hc

-- `Nat.fold_congr`, `foldRev_congr`, `any_congr`, `all_congr`, `dfold_congr`, `dfoldRev_congr`
-- (`w : n = m`, dependent: the conclusion uses it). Its independent parameters are `n`, `m`
-- (and `f`, `init`, `α`, which don't mention `w`), so `w` is derivable only if `∀ n m, n = m`.
example : ¬ ∀ n m : Nat, n = m := fun h => absurd (h 0 1) (by decide)

/-! ### `Nat.Internal.Linear` and `Nat.Internal.SOM`: all with `ctx := .leaf 0` -/

-- `Poly.of_isZero` (`h`): `p := [(1, fixedVar)]` denotes 1.
example : ¬ ∀ (ctx : Context) (p : Poly), p.denote ctx = 0 :=
  fun h => absurd (h (.leaf 0) [(1, fixedVar)]) (by decide)

-- `Poly.of_isNonZero` (`h`): `p := []` denotes 0.
example : ¬ ∀ (ctx : Context) (p : Poly), p.denote ctx > 0 :=
  fun h => absurd (h (.leaf 0) []) (by decide)

-- `PolyCnstr.eq_false_of_isUnsat` (`a`): `0 = 0`.
example : ¬ ∀ (ctx : Context) (c : PolyCnstr), c.denote ctx = False :=
  fun h => by have := h (.leaf 0) ⟨true, [], []⟩; simp at this; exact this rfl

-- `PolyCnstr.eq_true_of_isValid` (`a`): `0 = 1`.
example : ¬ ∀ (ctx : Context) (c : PolyCnstr), c.denote ctx = True :=
  fun h => by
    have := h (.leaf 0) ⟨true, [], [(1, fixedVar)]⟩; simp at this
    exact absurd this (show ¬ (0 : Nat) = 1 by decide)

-- `ExprCnstr.eq_false_of_isUnsat` (`h`): `0 = 0`.
example : ¬ ∀ (ctx : Context) (c : ExprCnstr), c.denote ctx = False :=
  fun h => by have := h (.leaf 0) ⟨true, .num 0, .num 0⟩; simp at this

-- `ExprCnstr.eq_true_of_isValid` (`h`): `0 = 1`.
example : ¬ ∀ (ctx : Context) (c : ExprCnstr), c.denote ctx = True :=
  fun h => by have := h (.leaf 0) ⟨true, .num 0, .num 1⟩; simp at this

-- `ExprCnstr.eq_false_of_isUnsat_k` (`h`)
example : ¬ ∀ (ctx : Context) (c : ExprCnstr), c.denote_k ctx = False :=
  fun h => by
    have := h (.leaf 0) ⟨true, .num 0, .num 0⟩
    rw [ExprCnstr.denote_k_eq_denote] at this; simp at this

-- `ExprCnstr.eq_true_of_isValid_k` (`h`)
example : ¬ ∀ (ctx : Context) (c : ExprCnstr), c.denote_k ctx = True :=
  fun h => by
    have := h (.leaf 0) ⟨true, .num 0, .num 1⟩
    rw [ExprCnstr.denote_k_eq_denote] at this; simp at this

-- `ExprCnstr.eq_of_toNormPoly_eq` (`h`): `(0 = 0) = (0 = 1)`.
example : ¬ ∀ (ctx : Context) (c d : ExprCnstr), c.denote ctx = d.denote ctx :=
  fun h => by have := h (.leaf 0) ⟨true, .num 0, .num 0⟩ ⟨true, .num 0, .num 1⟩; simp at this

-- `ExprCnstr.eq_of_toNormPoly_eq_k` (`h`)
example : ¬ ∀ (ctx : Context) (c d : ExprCnstr), c.denote_k ctx = d.denote_k ctx :=
  fun h => by
    have := h (.leaf 0) ⟨true, .num 0, .num 0⟩ ⟨true, .num 0, .num 1⟩
    rw [ExprCnstr.denote_k_eq_denote, ExprCnstr.denote_k_eq_denote] at this; simp at this

-- `Expr.eq_of_toNormPoly` and `Expr.eq_of_toNormPoly_eq` (`h`): `0 = 1`.
example : ¬ ∀ (ctx : Context) (a b : Expr), a.denote ctx = b.denote ctx :=
  fun h => absurd (h (.leaf 0) (.num 0) (.num 1)) (by decide)

-- `Expr.eq_of_toNormPoly_eq_k` (`h`)
example : ¬ ∀ (ctx : Context) (e e' : Expr), e.denote_k ctx = e'.denote_k ctx :=
  fun h => by
    have := h (.leaf 0) (.num 0) (.num 1)
    rw [Expr.denote_k_eq_denote, Expr.denote_k_eq_denote] at this
    exact absurd this (by decide)

-- `Expr.of_cancel_eq` (`h`): `(0 = 0) = (1 = 0)`.
example : ¬ ∀ (ctx : Context) (a b c d : Expr),
    (a.denote ctx = b.denote ctx) = (c.denote ctx = d.denote ctx) :=
  fun h => by have := h (.leaf 0) (.num 0) (.num 0) (.num 1) (.num 0); simp at this

-- `Expr.of_cancel_le` (`h`): `(0 ≤ 0) = (1 ≤ 0)`.
example : ¬ ∀ (ctx : Context) (a b c d : Expr),
    (a.denote ctx ≤ b.denote ctx) = (c.denote ctx ≤ d.denote ctx) :=
  fun h => by have := h (.leaf 0) (.num 0) (.num 0) (.num 1) (.num 0); simp at this

-- `Expr.of_cancel_lt` (`h`): `(0 < 1) = (1 < 0)`.
example : ¬ ∀ (ctx : Context) (a b c d : Expr),
    (a.denote ctx < b.denote ctx) = (c.denote ctx < d.denote ctx) :=
  fun h => by have := h (.leaf 0) (.num 0) (.num 1) (.num 1) (.num 0); simp at this

-- `Poly.denote_eq_cancel` (`h`): `cancel` preserves `denote_eq`, and `1 = 0` fails.
example : ¬ ∀ (ctx : Context) (m₁ m₂ : Poly), Poly.denote_eq ctx (m₁.cancel m₂) :=
  fun h => by
    have := h (.leaf 0) [(1, fixedVar)] []
    rw [Poly.denote_eq_cancel_eq] at this; exact absurd this (show ¬ (1 : Nat) = 0 by decide)

-- `Poly.of_denote_eq_cancel` (`h`)
example : ¬ ∀ (ctx : Context) (m₁ m₂ : Poly), Poly.denote_eq ctx (m₁, m₂) :=
  fun h => absurd (h (.leaf 0) [(1, fixedVar)] []) (show ¬ (1 : Nat) = 0 by decide)

-- `Poly.denote_le_cancel` (`h`): `1 ≤ 0` fails.
example : ¬ ∀ (ctx : Context) (m₁ m₂ : Poly), Poly.denote_le ctx (m₁.cancel m₂) :=
  fun h => by
    have := h (.leaf 0) [(1, fixedVar)] []
    rw [Poly.denote_le_cancel_eq] at this; exact absurd this (show ¬ (1 : Nat) ≤ 0 by decide)

-- `Poly.of_denote_le_cancel` (`h`)
example : ¬ ∀ (ctx : Context) (m₁ m₂ : Poly), Poly.denote_le ctx (m₁, m₂) :=
  fun h => absurd (h (.leaf 0) [(1, fixedVar)] []) (show ¬ (1 : Nat) ≤ 0 by decide)

-- `Poly.denote_eq_cancelAux` (`h`): `fuel = 0` returns its input.
example : ¬ ∀ (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly),
    Poly.denote_eq ctx (Poly.cancelAux fuel m₁ m₂ r₁ r₂) :=
  fun h => absurd (h (.leaf 0) 0 [(1, fixedVar)] [] [] []) (show ¬ (1 : Nat) = 0 by decide)

-- `Poly.of_denote_eq_cancelAux` (`h`)
example : ¬ ∀ (ctx : Context) (m₁ m₂ r₁ r₂ : Poly),
    Poly.denote_eq ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂) :=
  fun h => absurd (h (.leaf 0) [(1, fixedVar)] [] [] []) (show ¬ (1 : Nat) = 0 by decide)

-- `Poly.denote_le_cancelAux` (`h`)
example : ¬ ∀ (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly),
    Poly.denote_le ctx (Poly.cancelAux fuel m₁ m₂ r₁ r₂) :=
  fun h => absurd (h (.leaf 0) 0 [(1, fixedVar)] [] [] []) (show ¬ (1 : Nat) ≤ 0 by decide)

-- `Poly.of_denote_le_cancelAux` (`h`)
example : ¬ ∀ (ctx : Context) (m₁ m₂ r₁ r₂ : Poly),
    Poly.denote_le ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂) :=
  fun h => absurd (h (.leaf 0) [(1, fixedVar)] [] [] []) (show ¬ (1 : Nat) ≤ 0 by decide)

-- `Nat.Internal.SOM.Expr.eq_of_toPoly_eq` (`h`): `0 = 1`.
example : ¬ ∀ (ctx : Context) (a b : Nat.Internal.SOM.Expr), a.denote ctx = b.denote ctx :=
  fun h => absurd (h (.leaf 0) (.num 0) (.num 1)) (by decide)

end

#print axioms NatHand.sub_mul_div_of_le
#print axioms NatHand.div_div_div_eq_div
#print axioms NatHand.div_le_div_of_mul_le_mul
#print axioms NatHand.mul_add_mul_div_of_dvd_hba
#print axioms NatHand.mul_add_mul_div_of_dvd_hdc
#print axioms NatHand.mul_sub_mul_div_of_dvd
#print axioms NatHand.bitwise_div_two_pow
#print axioms NatHand.shiftRight_bitwise_distrib
