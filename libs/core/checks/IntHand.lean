/-!
Hand resolution of the 34 hypotheses in `Init.Data.Int.*` (`Cooper`, `DivMod.Lemmas`, `Lemmas`,
`Order`) that `HypCheck.lean` left unresolved. For each hypothesis `hᵢ` of theorem `T`, this file
proves either `T'` (the theorem without `hᵢ`: removable) or `¬T'` (necessary). None of them is
dependent, and none of the removable ones is derivable from the other hypotheses.

Most removable ones are `ediv` comparison lemmas with divisibility side conditions: `x / b` is
`⌊x / b⌋` for `b > 0` and `⌈x / b⌉` for `b < 0`, and for an integer `n`, `n ≤ ⌊r⌋ ↔ n ≤ r`,
`⌊r⌋ < n ↔ r < n`, `⌈r⌉ ≤ n ↔ r ≤ n`, `n < ⌈r⌉ ↔ n < r`. So a comparison of two quotients is exact
as soon as one of them is exact; only one of the two divisibility hypotheses is needed.

Run with the lean4 repo's stage1 binary: `lean checks/IntHand.lean`.
-/

/-! # Removable (23) -/

namespace IntHand

/-! ## `ediv` comparisons (12) -/

-- `Int.le_ediv_iff_of_dvd_of_pos` (`hcb`): `Int.le_ediv_iff_mul_le` needs no divisibility.
theorem le_ediv_iff_of_dvd_of_pos {a b c : Int} (hc : 0 < c) : a ≤ b / c ↔ c * a ≤ b := by
  rw [Int.le_ediv_iff_mul_le hc, Int.mul_comm]

-- `Int.ediv_lt_iff_of_dvd_of_pos` (`hba`): `Int.ediv_lt_iff_lt_mul` needs no divisibility.
theorem ediv_lt_iff_of_dvd_of_pos {a b c : Int} (hb : 0 < b) : a / b < c ↔ a < b * c := by
  rw [Int.ediv_lt_iff_lt_mul hb, Int.mul_comm]

-- `Int.ediv_le_iff_of_dvd_of_neg` (`hba`): `a / b = -(a / -b)`, reduce to
-- `le_ediv_iff_of_dvd_of_pos`.
theorem ediv_le_iff_of_dvd_of_neg {a b c : Int} (hb : b < 0) : a / b ≤ c ↔ b * c ≤ a := by
  obtain ⟨b, rfl⟩ : ∃ b', b = -b' := ⟨-b, (Int.neg_neg b).symm⟩
  have hb' : 0 < b := by omega
  have := le_ediv_iff_of_dvd_of_pos (a := -c) (b := a) hb'
  rw [Int.ediv_neg, Int.neg_mul, Int.mul_neg] at *
  omega

-- `Int.lt_ediv_iff_of_dvd_of_neg` (`hcb`): `b / c = -(b / -c)`, reduce to
-- `ediv_lt_iff_of_dvd_of_pos`.
theorem lt_ediv_iff_of_dvd_of_neg {a b c : Int} (hc : c < 0) : a < b / c ↔ b < c * a := by
  obtain ⟨c, rfl⟩ : ∃ c', c = -c' := ⟨-c, (Int.neg_neg c).symm⟩
  have hc' : 0 < c := by omega
  have := ediv_lt_iff_of_dvd_of_pos (a := b) (c := -a) hc'
  rw [Int.ediv_neg, Int.neg_mul, Int.mul_neg] at *
  omega

-- `Int.ediv_le_ediv_iff_of_dvd_of_pos_of_pos` (`hdc`): with `a = b * x`, the left side is `x`,
-- then `x ≤ c / d ↔ d * x ≤ c`; multiply by `b > 0`.
theorem ediv_le_ediv_iff_of_dvd_of_pos_of_pos {a b c d : Int} (hb : 0 < b) (hd : 0 < d)
    (hba : b ∣ a) : a / b ≤ c / d ↔ d * a ≤ c * b := by
  obtain ⟨x, rfl⟩ := hba
  rw [Int.mul_ediv_cancel_left _ (Int.ne_of_gt hb), le_ediv_iff_of_dvd_of_pos hd,
    ← Int.mul_le_mul_right hb]
  constructor <;> intro h <;> grind

-- `Int.ediv_lt_ediv_iff_of_dvd_of_pos_of_neg` (`hba`): with `c = d * y`, `a / b < y ↔ a < b * y`;
-- multiply by `d < 0`.
theorem ediv_lt_ediv_iff_of_dvd_of_pos_of_neg_hba {a b c d : Int} (hb : 0 < b) (hd : d < 0)
    (hdc : d ∣ c) : a / b < c / d ↔ c * b < d * a := by
  obtain ⟨y, rfl⟩ := hdc
  rw [Int.mul_ediv_cancel_left _ (Int.ne_of_lt hd), ediv_lt_iff_of_dvd_of_pos hb]
  have := Int.mul_lt_mul_left_of_neg hd (b := b * y) (c := a)
  constructor <;> intro h <;> grind

-- `Int.ediv_lt_ediv_iff_of_dvd_of_pos_of_neg` (`hdc`): with `a = b * x`, `x < c / d ↔ c < d * x`;
-- multiply by `b > 0`.
theorem ediv_lt_ediv_iff_of_dvd_of_pos_of_neg_hdc {a b c d : Int} (hb : 0 < b) (hd : d < 0)
    (hba : b ∣ a) : a / b < c / d ↔ c * b < d * a := by
  obtain ⟨x, rfl⟩ := hba
  rw [Int.mul_ediv_cancel_left _ (Int.ne_of_gt hb), lt_ediv_iff_of_dvd_of_neg hd]
  have := Int.mul_lt_mul_right hb (b := c) (c := d * x)
  constructor <;> intro h <;> grind

-- `Int.ediv_le_ediv_iff_of_dvd_of_neg_of_pos` (`hba`): with `c = d * y`, `a / b ≤ y ↔ b * y ≤ a`;
-- multiply by `d > 0`.
theorem ediv_le_ediv_iff_of_dvd_of_neg_of_pos_hba {a b c d : Int} (hb : b < 0) (hd : 0 < d)
    (hdc : d ∣ c) : a / b ≤ c / d ↔ c * b ≤ d * a := by
  obtain ⟨y, rfl⟩ := hdc
  rw [Int.mul_ediv_cancel_left _ (Int.ne_of_gt hd), ediv_le_iff_of_dvd_of_neg hb]
  have := Int.mul_le_mul_left hd (b := b * y) (c := a)
  constructor <;> intro h <;> grind

-- `Int.ediv_le_ediv_iff_of_dvd_of_neg_of_pos` (`hdc`): with `a = b * x`, `x ≤ c / d ↔ d * x ≤ c`;
-- multiply by `b < 0`.
theorem ediv_le_ediv_iff_of_dvd_of_neg_of_pos_hdc {a b c d : Int} (hb : b < 0) (hd : 0 < d)
    (hba : b ∣ a) : a / b ≤ c / d ↔ c * b ≤ d * a := by
  obtain ⟨x, rfl⟩ := hba
  rw [Int.mul_ediv_cancel_left _ (Int.ne_of_lt hb), le_ediv_iff_of_dvd_of_pos hd]
  have := Int.mul_le_mul_right_of_neg hb (b := c) (c := d * x)
  constructor <;> intro h <;> grind

-- `Int.ediv_le_ediv_iff_of_dvd_of_neg_of_neg` (`hba`): with `c = d * y`, `a / b ≤ y ↔ b * y ≤ a`;
-- multiply by `d < 0`.
theorem ediv_le_ediv_iff_of_dvd_of_neg_of_neg {a b c d : Int} (hb : b < 0) (hd : d < 0)
    (hdc : d ∣ c) : a / b ≤ c / d ↔ d * a ≤ c * b := by
  obtain ⟨y, rfl⟩ := hdc
  rw [Int.mul_ediv_cancel_left _ (Int.ne_of_lt hd), ediv_le_iff_of_dvd_of_neg hb]
  have := Int.mul_le_mul_left_of_neg hd (b := a) (c := b * y)
  constructor <;> intro h <;> grind

-- `Int.ediv_lt_ediv_iff_of_dvd_of_pos` (`hba`): with `c = d * y`, `a / b < y ↔ a < b * y`;
-- multiply by `d > 0`.
theorem ediv_lt_ediv_iff_of_dvd_of_pos {a b c d : Int} (hb : 0 < b) (hd : 0 < d)
    (hdc : d ∣ c) : a / b < c / d ↔ d * a < c * b := by
  obtain ⟨y, rfl⟩ := hdc
  rw [Int.mul_ediv_cancel_left _ (Int.ne_of_gt hd), ediv_lt_iff_of_dvd_of_pos hb]
  have := Int.mul_lt_mul_left hd (b := a) (c := b * y)
  constructor <;> intro h <;> grind

-- `Int.ediv_lt_ediv_iff_of_dvd_of_neg_of_neg` (`hdc`): with `a = b * x`, `x < c / d ↔ c < d * x`;
-- multiply by `b < 0`.
theorem ediv_lt_ediv_iff_of_dvd_of_neg_of_neg {a b c d : Int} (hb : b < 0) (hd : d < 0)
    (hba : b ∣ a) : a / b < c / d ↔ d * a < c * b := by
  obtain ⟨x, rfl⟩ := hba
  rw [Int.mul_ediv_cancel_left _ (Int.ne_of_lt hb), lt_ediv_iff_of_dvd_of_neg hd]
  have := Int.mul_lt_mul_right_of_neg hb (b := d * x) (c := c)
  constructor <;> intro h <;> grind

/-! ## `tdiv`, `tmod`, `fmod`, `bmod`, sign bounds (6) -/

theorem mul_tdiv_mul {k : Int} (x y : Int) (hk : k ≠ 0) : (k * x).tdiv (k * y) = x.tdiv y := by
  rcases Int.lt_or_gt_of_ne hk with hk | hk
  · obtain ⟨k, rfl⟩ : ∃ k', k = -k' := ⟨-k, (Int.neg_neg k).symm⟩
    rw [Int.neg_mul, Int.neg_mul, Int.neg_tdiv_neg, Int.mul_tdiv_mul_of_pos _ _ (by omega)]
  · exact Int.mul_tdiv_mul_of_pos _ _ hk

-- `Int.tdiv_eq_tdiv_of_mul_eq_mul` (`H2 : d ∣ c`): `a / b = c / d` as rationals, so the truncated
-- quotients agree: `a.tdiv b = (a * d).tdiv (b * d) = (b * c).tdiv (b * d) = c.tdiv d`.
theorem tdiv_eq_tdiv_of_mul_eq_mul {a b c d : Int} (H3 : b ≠ 0) (H4 : d ≠ 0)
    (H5 : a * d = b * c) : a.tdiv b = c.tdiv d := by
  rw [← mul_tdiv_mul a b H4, ← mul_tdiv_mul c d H3, Int.mul_comm d a, H5, Int.mul_comm d b]

-- `Int.mul_tmod_mul_of_pos` (`H : 0 < a`): `tmod` is odd in its first argument and even in its
-- second, so `a < 0` reduces to `-a > 0`; `a = 0` is `0 = 0`.
theorem mul_tmod_mul_of_pos {a : Int} (b c : Int) : (a * b).tmod (a * c) = a * (b.tmod c) := by
  rcases Int.lt_trichotomy a 0 with ha | rfl | ha
  · obtain ⟨a, rfl⟩ : ∃ a', a = -a' := ⟨-a, (Int.neg_neg a).symm⟩
    rw [Int.neg_mul, Int.neg_mul, Int.tmod_neg, Int.neg_tmod,
      Int.mul_tmod_mul_of_pos _ _ (by omega), Int.neg_mul]
  · simp
  · exact Int.mul_tmod_mul_of_pos _ _ ha

-- `Int.mul_fmod_mul_of_pos` (`H : 0 < a`): `(-x).fmod (-y) = -(x.fmod y)` reduces `a < 0` to
-- `-a > 0`; `a = 0` is `0 = 0`.
theorem mul_fmod_mul_of_pos {a : Int} (b c : Int) : (a * b).fmod (a * c) = a * (b.fmod c) := by
  rcases Int.lt_trichotomy a 0 with ha | rfl | ha
  · obtain ⟨a, rfl⟩ : ∃ a', a = -a' := ⟨-a, (Int.neg_neg a).symm⟩
    rw [Int.neg_mul, Int.neg_mul, Int.neg_fmod_neg,
      Int.mul_fmod_mul_of_pos _ _ (by omega), Int.neg_mul]
  · simp
  · exact Int.mul_fmod_mul_of_pos _ _ ha

-- `Int.mod_bmod_mul_of_pos` (`hce : 2 ∣ c`): with `r = b % c`, `bmod` compares `r < (c + 1) / 2`,
-- i.e. `2 * r < c`, and `2 * (a * r) < a * c` is the same condition for `a > 0`, whatever the
-- parity of `c`.
theorem mod_bmod_mul_of_pos {a : Nat} (b : Int) (c : Nat) (h : 0 < a) :
    (a * b).bmod (a * c) = a * (b.bmod c) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  have hr := Int.emod_nonneg b (b := (c : Int)) (by omega)
  have hr' := Int.emod_lt_of_pos b (b := (c : Int)) (by omega)
  have key : (a : Int) * (b % c) < ((a * c : Nat) + 1) / 2 ↔ b % c < ((c : Nat) + 1) / 2 := by
    have : 2 * ((a : Int) * (b % c)) < a * c ↔ 2 * (b % c) < c := by
      rw [← Int.mul_assoc, Int.mul_comm 2, Int.mul_assoc]
      exact Int.mul_lt_mul_left (by omega)
    push_cast
    omega
  simp only [Int.bmod, Int.natCast_mul, Int.mul_emod_mul_of_pos _ _ (by omega : (0 : Int) < a)]
  push_cast at key
  by_cases hk : b % c < ((c : Int) + 1) / 2
  · simp [hk, key.mpr hk]
  · simp [hk, mt key.mp hk, Int.mul_sub]

-- `Int.self_le_ediv_of_nonpos_of_nonneg` (`hy : 0 ≤ y`): for `y < 0`, `x / y = -(x / -y) ≥ 0 ≥ x`.
theorem self_le_ediv_of_nonpos_of_nonneg {x y : Int} (hx : x ≤ 0) : x ≤ x / y := by
  rcases Int.lt_or_le y 0 with hy | hy
  · obtain ⟨y, rfl⟩ : ∃ y', y = -y' := ⟨-y, (Int.neg_neg y).symm⟩
    rw [Int.ediv_neg]
    have : x / y ≤ 0 := Int.ediv_nonpos_of_nonpos_of_neg hx (by omega)
    omega
  · exact Int.self_le_ediv_of_nonpos_of_nonneg hx hy

-- `Int.neg_self_le_ediv_of_nonneg_of_nonpos` (`hy : y ≤ 0`): for `y > 0`, `x / y ≥ 0 ≥ -x`.
theorem neg_self_le_ediv_of_nonneg_of_nonpos (x y : Int) (hx : 0 ≤ x) : -x ≤ x / y := by
  rcases Int.lt_or_le 0 y with hy | hy
  · have : 0 ≤ x / y := Int.ediv_nonneg hx (by omega)
    omega
  · exact Int.neg_self_le_ediv_of_nonneg_of_nonpos x y hx hy

/-! ## `toNat_mul` (2) -/

-- `Int.toNat_mul` (`ha : 0 ≤ a`): for `a < 0 ≤ b`, `a * b ≤ 0`, so both sides are `0`.
theorem toNat_mul_ha {a b : Int} (hb : 0 ≤ b) : (a * b).toNat = a.toNat * b.toNat := by
  rcases Int.lt_or_le a 0 with ha | ha
  · have : a * b ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) hb
    rw [Int.toNat_of_nonpos this, Int.toNat_of_nonpos (by omega), Nat.zero_mul]
  · exact Int.toNat_mul ha hb

-- `Int.toNat_mul` (`hb : 0 ≤ b`): symmetric to `ha`.
theorem toNat_mul_hb {a b : Int} (ha : 0 ≤ a) : (a * b).toNat = a.toNat * b.toNat := by
  rw [Int.mul_comm, toNat_mul_ha ha, Nat.mul_comm]

/-! ## Cooper resolution (3) -/

namespace Cooper
open Int.Cooper

-- `Int.Cooper.resolve_left_lt_lcm` (`h₁ : p ≤ a * x`): `resolve_left` is an `emod` by
-- `L = lcm a (a * d / gcd (a * d) c)`, and `L > 0` for `a, d > 0` (obtained from the original at
-- `x = p.natAbs`, where `h₁` holds).
theorem resolve_left_lt_lcm (a c d p x : Int) (a_pos : 0 < a) (d_pos : 0 < d) :
    resolve_left a c d p x < Int.lcm a (a * d / Int.gcd (a * d) c) := by
  have hp : p ≤ a * p.natAbs := by
    have := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ a by omega)
      (Int.natCast_nonneg p.natAbs)
    rw [Int.one_mul] at this
    omega
  have h0 := le_zero_resolve_left a c d p p.natAbs hp
  have hL := Int.Cooper.resolve_left_lt_lcm a c d p p.natAbs a_pos d_pos hp
  exact Int.emod_lt_of_pos _ (by omega)

-- `Int.Cooper.resolve_left_dvd₁` (`h₁ : p ≤ a * x`): `(a * x - p) % L + p = a * x - L * q` and
-- `a ∣ L`.
theorem resolve_left_dvd₁ (a c d p x : Int) : a ∣ resolve_left a c d p x + p := by
  have h : a ∣ (Int.lcm a (a * d / Int.gcd (a * d) c) : Int) := Int.dvd_lcm_left ..
  simp only [resolve_left, Int.emod_def]
  have : a * x - p - ↑(a.lcm (a * d / ↑((a * d).gcd c))) *
      ((a * x - p) / ↑(a.lcm (a * d / ↑((a * d).gcd c)))) + p =
      a * x - ↑(a.lcm (a * d / ↑((a * d).gcd c))) *
      ((a * x - p) / ↑(a.lcm (a * d / ↑((a * d).gcd c)))) := by omega
  rw [this]
  exact Int.dvd_sub (Int.dvd_mul_right _ _) (Int.dvd_trans h (Int.dvd_mul_right _ _))

-- `Int.Cooper.resolve_left_dvd₂` (`h₁ : p ≤ a * x`): the library's proof without the
-- `resolve_left'` rewrite; `dvd_mul_emod_add_of_dvd_mul_add` holds for any `x`.
theorem resolve_left_dvd₂ {s : Int} (a c d p x : Int) (h₃ : d ∣ c * x + s) :
    a * d ∣ c * resolve_left a c d p x + c * p + a * s := by
  simp only [resolve_left, Int.add_assoc]
  apply Int.dvd_mul_emod_add_of_dvd_mul_add
  · obtain ⟨z, r⟩ := h₃
    exact ⟨z, by rw [Int.mul_assoc, ← r]; grind⟩
  · exact Int.dvd_lcm_right ..

end Cooper

end IntHand

/-! # Necessary (11) -/

section
open Int.Cooper

-- `Int.Cooper.resolve_left_ineq` (`b_pos`): `b = -1`, `q = 0`, `a = 1`, `c = 0`, `d = 1`,
-- `p = -5`, `x = 0`: `resolve_left = 5 % 1 = 0`, and `0 + 5 ≤ 0` fails.
example : ¬ ∀ {b q : Int} (a c d p x : Int), 0 < a → p ≤ a * x → b * x ≤ q →
    b * resolve_left a c d p x + b * p ≤ a * q := fun h =>
  absurd (@h (-1) 0 1 0 1 (-5) 0 (by decide) (by decide) (by decide)) (by decide)

-- `Int.Cooper.mul_resolve_left_inv_le` (`h₄ : a ∣ k + p`): `b = -2`, `q = 1`, `a = 2`, `p = 0`,
-- `k = -1`: `2 ≤ 2`, but `-2 * ((-1) / 2) = 2 ≤ 1` fails.
example : ¬ ∀ {b q : Int} (a p k : Int), 0 < a → b * k + b * p ≤ a * q →
    b * resolve_left_inv a p k ≤ q := fun h =>
  absurd (@h (-2) 1 2 0 (-1) (by decide) (by decide)) (by decide)

-- `Int.Cooper.resolve_left_inv_dvd` (`h₄ : a ∣ k + p`): `s = 1`, `a = c = d = 2`, `p = 0`,
-- `k = 1`: `4 ∣ 4`, but `2 ∣ 2 * (1 / 2) + 1 = 1` fails.
example : ¬ ∀ {s : Int} (a c d p k : Int), 0 < a → a * d ∣ c * k + c * p + a * s →
    d ∣ c * resolve_left_inv a p k + s := fun h =>
  absurd (@h 1 2 2 2 0 1 (by decide) (by decide)) (by decide)

-- `Int.cooper_resolution_dvd_left` (`a_pos`): `a = 0`, `b = d = 1`, rest `0`: `x = 0` solves the
-- left side, but `lcm 0 _ = 0` leaves no `k` with `0 ≤ k < 0`.
example : ¬ ∀ {a b c d s p q : Int}, 0 < b → 0 < d →
    ((∃ x, p ≤ a * x ∧ b * x ≤ q ∧ d ∣ c * x + s) ↔
      ∃ k, 0 ≤ k ∧ k < ↑(a.lcm (a * d / ↑((a * d).gcd c))) ∧
        b * k + b * p ≤ a * q ∧ a ∣ k + p ∧ a * d ∣ c * k + c * p + a * s) := fun h => by
  obtain ⟨k, hk0, hk1, -⟩ := (@h 0 1 0 1 0 0 0 (by decide) (by decide)).mp
    ⟨0, by decide, by decide, by decide⟩
  simp at hk1
  omega

-- `Int.cooper_resolution_dvd_left` (`b_pos`): `a = d = 1`, `b = -1`, `c = s = q = 0`, `p = -5`:
-- `x = 0` solves the left side; the right side forces `k = 0` (`lcm 1 1 = 1`) and `5 ≤ 0`.
example : ¬ ∀ {a b c d s p q : Int}, 0 < a → 0 < d →
    ((∃ x, p ≤ a * x ∧ b * x ≤ q ∧ d ∣ c * x + s) ↔
      ∃ k, 0 ≤ k ∧ k < ↑(a.lcm (a * d / ↑((a * d).gcd c))) ∧
        b * k + b * p ≤ a * q ∧ a ∣ k + p ∧ a * d ∣ c * k + c * p + a * s) := fun h => by
  obtain ⟨k, hk0, hk1, hk2, -⟩ := (@h 1 (-1) 0 1 0 (-5) 0 (by decide) (by decide)).mp
    ⟨0, by decide, by decide, by decide⟩
  simp at hk1
  omega

-- `Int.cooper_resolution_dvd_right` (`a_pos`): `a = -1`, `b = d = 1`, `c = s = q = 0`, `p = 1`:
-- `x = -1` solves the left side; the right side forces `k = 0` and `1 ≤ 0`.
example : ¬ ∀ {a b c d s p q : Int}, 0 < b → 0 < d →
    ((∃ x, p ≤ a * x ∧ b * x ≤ q ∧ d ∣ c * x + s) ↔
      ∃ k, 0 ≤ k ∧ k < ↑(b.lcm (b * d / ↑((b * d).gcd c))) ∧
        a * k + b * p ≤ a * q ∧ b ∣ k - q ∧ b * d ∣ -c * k + c * q + b * s) := fun h => by
  obtain ⟨k, hk0, hk1, hk2, -⟩ := (@h (-1) 1 0 1 0 1 0 (by decide) (by decide)).mp
    ⟨-1, by decide, by decide, by decide⟩
  simp at hk1
  omega

-- `Int.cooper_resolution_dvd_right` (`b_pos`): `b = 0`, `a = d = 1`, rest `0`: `x = 0` solves the
-- left side, but `lcm 0 _ = 0` leaves no `k`.
example : ¬ ∀ {a b c d s p q : Int}, 0 < a → 0 < d →
    ((∃ x, p ≤ a * x ∧ b * x ≤ q ∧ d ∣ c * x + s) ↔
      ∃ k, 0 ≤ k ∧ k < ↑(b.lcm (b * d / ↑((b * d).gcd c))) ∧
        a * k + b * p ≤ a * q ∧ b ∣ k - q ∧ b * d ∣ -c * k + c * q + b * s) := fun h => by
  obtain ⟨k, hk0, hk1, -⟩ := (@h 1 0 0 1 0 0 0 (by decide) (by decide)).mp
    ⟨0, by decide, by decide, by decide⟩
  simp at hk1
  omega

end

-- `Int.subNatNat_elim` (`hp`): `motive _ _ z := z < 0` (true at every `negSucc`), `m = n = 0`.
example : ¬ ∀ (m n : Nat) (motive : Nat → Nat → Int → Prop),
    (∀ (i m : Nat), motive m (m + i + 1) (Int.negSucc i)) → motive m n (Int.subNatNat m n) :=
  fun h => absurd (h 0 0 (fun _ _ z => z < 0) (fun _ _ => Int.negSucc_lt_zero _)) (by decide)

-- `Int.subNatNat_elim` (`hn`): `motive _ _ z := 0 ≤ z`, `m = 0`, `n = 1`.
example : ¬ ∀ (m n : Nat) (motive : Nat → Nat → Int → Prop),
    (∀ (i n : Nat), motive (n + i) n ↑i) → motive m n (Int.subNatNat m n) :=
  fun h => absurd (h 0 1 (fun _ _ z => 0 ≤ z) (fun _ _ => Int.natCast_nonneg _)) (by decide)

-- `Int.wlog_sign` (`inv`): `P := (0 ≤ ·)`, `i = -1`.
example : ¬ ∀ {P : Int → Prop}, (∀ (n : Nat), P ↑n) → ∀ (i : Int), P i :=
  fun h => absurd (@h (0 ≤ ·) (fun n => Int.natCast_nonneg n) (-1)) (by decide)

-- `Int.wlog_sign` (`w`): `P := fun _ => False`, `i = 0`.
example : ¬ ∀ {P : Int → Prop}, (∀ (i : Int), P i ↔ P (-i)) → ∀ (i : Int), P i :=
  fun h => @h (fun _ => False) (fun _ => Iff.rfl) 0

/-! # Consistency: each removable restatement implies the original theorem -/

example : type_of% @Int.le_ediv_iff_of_dvd_of_pos := fun hc _ =>
  IntHand.le_ediv_iff_of_dvd_of_pos hc
example : type_of% @Int.ediv_lt_iff_of_dvd_of_pos := fun hb _ =>
  IntHand.ediv_lt_iff_of_dvd_of_pos hb
example : type_of% @Int.ediv_le_iff_of_dvd_of_neg := fun hb _ =>
  IntHand.ediv_le_iff_of_dvd_of_neg hb
example : type_of% @Int.lt_ediv_iff_of_dvd_of_neg := fun hc _ =>
  IntHand.lt_ediv_iff_of_dvd_of_neg hc
example : type_of% @Int.ediv_le_ediv_iff_of_dvd_of_pos_of_pos := fun hb hd hba _ =>
  IntHand.ediv_le_ediv_iff_of_dvd_of_pos_of_pos hb hd hba
example : type_of% @Int.ediv_lt_ediv_iff_of_dvd_of_pos_of_neg := fun hb hd _ hdc =>
  IntHand.ediv_lt_ediv_iff_of_dvd_of_pos_of_neg_hba hb hd hdc
example : type_of% @Int.ediv_lt_ediv_iff_of_dvd_of_pos_of_neg := fun hb hd hba _ =>
  IntHand.ediv_lt_ediv_iff_of_dvd_of_pos_of_neg_hdc hb hd hba
example : type_of% @Int.ediv_le_ediv_iff_of_dvd_of_neg_of_pos := fun hb hd _ hdc =>
  IntHand.ediv_le_ediv_iff_of_dvd_of_neg_of_pos_hba hb hd hdc
example : type_of% @Int.ediv_le_ediv_iff_of_dvd_of_neg_of_pos := fun hb hd hba _ =>
  IntHand.ediv_le_ediv_iff_of_dvd_of_neg_of_pos_hdc hb hd hba
example : type_of% @Int.ediv_le_ediv_iff_of_dvd_of_neg_of_neg := fun hb hd _ hdc =>
  IntHand.ediv_le_ediv_iff_of_dvd_of_neg_of_neg hb hd hdc
example : type_of% @Int.ediv_lt_ediv_iff_of_dvd_of_pos := fun hb hd _ hdc =>
  IntHand.ediv_lt_ediv_iff_of_dvd_of_pos hb hd hdc
example : type_of% @Int.ediv_lt_ediv_iff_of_dvd_of_neg_of_neg := fun hb hd hba _ =>
  IntHand.ediv_lt_ediv_iff_of_dvd_of_neg_of_neg hb hd hba
example : type_of% @Int.tdiv_eq_tdiv_of_mul_eq_mul := fun _ H3 H4 H5 =>
  IntHand.tdiv_eq_tdiv_of_mul_eq_mul H3 H4 H5
example : type_of% @Int.mul_tmod_mul_of_pos := fun b c _ => IntHand.mul_tmod_mul_of_pos b c
example : type_of% @Int.mul_fmod_mul_of_pos := fun b c _ => IntHand.mul_fmod_mul_of_pos b c
example : type_of% @Int.mod_bmod_mul_of_pos := fun b c h _ => IntHand.mod_bmod_mul_of_pos b c h
example : type_of% @Int.self_le_ediv_of_nonpos_of_nonneg := fun hx _ =>
  IntHand.self_le_ediv_of_nonpos_of_nonneg hx
example : type_of% @Int.neg_self_le_ediv_of_nonneg_of_nonpos := fun x y hx _ =>
  IntHand.neg_self_le_ediv_of_nonneg_of_nonpos x y hx
example : type_of% @Int.toNat_mul := fun _ hb => IntHand.toNat_mul_ha hb
example : type_of% @Int.toNat_mul := fun ha _ => IntHand.toNat_mul_hb ha
example : type_of% @Int.Cooper.resolve_left_lt_lcm := fun a c d p x ha hd _ =>
  IntHand.Cooper.resolve_left_lt_lcm a c d p x ha hd
example : type_of% @Int.Cooper.resolve_left_dvd₁ := fun a c d p x _ =>
  IntHand.Cooper.resolve_left_dvd₁ a c d p x
example : type_of% @Int.Cooper.resolve_left_dvd₂ := fun a c d p x _ h₃ =>
  IntHand.Cooper.resolve_left_dvd₂ a c d p x h₃

#print axioms IntHand.le_ediv_iff_of_dvd_of_pos
#print axioms IntHand.ediv_lt_iff_of_dvd_of_pos
#print axioms IntHand.ediv_le_iff_of_dvd_of_neg
#print axioms IntHand.lt_ediv_iff_of_dvd_of_neg
#print axioms IntHand.ediv_le_ediv_iff_of_dvd_of_pos_of_pos
#print axioms IntHand.ediv_lt_ediv_iff_of_dvd_of_pos_of_neg_hba
#print axioms IntHand.ediv_lt_ediv_iff_of_dvd_of_pos_of_neg_hdc
#print axioms IntHand.ediv_le_ediv_iff_of_dvd_of_neg_of_pos_hba
#print axioms IntHand.ediv_le_ediv_iff_of_dvd_of_neg_of_pos_hdc
#print axioms IntHand.ediv_le_ediv_iff_of_dvd_of_neg_of_neg
#print axioms IntHand.ediv_lt_ediv_iff_of_dvd_of_pos
#print axioms IntHand.ediv_lt_ediv_iff_of_dvd_of_neg_of_neg
#print axioms IntHand.tdiv_eq_tdiv_of_mul_eq_mul
#print axioms IntHand.mul_tmod_mul_of_pos
#print axioms IntHand.mul_fmod_mul_of_pos
#print axioms IntHand.mod_bmod_mul_of_pos
#print axioms IntHand.self_le_ediv_of_nonpos_of_nonneg
#print axioms IntHand.neg_self_le_ediv_of_nonneg_of_nonpos
#print axioms IntHand.toNat_mul_ha
#print axioms IntHand.toNat_mul_hb
#print axioms IntHand.Cooper.resolve_left_lt_lcm
#print axioms IntHand.Cooper.resolve_left_dvd₁
#print axioms IntHand.Cooper.resolve_left_dvd₂
