/-!
Hand proofs for 8 verdicts (found automatically before v6) whose stored proofs failed when the
`--redo` run printed them as source (omega proof terms and proof fields printed back do not
elaborate). The witnesses are the recorded ones. All 8 are necessary.

Run with the lean4 repo's stage1 binary: `lean checks/RedoHand.lean`.
-/

-- `Int.cooper_resolution_dvd_left` (`d_pos`): `a = b = c = 1`, `d = s = p = q = 0`: the left side
-- holds at `x = 0` (`0 ∣ 0`), the right side needs `k < lcm 1 0 = 0` and `0 ≤ k`.
example : ¬ ∀ {a b c d s p q : Int}, 0 < a → 0 < b →
    ((∃ (x : Int), p ≤ a * x ∧ b * x ≤ q ∧ d ∣ c * x + s) ↔
      ∃ (k : Int), 0 ≤ k ∧ k < ↑(a.lcm (a * d / ↑((a * d).gcd c))) ∧
        b * k + b * p ≤ a * q ∧ a ∣ k + p ∧ a * d ∣ c * k + c * p + a * s) := fun h => by
  have := (@h 1 1 1 0 0 0 0 (by decide) (by decide)).mp ⟨0, by decide, by decide, by decide⟩
  obtain ⟨k, hk0, hk, -⟩ := this
  simp at hk; omega

-- `Int.cooper_resolution_dvd_right` (`d_pos`): same values.
example : ¬ ∀ {a b c d s p q : Int}, 0 < a → 0 < b →
    ((∃ (x : Int), p ≤ a * x ∧ b * x ≤ q ∧ d ∣ c * x + s) ↔
      ∃ (k : Int), 0 ≤ k ∧ k < ↑(b.lcm (b * d / ↑((b * d).gcd c))) ∧
        a * k + b * p ≤ a * q ∧ b ∣ k - q ∧ b * d ∣ -c * k + c * q + b * s) := fun h => by
  have := (@h 1 1 1 0 0 0 0 (by decide) (by decide)).mp ⟨0, by decide, by decide, by decide⟩
  obtain ⟨k, hk0, hk, -⟩ := this
  simp at hk; omega

-- `BitVec.resRec_of_clz_le` (`x.clz.toNat + y.clz.toNat ≤ w - 2`): `w = 2`, `x = y = 1#2`.
example : ¬ ∀ {w : Nat} {x y : BitVec w} (hw : 1 < w), x ≠ 0#w → y ≠ 0#w →
    x.resRec y (w - 1) (by omega) (by omega) = true := fun h =>
  absurd (@h 2 1#2 1#2 (by decide) (by decide) (by decide)) (by decide)

-- `BitVec.extractLsb_flattenList` (`w₂ : hi < w * vs.length`): `hi = lo = w = 1`, `vs = [1#1]`.
example : ¬ ∀ (hi lo : Nat) {w : Nat} (vs : List (BitVec w)) (w₁ : lo ≤ hi)
    (h : hi / w = lo / w),
    BitVec.extractLsb hi lo (BitVec.flattenList vs) =
      BitVec.cast (by
        have h1 := Nat.div_add_mod hi w; have h2 := Nat.div_add_mod lo w; rw [h] at h1; omega)
        (BitVec.extractLsb (hi % w) (lo % w) (vs[vs.length - 1 - hi / w]?.getD 0#w)) := fun h =>
  absurd (h 1 1 (w := 1) [1#1] (by decide) (by decide)) (by decide)

-- `BitVec.not_extractLsb'_append_not_extractLsb'_eq_not_extractLsb'` (`h`): `w = 1`,
-- `start₂ = start₁ = 0`, `len₁ = len₂ = 1`, `x = 1#1`.
example : ¬ ∀ {w start₂ start₁ len₁ len₂ : Nat} {x : BitVec w},
    ~~~BitVec.extractLsb' start₂ len₂ x ++ ~~~BitVec.extractLsb' start₁ len₁ x =
      BitVec.cast (by omega) (~~~BitVec.extractLsb' start₁ (len₁ + len₂) x) := fun h =>
  absurd (@h 1 0 0 1 1 1#1) (by decide)

-- `BitVec.DivModState.udiv_eq_of_lawful` (`h_final : qr.wn = 0`): `w = 1`, `n = d = 1#1`,
-- `qr = ⟨1, 0, 0#1, 0#1⟩`.
example : ¬ ∀ {w : Nat} {n d : BitVec w} {qr : BitVec.DivModState w},
    BitVec.DivModState.Lawful { n := n, d := d } qr → n / d = qr.q := fun h =>
  absurd (@h 1 1#1 1#1 ⟨1, 0, 0#1, 0#1⟩ ⟨by decide, by decide, by decide, by decide, by decide,
    by decide⟩) (by decide)

-- `Rat.mkRat_num_den` (`z : d ≠ 0`): `d = 0`, `n = n' = 0`, `d' = 1`; `mkRat 0 0 = 0`, and
-- `d = d' * m` forces `m = 0`.
example : ¬ ∀ {d : Nat} {n n' : Int} {d' : Nat} {z' : d' ≠ 0} {c : n'.natAbs.Coprime d'},
    mkRat n d = { num := n', den := d', den_nz := z', reduced := c } →
      ∃ (m : Nat), m ≠ 0 ∧ n = n' * ↑m ∧ d = d' * m := fun h => by
  obtain ⟨m, hm, -, hd⟩ := @h 0 0 0 1 (by decide) (by decide) (by simp)
  omega

-- `Rat.divInt_num_den` (`z : d ≠ 0`): same values.
example : ¬ ∀ {d n n' : Int} {d' : Nat} {z' : d' ≠ 0} {c : n'.natAbs.Coprime d'},
    Rat.divInt n d = { num := n', den := d', den_nz := z', reduced := c } →
      ∃ (m : Int), m ≠ 0 ∧ n = n' * m ∧ d = ↑d' * m := fun h => by
  obtain ⟨m, hm, -, hd⟩ := @h 0 0 0 1 (by decide) (by decide) (by simp)
  omega
