/-!
Hand resolution of the hypotheses in `Init.Data.UInt.Bitwise` that `HypCheck.lean` left unresolved
(cluster `UIntBitwise`, 39 hypotheses). For each hypothesis `hᵢ` of theorem `T`, this file proves
`¬T'` (necessary) or, for a dependent hypothesis, `¬∀ indep, Hᵢ`.

35 necessary, 0 removable; 4 independent (platform-dependent; listed in
`runs/hand6/UIntBitwise_independent.jsonl`, not here): `UInt32.toUSize_shiftLeft_of_lt`,
`USize.toUInt64_shiftLeft_of_lt`, `UInt64.toUSize_shiftLeft`, `USize.toUInt32_shiftLeft`, whose `T'`
holds on one platform width and fails on the other.

Counterexamples:
* `and_lt_add_one`: `c = -1`, so `c + 1 = 0` and nothing is `< 0`.
* Shift-amount bounds `b < w` (`ofFin_*`, `toFin_*`, `ofBitVec_*`, `toUIntN_shiftLeft`): `a = 1`,
  `b = w`; one side reduces the shift amount mod `w` (giving `1`), the other doesn't (giving `0`).
* `shiftLeft_add`: `b = -1`, `c = 1` (or swapped), so `b + c = 0` while `(1 <<< (w-1)) <<< 1 = 0`;
  `hbc`/`shiftLeft_add_of_toNat_lt`: `b = w - 1`, `c = 1`.
* `USize` statements: witnesses written in terms of `System.Platform.numBits`, then a case split on
  `System.Platform.numBits_eq` evaluates both platforms (no `decide` on `numBits`).

Run with the lean4 repo's stage1 binary: `lean checks/UIntBitwiseHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace UIntBitwiseHand

/-! ## Fixed widths (`UInt8` … `UInt64`, by `decide`) -/

-- `UInt8.and_lt_add_one` (`h`, idx 2): `b = 0`, `c = -1`, so `c + 1 = 0`
theorem UInt8.and_lt_add_one_h2 : ¬ ∀ {b c : UInt8}, b &&& c < c + 1 :=
  fun h => absurd (@h 0 (-1)) (by decide)

-- `UInt16.and_lt_add_one` (`h`, idx 2): `b = 0`, `c = -1`, so `c + 1 = 0`
theorem UInt16.and_lt_add_one_h2 : ¬ ∀ {b c : UInt16}, b &&& c < c + 1 :=
  fun h => absurd (@h 0 (-1)) (by decide)

-- `UInt32.and_lt_add_one` (`h`, idx 2): `b = 0`, `c = -1`, so `c + 1 = 0`
theorem UInt32.and_lt_add_one_h2 : ¬ ∀ {b c : UInt32}, b &&& c < c + 1 :=
  fun h => absurd (@h 0 (-1)) (by decide)

-- `UInt64.and_lt_add_one` (`h`, idx 2): `b = 0`, `c = -1`, so `c + 1 = 0`
theorem UInt64.and_lt_add_one_h2 : ¬ ∀ {b c : UInt64}, b &&& c < c + 1 :=
  fun h => absurd (@h 0 (-1)) (by decide)

-- `UInt8.ofFin_shiftLeft` (`hb`, idx 2): `a = 1`, `b = 8`: `0 ≠ 1 <<< (8 % 8)`
theorem UInt8.ofFin_shiftLeft_h2 : ¬ ∀ (a b : Fin UInt8.size), UInt8.ofFin (a <<< b) = UInt8.ofFin a <<< UInt8.ofFin b :=
  fun h => absurd (h 1 8) (by decide)

-- `UInt16.ofFin_shiftLeft` (`hb`, idx 2): `a = 1`, `b = 16`: `0 ≠ 1 <<< (16 % 16)`
theorem UInt16.ofFin_shiftLeft_h2 : ¬ ∀ (a b : Fin UInt16.size), UInt16.ofFin (a <<< b) = UInt16.ofFin a <<< UInt16.ofFin b :=
  fun h => absurd (h 1 16) (by decide)

-- `UInt32.ofFin_shiftLeft` (`hb`, idx 2): `a = 1`, `b = 32`: `0 ≠ 1 <<< (32 % 32)`
theorem UInt32.ofFin_shiftLeft_h2 : ¬ ∀ (a b : Fin UInt32.size), UInt32.ofFin (a <<< b) = UInt32.ofFin a <<< UInt32.ofFin b :=
  fun h => absurd (h 1 32) (by decide)

-- `UInt64.ofFin_shiftLeft` (`hb`, idx 2): `a = 1`, `b = 64`: `0 ≠ 1 <<< (64 % 64)`
theorem UInt64.ofFin_shiftLeft_h2 : ¬ ∀ (a b : Fin UInt64.size), UInt64.ofFin (a <<< b) = UInt64.ofFin a <<< UInt64.ofFin b :=
  fun h => absurd (h 1 64) (by decide)

-- `UInt8.ofFin_shiftRight` (`hb`, idx 2): `a = 1`, `b = 8`: `0 ≠ 1 >>> (8 % 8)`
theorem UInt8.ofFin_shiftRight_h2 : ¬ ∀ (a b : Fin UInt8.size), UInt8.ofFin (a >>> b) = UInt8.ofFin a >>> UInt8.ofFin b :=
  fun h => absurd (h 1 8) (by decide)

-- `UInt16.ofFin_shiftRight` (`hb`, idx 2): `a = 1`, `b = 16`: `0 ≠ 1 >>> (16 % 16)`
theorem UInt16.ofFin_shiftRight_h2 : ¬ ∀ (a b : Fin UInt16.size), UInt16.ofFin (a >>> b) = UInt16.ofFin a >>> UInt16.ofFin b :=
  fun h => absurd (h 1 16) (by decide)

-- `UInt32.ofFin_shiftRight` (`hb`, idx 2): `a = 1`, `b = 32`: `0 ≠ 1 >>> (32 % 32)`
theorem UInt32.ofFin_shiftRight_h2 : ¬ ∀ (a b : Fin UInt32.size), UInt32.ofFin (a >>> b) = UInt32.ofFin a >>> UInt32.ofFin b :=
  fun h => absurd (h 1 32) (by decide)

-- `UInt64.ofFin_shiftRight` (`hb`, idx 2): `a = 1`, `b = 64`: `0 ≠ 1 >>> (64 % 64)`
theorem UInt64.ofFin_shiftRight_h2 : ¬ ∀ (a b : Fin UInt64.size), UInt64.ofFin (a >>> b) = UInt64.ofFin a >>> UInt64.ofFin b :=
  fun h => absurd (h 1 64) (by decide)

-- `UInt8.shiftLeft_add` (`hb`, idx 3): `a = 1`, `b = 255` (= -1), `c = 1`: `b + c = 0`, `1 ≠ (1 <<< 7) <<< 1 = 0`
theorem UInt8.shiftLeft_add_h3 : ¬ ∀ {a b c : UInt8}, c < 8 → b + c < 8 → a <<< (b + c) = (a <<< b) <<< c :=
  fun h => absurd (@h 1 255 1 (by decide) (by decide)) (by decide)

-- `UInt8.shiftLeft_add` (`hc`, idx 4): `a = 1`, `b = 1`, `c = 255` (= -1): `b + c = 0`, `1 ≠ (1 <<< 1) <<< 7 = 0`
theorem UInt8.shiftLeft_add_h4 : ¬ ∀ {a b c : UInt8}, b < 8 → b + c < 8 → a <<< (b + c) = (a <<< b) <<< c :=
  fun h => absurd (@h 1 1 255 (by decide) (by decide)) (by decide)

-- `UInt16.shiftLeft_add` (`hb`, idx 3): `a = 1`, `b = 65535` (= -1), `c = 1`: `b + c = 0`, `1 ≠ (1 <<< 15) <<< 1 = 0`
theorem UInt16.shiftLeft_add_h3 : ¬ ∀ {a b c : UInt16}, c < 16 → b + c < 16 → a <<< (b + c) = (a <<< b) <<< c :=
  fun h => absurd (@h 1 65535 1 (by decide) (by decide)) (by decide)

-- `UInt16.shiftLeft_add` (`hc`, idx 4): `a = 1`, `b = 1`, `c = 65535` (= -1): `b + c = 0`, `1 ≠ (1 <<< 1) <<< 15 = 0`
theorem UInt16.shiftLeft_add_h4 : ¬ ∀ {a b c : UInt16}, b < 16 → b + c < 16 → a <<< (b + c) = (a <<< b) <<< c :=
  fun h => absurd (@h 1 1 65535 (by decide) (by decide)) (by decide)

-- `UInt32.shiftLeft_add` (`hb`, idx 3): `a = 1`, `b = 4294967295` (= -1), `c = 1`: `b + c = 0`, `1 ≠ (1 <<< 31) <<< 1 = 0`
theorem UInt32.shiftLeft_add_h3 : ¬ ∀ {a b c : UInt32}, c < 32 → b + c < 32 → a <<< (b + c) = (a <<< b) <<< c :=
  fun h => absurd (@h 1 4294967295 1 (by decide) (by decide)) (by decide)

-- `UInt32.shiftLeft_add` (`hc`, idx 4): `a = 1`, `b = 1`, `c = 4294967295` (= -1): `b + c = 0`, `1 ≠ (1 <<< 1) <<< 31 = 0`
theorem UInt32.shiftLeft_add_h4 : ¬ ∀ {a b c : UInt32}, b < 32 → b + c < 32 → a <<< (b + c) = (a <<< b) <<< c :=
  fun h => absurd (@h 1 1 4294967295 (by decide) (by decide)) (by decide)

-- `UInt64.shiftLeft_add` (`hb`, idx 3): `a = 1`, `b = 18446744073709551615` (= -1), `c = 1`: `b + c = 0`, `1 ≠ (1 <<< 63) <<< 1 = 0`
theorem UInt64.shiftLeft_add_h3 : ¬ ∀ {a b c : UInt64}, c < 64 → b + c < 64 → a <<< (b + c) = (a <<< b) <<< c :=
  fun h => absurd (@h 1 18446744073709551615 1 (by decide) (by decide)) (by decide)

-- `UInt64.shiftLeft_add` (`hc`, idx 4): `a = 1`, `b = 1`, `c = 18446744073709551615` (= -1): `b + c = 0`, `1 ≠ (1 <<< 1) <<< 63 = 0`
theorem UInt64.shiftLeft_add_h4 : ¬ ∀ {a b c : UInt64}, b < 64 → b + c < 64 → a <<< (b + c) = (a <<< b) <<< c :=
  fun h => absurd (@h 1 1 18446744073709551615 (by decide) (by decide)) (by decide)

/-! ## `USize` (platform case split on `System.Platform.numBits_eq`) -/

theorem nb_lt_size : System.Platform.numBits < USize.size := by
  rw [USize.size_eq_two_pow]; exact Nat.lt_two_pow_self

theorem one_lt_size : 1 < USize.size := by
  rw [USize.size_eq_two_pow]; exact Nat.one_lt_two_pow (Nat.ne_of_gt System.Platform.numBits_pos)

theorem fin_one_val : ((1 : Fin USize.size) : Nat) = 1 := Nat.mod_eq_of_lt one_lt_size

-- `USize.and_lt_add_one` (`h`, idx 2): `b = 0`, `c = -1`, so `c + 1 = 0`
theorem USize.and_lt_add_one_h2 : ¬ ∀ {b c : USize}, b &&& c < c + 1 :=
  fun h => absurd (@h 0 (-1)) (by simp [USize.add_left_neg])

-- `USize.ofFin_shiftLeft` (`hb`, idx 2): `a = 1`, `b = numBits`: `0 ≠ 1 <<< (numBits % numBits)`
theorem USize.ofFin_shiftLeft_h2 : ¬ ∀ (a b : Fin USize.size), USize.ofFin (a <<< b) = USize.ofFin a <<< USize.ofFin b :=
  fun h => by
    have := congrArg USize.toNat (h ⟨1, one_lt_size⟩ ⟨_, nb_lt_size⟩)
    rcases System.Platform.numBits_eq with hn | hn <;> simp [USize.toNat_shiftLeft, USize.size_eq_two_pow, hn] at this

-- `USize.ofFin_shiftRight` (`hb`, idx 2): `a = 1`, `b = numBits`: `0 ≠ 1 >>> (numBits % numBits)`
theorem USize.ofFin_shiftRight_h2 : ¬ ∀ (a b : Fin USize.size), USize.ofFin (a >>> b) = USize.ofFin a >>> USize.ofFin b :=
  fun h => by
    have := congrArg USize.toNat (h ⟨1, one_lt_size⟩ ⟨_, nb_lt_size⟩)
    rcases System.Platform.numBits_eq with hn | hn <;> simp [USize.toNat_shiftRight, USize.size_eq_two_pow, hn] at this

-- `USize.toFin_shiftLeft` (`hb`, idx 2): `a = 1`, `b = numBits`: `1 <<< 0 ≠ 1 <<< numBits % 2 ^ numBits = 0`
theorem USize.toFin_shiftLeft_h2 : ¬ ∀ (a b : USize), (a <<< b).toFin = a.toFin <<< b.toFin :=
  fun h => by
    have := congrArg Fin.val (h 1 (USize.ofNat System.Platform.numBits))
    rcases System.Platform.numBits_eq with hn | hn <;> simp [USize.toNat_shiftLeft, USize.toNat_one, fin_one_val, USize.size_eq_two_pow, hn] at this

-- `USize.toFin_shiftRight` (`hb`, idx 2): `a = 1`, `b = numBits`: `1 >>> 0 ≠ 1 >>> numBits = 0`
theorem USize.toFin_shiftRight_h2 : ¬ ∀ (a b : USize), (a >>> b).toFin = a.toFin >>> b.toFin :=
  fun h => by
    have := congrArg Fin.val (h 1 (USize.ofNat System.Platform.numBits))
    rcases System.Platform.numBits_eq with hn | hn <;> simp [USize.toNat_shiftRight, USize.toNat_one, fin_one_val, USize.size_eq_two_pow, hn] at this

-- `USize.ofBitVec_shiftLeft` (`hb`, idx 2): `a = 1`, `b = numBits`: `0 ≠ 1 <<< (numBits % numBits)`
theorem USize.ofBitVec_shiftLeft_h2 : ¬ ∀ (a : BitVec System.Platform.numBits) (b : Nat),
    USize.ofBitVec (a <<< b) = USize.ofBitVec a <<< USize.ofNat b :=
  fun h => by
    have := congrArg (fun x => x.toBitVec.toNat) (h (BitVec.ofNat _ 1) System.Platform.numBits)
    rcases System.Platform.numBits_eq with hn | hn <;> simp [USize.toBitVec_shiftLeft, hn] at this

-- `USize.ofBitVec_shiftRight` (`hb`, idx 2): `a = 1`, `b = numBits`: `0 ≠ 1 >>> (numBits % numBits)`
theorem USize.ofBitVec_shiftRight_h2 : ¬ ∀ (a : BitVec System.Platform.numBits) (b : Nat),
    USize.ofBitVec (a >>> b) = USize.ofBitVec a >>> USize.ofNat b :=
  fun h => by
    have := congrArg (fun x => x.toBitVec.toNat) (h (BitVec.ofNat _ 1) System.Platform.numBits)
    rcases System.Platform.numBits_eq with hn | hn <;> simp [USize.toBitVec_shiftRight, hn] at this

-- `USize.ofNatLT_shiftLeft` (`ha`, idx 2): dependent; `∀ a b, b < numBits → a <<< b < USize.size` fails for `a = USize.size`, `b = 0`
theorem USize.ofNatLT_shiftLeft_h2 : ¬ ∀ {a b : Nat}, b < System.Platform.numBits → a <<< b < USize.size :=
  fun h => absurd (@h USize.size 0 System.Platform.numBits_pos) (by simp)

-- `USize.ofNatLT_shiftLeft` (`hb`, idx 3): dependent; `∀ a b, a <<< b < USize.size → b < numBits` fails for `a = 0`, `b = numBits`
theorem USize.ofNatLT_shiftLeft_h3 : ¬ ∀ {a b : Nat}, a <<< b < USize.size → b < System.Platform.numBits :=
  fun h => absurd (@h 0 System.Platform.numBits (by simp [USize.size_eq_two_pow, Nat.two_pow_pos])) (Nat.lt_irrefl _)

-- `USize.toUInt8_shiftLeft` (`hb`, idx 2): `a = 1`, `b = 8`: `(1 <<< 8).toUInt8 = 0 ≠ 1 <<< (8 % 8)`
theorem USize.toUInt8_shiftLeft_h2 : ¬ ∀ (a b : USize), (a <<< b).toUInt8 = a.toUInt8 <<< b.toUInt8 :=
  fun h => by
    have := congrArg UInt8.toNat (h 1 8)
    rcases System.Platform.numBits_eq with hn | hn <;> simp [USize.toNat_shiftLeft, hn] at this

-- `USize.toUInt16_shiftLeft` (`hb`, idx 2): `a = 1`, `b = 16`: `(1 <<< 16).toUInt16 = 0 ≠ 1 <<< (16 % 16)`
theorem USize.toUInt16_shiftLeft_h2 : ¬ ∀ (a b : USize), (a <<< b).toUInt16 = a.toUInt16 <<< b.toUInt16 :=
  fun h => by
    have := congrArg UInt16.toNat (h 1 16)
    rcases System.Platform.numBits_eq with hn | hn <;> simp [USize.toNat_shiftLeft, hn] at this

-- `USize.shiftLeft_add_of_toNat_lt` (`h`, idx 3): `a = 1`, `b = numBits - 1`, `c = 1`: `1 <<< (numBits % numBits) = 1 ≠ 0`
theorem USize.shiftLeft_add_of_toNat_lt_h3 : ¬ ∀ {a b c : USize}, a <<< (b + c) = (a <<< b) <<< c :=
  fun h => by
    have := congrArg USize.toNat (@h 1 (USize.ofNat (System.Platform.numBits - 1)) 1)
    rcases System.Platform.numBits_eq with hn | hn <;> simp [USize.toNat_shiftLeft, USize.toNat_add, USize.size_eq_two_pow, hn] at this

-- `USize.shiftLeft_add` (`hb`, idx 3): `a = 1`, `b = -1`, `c = 1`: `b + c = 0`, `1 ≠ (1 <<< (numBits - 1)) <<< 1 = 0`
theorem USize.shiftLeft_add_h3 : ¬ ∀ {a b c : USize}, c < USize.ofNat System.Platform.numBits →
    b + c < USize.ofNat System.Platform.numBits → a <<< (b + c) = (a <<< b) <<< c :=
  fun h => by
    rcases System.Platform.numBits_eq with hn | hn
    all_goals
      have := congrArg USize.toNat (@h 1 (-1) 1
        (by simp [USize.lt_iff_toNat_lt, USize.size_eq_two_pow, hn]) (by simp [USize.add_left_neg, USize.lt_iff_toNat_lt, USize.size_eq_two_pow, hn]))
      simp [USize.toNat_shiftLeft, USize.add_left_neg, USize.size_eq_two_pow, hn] at this

-- `USize.shiftLeft_add` (`hc`, idx 4): `a = 1`, `b = 1`, `c = -1`: `b + c = 0`, `1 ≠ (1 <<< 1) <<< (numBits - 1) = 0`
theorem USize.shiftLeft_add_h4 : ¬ ∀ {a b c : USize}, b < USize.ofNat System.Platform.numBits →
    b + c < USize.ofNat System.Platform.numBits → a <<< (b + c) = (a <<< b) <<< c :=
  fun h => by
    rcases System.Platform.numBits_eq with hn | hn
    all_goals
      have := congrArg USize.toNat (@h 1 1 (-1)
        (by simp [USize.lt_iff_toNat_lt, USize.size_eq_two_pow, hn]) (by simp [USize.add_right_neg, USize.lt_iff_toNat_lt, USize.size_eq_two_pow, hn]))
      simp [USize.toNat_shiftLeft, USize.add_right_neg, USize.size_eq_two_pow, hn] at this

-- `USize.shiftLeft_add` (`hbc`, idx 5): `a = 1`, `b = numBits - 1`, `c = 1`: `1 <<< (numBits % numBits) = 1 ≠ 0`
theorem USize.shiftLeft_add_h5 : ¬ ∀ {a b c : USize}, b < USize.ofNat System.Platform.numBits →
    c < USize.ofNat System.Platform.numBits → a <<< (b + c) = (a <<< b) <<< c :=
  fun h => by
    rcases System.Platform.numBits_eq with hn | hn
    all_goals
      have := congrArg USize.toNat (@h 1 (USize.ofNat (System.Platform.numBits - 1)) 1
        (by simp [USize.lt_iff_toNat_lt, USize.size_eq_two_pow, hn]) (by simp [USize.lt_iff_toNat_lt, USize.size_eq_two_pow, hn]))
      simp [USize.toNat_shiftLeft, USize.toNat_add, USize.size_eq_two_pow, hn] at this

end UIntBitwiseHand
