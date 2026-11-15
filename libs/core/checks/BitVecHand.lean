/-!
Hand resolution of the 34 hypotheses in `Init.Data.BitVec.*` (`Bitblast`, `Lemmas`, `Bootstrap`,
`Folds`) that `HypCheck.lean` left unresolved. For each hypothesis `hᵢ` of theorem `T`, this file
proves either `T'` (the theorem without `hᵢ`: removable) or `¬T'` (necessary). For the dependent
hypothesis (`getElem_eq_true_of_lt_of_le`, `hk'`) removability means proving it from the
independent parameters (see `Methods.md`). Universe-polymorphic theorems are refuted at universe 0.
For theorems with two removable hypotheses, each was removed separately.

Run with the lean4 repo's stage1 binary: `lean checks/BitVecHand.lean`.
-/

namespace BitVecHand
open BitVec

/-! ## Removable (23) -/

-- `BitVec.resRec_of_clz_le` (`hx`): `clz 0 = w`, so for `x = 0` the premise `w + clz y ≤ w - 2` is false.
theorem resRec_of_clz_le_hx {w : Nat} {x y : BitVec w} (hw : 1 < w) (hy : y ≠ 0#w) :
    x.clz.toNat + y.clz.toNat ≤ w - 2 → x.resRec y (w - 1) (by omega) (by omega) = true := by
  intro h
  by_cases hx : x = 0#w
  · subst hx; simp [toNat_clz] at h; omega
  · exact BitVec.resRec_of_clz_le hw hx hy h

-- `BitVec.resRec_of_clz_le` (`hy`): symmetric, `clz 0 = w` makes the premise false.
theorem resRec_of_clz_le_hy {w : Nat} {x y : BitVec w} (hw : 1 < w) (hx : x ≠ 0#w) :
    x.clz.toNat + y.clz.toNat ≤ w - 2 → x.resRec y (w - 1) (by omega) (by omega) = true := by
  intro h
  by_cases hy : y = 0#w
  · subst hy; simp [toNat_clz] at h; omega
  · exact BitVec.resRec_of_clz_le hw hx hy h

-- `BitVec.msb_neg_umod_neg_of_msb_true_of_msb_true` (`hx`): `(a % -y).toNat < (-y).toNat ≤ 2^(w-1)`
-- for every `a` once `y.msb` (so `y ≠ 0`); `x` plays no role.
theorem msb_neg_umod_neg {w : Nat} {x y : BitVec w} (hy : y.msb = true) :
    (-x % -y).msb = false := by
  have h1 := toNat_neg_lt_of_msb y hy
  have h2 : (-y).toNat ≠ 0 := by
    intro h0
    have : -y = 0#w := eq_of_toNat_eq (by simpa using h0)
    have : y = 0#w := by rw [← BitVec.neg_neg (x := y), this]; simp
    subst this; simp at hy
  have h3 : (-x % -y).toNat < (-y).toNat := by
    rw [toNat_umod]; exact Nat.mod_lt _ (by omega)
  rw [msb_eq_decide, decide_eq_false_iff_not]; omega

-- Helper: `-(-z).toInt = z.toNat` whenever `z.toNat ≤ 2^(w-1)` (this includes `z = intMin`).
theorem neg_toInt_neg_of_toNat_le {w : Nat} {z : BitVec w} (hz : z.toNat ≤ 2 ^ (w - 1)) :
    -(-z).toInt = z.toNat := by
  rcases w with _ | w
  · simp [of_length_zero]
  by_cases h0 : z = 0#(w+1)
  · subst h0; simp
  have hpos : 0 < z.toNat := toNat_pos_of_ne_zero h0
  have hlt := z.isLt
  have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ]; omega
  simp only [Nat.add_sub_cancel] at hz
  rw [toInt_eq_msb_cond, msb_eq_decide, toNat_neg, Nat.mod_eq_of_lt (by omega)]
  simp only [Nat.add_sub_cancel]
  rw [ite_eq_left (by simp; omega)]
  omega

-- `BitVec.neg_toInt_neg_umod_eq_of_msb_true_msb_true` (`hx`): `(-x % -y).toNat < (-y).toNat ≤ 2^(w-1)`.
theorem neg_toInt_neg_umod_hx {w : Nat} {x y : BitVec w} (hy : y.msb = true) :
    -(-(-x % -y)).toInt = (-x % -y).toNat := by
  apply neg_toInt_neg_of_toNat_le
  have h1 := toNat_neg_lt_of_msb y hy
  have h2 : (-y).toNat ≠ 0 := by
    intro h0
    have : -y = 0#w := eq_of_toNat_eq (by simpa using h0)
    have : y = 0#w := by rw [← BitVec.neg_neg (x := y), this]; simp
    subst this; simp at hy
  have h3 : (-x % -y).toNat < (-y).toNat := by
    rw [toNat_umod]; exact Nat.mod_lt _ (by omega)
  omega

-- `BitVec.neg_toInt_neg_umod_eq_of_msb_true_msb_true` (`hy`): `(-x % -y).toNat ≤ (-x).toNat ≤ 2^(w-1)`.
theorem neg_toInt_neg_umod_hy {w : Nat} {x y : BitVec w} (hx : x.msb = true) :
    -(-(-x % -y)).toInt = (-x % -y).toNat := by
  apply neg_toInt_neg_of_toNat_le
  have h1 := toNat_neg_lt_of_msb x hx
  have h3 : (-x % -y).toNat ≤ (-x).toNat := by
    rw [toNat_umod]; exact Nat.mod_le _ _
  omega

-- `BitVec.toInt_signExtend_eq_toInt_bmod_of_le` (`h`): for `w < v` both sides are `x.toInt`,
-- since `-2^(w-1) ≤ x.toInt < 2^(w-1)` lies in the `bmod (2^v)` range.
theorem toInt_signExtend_eq_toInt_bmod {w v : Nat} (x : BitVec w) :
    (BitVec.signExtend v x).toInt = x.toInt.bmod (2 ^ v) := by
  by_cases h : v ≤ w
  · exact BitVec.toInt_signExtend_eq_toInt_bmod_of_le x h
  rw [BitVec.toInt_signExtend, Nat.min_eq_right (by omega), toInt_bmod_cancel]
  have h1 := le_two_mul_toInt (x := x)
  have h2 := two_mul_toInt_lt (x := x)
  have hp : (2 : Int) ^ v = 2 ^ (v - 1) * 2 := by
    rw [← Int.pow_succ]; congr 1; omega
  have hw' : 2 ^ w ≤ 2 ^ (v - 1) := Nat.pow_le_pow_of_le (by decide) (by omega)
  have hw : (2 : Int) ^ w ≤ 2 ^ (v - 1) := by exact_mod_cast hw'
  symm; apply Int.bmod_eq_of_le
  · push_cast; rw [hp, Int.mul_ediv_cancel _ (by decide)]; omega
  · push_cast; rw [hp]
    have : (2 ^ (v - 1) * 2 + 1 : Int) / 2 = 2 ^ (v - 1) := by omega
    omega

-- `BitVec.le_toNat_iff_getLsbD_eq_true` (`hi`): for `w ≤ i` both sides are false.
theorem le_toNat_iff_getLsbD_eq_true {w i : Nat} {x : BitVec w} :
    (2 ^ i ≤ x.toNat ↔ ∃ k, x.getLsbD (i + k) = true) := by
  by_cases hi : i < w
  · exact BitVec.le_toNat_iff_getLsbD_eq_true hi
  have : 2 ^ w ≤ 2 ^ i := Nat.pow_le_pow_of_le (by decide) (by omega)
  have := x.isLt
  constructor
  · intro h; omega
  · rintro ⟨k, hk⟩; rw [getLsbD_of_ge x _ (by omega)] at hk; simp at hk

-- `BitVec.toNat_lt_iff_getLsbD_eq_false` (`hi`): for `w ≤ i` both sides are true.
theorem toNat_lt_iff_getLsbD_eq_false {w : Nat} {x : BitVec w} (i : Nat) :
    (x.toNat < 2 ^ i ↔ ∀ (k : Nat), x.getLsbD (i + k) = false) := by
  by_cases hi : i < w
  · exact BitVec.toNat_lt_iff_getLsbD_eq_false i hi
  have : 2 ^ w ≤ 2 ^ i := Nat.pow_le_pow_of_le (by decide) (by omega)
  have := x.isLt
  exact ⟨fun _ k => getLsbD_of_ge x _ (by omega), fun _ => by omega⟩

-- `BitVec.toInt_ediv_toInt_lt_of_nonpos_of_lt_neg_one` (`hx`): for `0 < x.toInt`, `y.toInt < 0`
-- gives `x.toInt / y.toInt ≤ 0 < 2^(w-1)`.
theorem toInt_ediv_toInt_lt_of_lt_neg_one {w : Nat} {x y : BitVec w} (hy : y.toInt < -1) :
    x.toInt / y.toInt < 2 ^ (w - 1) := by
  by_cases hx : x.toInt ≤ 0
  · exact BitVec.toInt_ediv_toInt_lt_of_nonpos_of_lt_neg_one hx hy
  have := Int.ediv_nonpos_of_nonneg_of_nonpos (a := x.toInt) (b := y.toInt) (by omega) (by omega)
  have : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by decide)
  omega

-- `BitVec.toInt_ediv_toInt_lt_of_nonneg_of_nonneg` (`hx`): for `x.toInt < 0 ≤ y.toInt` the quotient is `≤ 0`.
theorem toInt_ediv_toInt_lt_of_nonneg_hx {w : Nat} {x y : BitVec w} (hy : 0 ≤ y.toInt) :
    x.toInt / y.toInt < 2 ^ (w - 1) := by
  by_cases hx : 0 ≤ x.toInt
  · exact BitVec.toInt_ediv_toInt_lt_of_nonneg_of_nonneg hx hy
  have : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by decide)
  rcases Int.lt_or_eq_of_le hy with hy | hy
  · have := Int.ediv_neg_of_neg_of_pos (a := x.toInt) (b := y.toInt) (by omega) hy
    omega
  · rw [← hy, Int.ediv_zero]; omega

-- `BitVec.toInt_ediv_toInt_lt_of_nonneg_of_nonneg` (`hy`): for `0 ≤ x.toInt`, `y.toInt < 0` the quotient is `≤ 0`.
theorem toInt_ediv_toInt_lt_of_nonneg_hy {w : Nat} {x y : BitVec w} (hx : 0 ≤ x.toInt) :
    x.toInt / y.toInt < 2 ^ (w - 1) := by
  by_cases hy : 0 ≤ y.toInt
  · exact BitVec.toInt_ediv_toInt_lt_of_nonneg_of_nonneg hx hy
  have := Int.ediv_nonpos_of_nonneg_of_nonpos (a := x.toInt) (b := y.toInt) hx (by omega)
  have : (0 : Int) < 2 ^ (w - 1) := Int.pow_pos (by decide)
  omega

-- `BitVec.toNat_cpop_setWidth_le_of_le` (`h`): for `w ≤ n` the popcount is unchanged
-- (`toNat_cpop_setWidth_eq_of_le`).
theorem toNat_cpop_setWidth_le {w : Nat} {x : BitVec w} {n : Nat} :
    (BitVec.setWidth n x).cpop.toNat ≤ x.cpop.toNat := by
  by_cases h : n ≤ w
  · exact BitVec.toNat_cpop_setWidth_le_of_le h
  · exact Nat.le_of_eq (BitVec.toNat_cpop_setWidth_eq_of_le (by omega))

-- `BitVec.toInt_umod_neg_add` (`hdvd`): if `y.toInt ∣ x.toInt` then `x % -y = 0` and
-- `x.toInt % y.toInt = 0`, so both sides are `y.toInt`.
theorem toInt_umod_neg_add {w : Nat} {x y : BitVec w} (hymsb : y.msb = true) (hxmsb : x.msb = false) :
    (x % -y + y).toInt = x.toInt % y.toInt + y.toInt := by
  by_cases hdvd : y.toInt ∣ x.toInt
  · rw [(toInt_dvd_toInt_iff_of_msb_false_msb_true hxmsb hymsb).mp hdvd, Int.emod_eq_zero_of_dvd hdvd]
    simp
  · exact BitVec.toInt_umod_neg_add hymsb hxmsb hdvd

-- `BitVec.getMsbD_add` (`i_lt`): for `w ≤ i` all `getMsbD` are false and `carry 0 _ _ false = false`.
theorem getMsbD_add {w i : Nat} {x y : BitVec w} :
    (x + y).getMsbD i = (x.getMsbD i ^^ (y.getMsbD i ^^ BitVec.carry (w - 1 - i) x y false)) := by
  by_cases h : i < w
  · exact BitVec.getMsbD_add (i_lt := h)
  · have hge : w ≤ i := by omega
    rw [show w - 1 - i = 0 by omega]; simp [getMsbD_of_ge, hge]

-- `BitVec.getMsbD_sub` (`i_lt`): as for `getMsbD_add`.
theorem getMsbD_sub {w i : Nat} {x y : BitVec w} :
    (x - y).getMsbD i = (x.getMsbD i ^^ ((~~~y + 1).getMsbD i ^^ BitVec.carry (w - 1 - i) x (~~~y + 1) false)) := by
  by_cases h : i < w
  · exact BitVec.getMsbD_sub (i_lt := h)
  · have hge : w ≤ i := by omega
    rw [show w - 1 - i = 0 by omega]; simp [getMsbD_of_ge, hge]

-- `BitVec.udiv_twoPow_eq_of_lt` (`hk`): for `w ≤ k`, `twoPow w k = 0`, `x / 0 = 0 = x >>> k`.
theorem udiv_twoPow_eq {w : Nat} {x : BitVec w} {k : Nat} : x / BitVec.twoPow w k = x >>> k := by
  by_cases hk : k < w
  · exact BitVec.udiv_twoPow_eq_of_lt hk
  have : BitVec.twoPow w k = 0#w := eq_of_toNat_eq (by simp [toNat_twoPow_of_le (show w ≤ k by omega)])
  rw [this, udiv_zero, ushiftRight_eq_zero (by omega)]

-- `BitVec.clzAuxRec_eq_iff_of_getLsbD_false` (`h`): `clzAuxRec x n` only inspects bits `≤ n`;
-- direct induction on `n` (a set bit `j ≤ n` gives `w - 1 - j ≠ w`).
theorem clzAuxRec_eq_iff {w n : Nat} {x : BitVec w} :
    (x.clzAuxRec n = BitVec.ofNat w w ↔ ∀ (j : Nat), j ≤ n → x.getLsbD j = false) := by
  have hw : w < 2 ^ w := Nat.lt_two_pow_self
  induction n with
  | zero =>
    by_cases h0 : x.getLsbD 0
    · have : 0 < w := by
        rcases Nat.eq_zero_or_pos w with rfl | h
        · simp at h0
        · exact h
      simp only [clzAuxRec, h0, ite_true]
      constructor
      · intro h; have := congrArg BitVec.toNat h; simp at this
        rw [Nat.mod_eq_of_lt (by omega)] at this; omega
      · intro h; simp [h 0 (Nat.le_refl 0)] at h0
    · simp only [clzAuxRec, h0]
      simp only [Bool.false_eq_true, ite_false, true_iff]
      intro j hj; rw [show j = 0 by omega]; simpa using h0
  | succ n ih =>
    by_cases h1 : x.getLsbD (n + 1)
    · have : n + 1 < w := by
        false_or_by_contra
        rw [getLsbD_of_ge x _ (by omega)] at h1; simp at h1
      simp only [clzAuxRec, h1, ite_true]
      constructor
      · intro h; have := congrArg BitVec.toNat h; simp at this
        rw [Nat.mod_eq_of_lt (by omega)] at this; omega
      · intro h; simp [h (n + 1) (Nat.le_refl _)] at h1
    · simp only [clzAuxRec, h1, Bool.false_eq_true, ite_false, ih]
      constructor
      · intro h j hj
        rcases Nat.lt_or_eq_of_le hj with hj | rfl
        · exact h j (by omega)
        · simpa using h1
      · intro h j hj; exact h j (by omega)

-- `BitVec.carry_succ_one` (`h`): for `w = 0` both sides are false (bit 0 of `x : BitVec 0` is false).
theorem carry_succ_one {w : Nat} (i : Nat) (x : BitVec w) :
    BitVec.carry (i + 1) x (1#w) false = decide (∀ (j : Nat), j ≤ i → x.getLsbD j = true) := by
  rcases Nat.eq_zero_or_pos w with rfl | h
  · simp [carry, of_length_zero]
    exact ⟨0, Nat.zero_le _⟩
  · exact BitVec.carry_succ_one i x h

-- `BitVec.toNat_ushiftRight_lt` (`hn`): for `w < n`, `x >>> n = 0 < 1 = 2^(w-n)`.
theorem toNat_ushiftRight_lt {w : Nat} (x : BitVec w) (n : Nat) : (x >>> n).toNat < 2 ^ (w - n) := by
  by_cases hn : n ≤ w
  · exact BitVec.toNat_ushiftRight_lt x n hn
  · rw [ushiftRight_eq_zero (by omega)]; simp [Nat.two_pow_pos]

-- `BitVec.ofNat_sub_ofNat_of_le` (`hy`): `ofNat x = ofNat (x - y) + ofNat y` for `y ≤ x`, any `y`.
theorem ofNat_sub_ofNat_of_le {w : Nat} (x y : Nat) (hlt : y ≤ x) :
    BitVec.ofNat w x - BitVec.ofNat w y = BitVec.ofNat w (x - y) := by
  conv => lhs; rw [show x = (x - y) + y by omega, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

-- `BitVec.getElem_eq_true_of_lt_of_le` (`hk'`, dependent): `2^k ≤ x.toNat < 2^w` forces `k < w`.
theorem getElem_eq_true_of_lt_of_le.der {w k : Nat} {x : BitVec w}
    (_hlt : x.toNat < 2 ^ (k + 1)) (hle : 2 ^ k ≤ x.toNat) : k < w := by
  have := x.isLt
  false_or_by_contra
  have : 2 ^ w ≤ 2 ^ k := Nat.pow_le_pow_of_le (by decide) (by omega)
  omega

theorem getElem_eq_true_of_lt_of_le {w k : Nat} {x : BitVec w}
    (hlt : x.toNat < 2 ^ (k + 1)) (hle : 2 ^ k ≤ x.toNat) :
    x[k]'(getElem_eq_true_of_lt_of_le.der hlt hle) = true :=
  BitVec.getElem_eq_true_of_lt_of_le _ hlt hle

-- `BitVec.toNat_shiftConcat_lt_of_lt` (`hk`): for `w ≤ k`, the result is `< 2^w ≤ 2^(k+1)`.
theorem toNat_shiftConcat_lt_of_lt {w : Nat} {x : BitVec w} {b : Bool} {k : Nat} (hx : x.toNat < 2 ^ k) :
    (x.shiftConcat b).toNat < 2 ^ (k + 1) := by
  by_cases hk : k < w
  · exact BitVec.toNat_shiftConcat_lt_of_lt hk hx
  have h1 := (x.shiftConcat b).isLt
  have : 2 ^ w ≤ 2 ^ (k + 1) := Nat.pow_le_pow_of_le (by decide) (by omega)
  omega

-- `BitVec.umod_eq_divRec` (`hd`): for `d = 0` no step subtracts, so `divRec` shifts all bits of `n`
-- into `r` and returns `r = n = n % 0`. Helpers first.
theorem mod_mul_add_mod (a c e N : Nat) : (a % N * c + e) % N = (a * c + e) % N := by
  conv => rhs; rw [← Nat.mod_add_div a N]
  rw [Nat.add_mul, Nat.add_right_comm, Nat.mul_assoc, Nat.add_mul_mod_self_left]

theorem divRec_zero_r (n : BitVec w) : ∀ (m : Nat) (qr : DivModState w), qr.wn = m →
    (divRec m {n := n, d := 0#w} qr).r.toNat = (qr.r.toNat * 2 ^ m + n.toNat % 2 ^ m) % 2 ^ w := by
  intro m
  induction m with
  | zero => intro qr _; simp [Nat.mod_one, Nat.mod_eq_of_lt qr.r.isLt]
  | succ m ih =>
    intro qr hm
    rw [divRec_succ, ih]
    · have hr : (divSubtractShift {n := n, d := 0#w} qr).r = qr.r.shiftConcat (n.getLsbD m) := by
        simp [divSubtractShift, hm]
      rw [hr, toNat_shiftConcat, Nat.shiftLeft_eq, Nat.pow_one, mod_mul_add_mod, Nat.mod_pow_succ,
        ← Nat.toNat_testBit, testBit_toNat]
      congr 1
      rw [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ m), Nat.mul_comm (n.getLsbD m).toNat]
      omega
    · simp [divSubtractShift, hm]

theorem umod_eq_divRec {w : Nat} {d n : BitVec w} :
    have out := BitVec.divRec w { n := n, d := d } (BitVec.DivModState.init w);
    n % d = out.r := by
  by_cases hd : 0#w < d
  · exact BitVec.umod_eq_divRec hd
  have hd0 : d = 0#w := by
    apply eq_of_toNat_eq; simp only [lt_def, toNat_ofNat, Nat.zero_mod] at hd; simp; omega
  subst hd0
  apply eq_of_toNat_eq
  rw [umod_zero, divRec_zero_r n w _ rfl]
  simp [DivModState.init, Nat.mod_eq_of_lt n.isLt]

end BitVecHand

/-! ## Necessary (11) -/

open BitVec in
section

-- `BitVec.iunfoldr_replace_snd` (`init`): `w = 1`, `f _ s := (s, s)`, `state := fun _ => false`,
-- `value := 0#1`, `a := true`; the result is `1#1`.
example : ¬ ∀ {w : Nat} {α : Type} {f : Fin w → α → α × Bool} (state : Nat → α) (value : BitVec w) (a : α),
    (∀ (i : Fin w), f i (state ↑i) = (state (↑i + 1), value[↑i])) → (BitVec.iunfoldr f a).snd = value :=
  fun h => absurd (h (w := 1) (f := fun _ s => (s, s)) (fun _ => false) 0#1 true (by decide)) (by decide +kernel)

-- `BitVec.iunfoldr_getLsbD` (`ind`): `w = 2`, `f _ s := (true, s)`, `state := fun _ => false`, `i = 1`:
-- bit 1 is `true` but `(f 1 false).snd = false`.
example : ¬ ∀ {w : Nat} {α : Type} {f : Fin w → α → α × Bool} (state : Nat → α) (i : Fin w),
    (BitVec.iunfoldr f (state 0)).snd.getLsbD ↑i = (f i (state ↑i)).snd :=
  fun h => absurd (h (w := 2) (f := fun _ s => (true, s)) (fun _ => false) 1) (by decide +kernel)

-- `BitVec.DivModState.umod_eq_of_lawful` (`h_final`): `w = 2`, `n = d = 2`,
-- `qr := ⟨wn := 1, wr := 1, q := 0, r := 1⟩` is lawful (`2 >>> 1 = 2 * 0 + 1`) but `2 % 2 = 0 ≠ 1`.
example : ¬ ∀ {w : Nat} {n d : BitVec w} {qr : BitVec.DivModState w},
    BitVec.DivModState.Lawful { n := n, d := d } qr → n % d = qr.r := fun h => by
  have := @h 2 2#2 2#2 ⟨1, 1, 0#2, 1#2⟩ ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  revert this; decide

-- `BitVec.cons_induction` (`nil`): `motive := fun _ _ => False`.
example : ¬ ∀ {motive : (w : Nat) → BitVec w → Prop},
    (∀ {w : Nat} (b : Bool) (bv : BitVec w), motive w bv → motive (w + 1) (BitVec.cons b bv)) →
      ∀ {w : Nat} (x : BitVec w), motive w x :=
  fun h => h (motive := fun _ _ => False) (fun _ _ h => h) (w := 0) BitVec.nil

-- `BitVec.cons_induction` (`cons`): `motive := fun w _ => w = 0`, at `0#1`.
example : ¬ ∀ {motive : (w : Nat) → BitVec w → Prop}, motive 0 BitVec.nil →
      ∀ {w : Nat} (x : BitVec w), motive w x :=
  fun h => absurd (h (motive := fun w _ => w = 0) rfl (w := 1) 0#1) (by decide)

-- `BitVec.concat_induction` (`nil`): `motive := fun _ _ => False`.
example : ¬ ∀ {motive : (w : Nat) → BitVec w → Prop},
    (∀ {w : Nat} (bv : BitVec w) (b : Bool), motive w bv → motive (w + 1) (bv.concat b)) →
      ∀ {w : Nat} (x : BitVec w), motive w x :=
  fun h => h (motive := fun _ _ => False) (fun _ _ h => h) (w := 0) BitVec.nil

-- `BitVec.concat_induction` (`concat`): `motive := fun w _ => w = 0`, at `0#1`.
example : ¬ ∀ {motive : (w : Nat) → BitVec w → Prop}, motive 0 BitVec.nil →
      ∀ {w : Nat} (x : BitVec w), motive w x :=
  fun h => absurd (h (motive := fun w _ => w = 0) rfl (w := 1) 0#1) (by decide)

-- `BitVec.lawful_divRec` (`h`): `w = 0`, `d = 0`; `Lawful` requires `0 < d`.
example : ¬ ∀ {w : Nat} {args : BitVec.DivModArgs w} {qr : BitVec.DivModState w},
    BitVec.DivModState.Lawful args (BitVec.divRec qr.wn args qr) :=
  fun h => absurd (@h 0 ⟨0#0, 0#0⟩ (DivModState.init 0)).hdPos (by decide)

-- `BitVec.DivModState.Poised.toLawful` (`self`): `w = 0`, `d = 0`; `Lawful` requires `0 < d`.
example : ¬ ∀ {w : Nat} {args : BitVec.DivModArgs w} {qr : BitVec.DivModState w},
    BitVec.DivModState.Lawful args qr :=
  fun h => absurd (@h 0 ⟨0#0, 0#0⟩ (DivModState.init 0)).hdPos (by decide)

-- `BitVec.DivModState.lawful_init` (`hd`): `w = 0`, `d = 0`; `Lawful` requires `0 < d`.
example : ¬ ∀ {w : Nat} (args : BitVec.DivModArgs w), BitVec.DivModState.Lawful args (BitVec.DivModState.init w) :=
  fun h => absurd (h (w := 0) ⟨0#0, 0#0⟩).hdPos (by decide)

-- `BitVec.lawful_divSubtractShift` (`h`): `w = 0`, `d = 0`; `Lawful` requires `0 < d`.
example : ¬ ∀ {w : Nat} {args : BitVec.DivModArgs w} (qr : BitVec.DivModState w),
    BitVec.DivModState.Lawful args (BitVec.divSubtractShift args qr) :=
  fun h => absurd (@h 0 ⟨0#0, 0#0⟩ (DivModState.init 0)).hdPos (by decide)

end

/-! ## Consistency: each removable restatement implies the original theorem -/

example : type_of% @BitVec.resRec_of_clz_le := fun hw _ hy => BitVecHand.resRec_of_clz_le_hx hw hy
example : type_of% @BitVec.resRec_of_clz_le := fun hw hx _ => BitVecHand.resRec_of_clz_le_hy hw hx
example : type_of% @BitVec.msb_neg_umod_neg_of_msb_true_of_msb_true := fun _ hy =>
  BitVecHand.msb_neg_umod_neg hy
example : type_of% @BitVec.neg_toInt_neg_umod_eq_of_msb_true_msb_true := fun _ hy =>
  BitVecHand.neg_toInt_neg_umod_hx hy
example : type_of% @BitVec.neg_toInt_neg_umod_eq_of_msb_true_msb_true := fun hx _ =>
  BitVecHand.neg_toInt_neg_umod_hy hx
example : type_of% @BitVec.toInt_signExtend_eq_toInt_bmod_of_le := fun x _ =>
  BitVecHand.toInt_signExtend_eq_toInt_bmod x
example : type_of% @BitVec.le_toNat_iff_getLsbD_eq_true := fun _ =>
  BitVecHand.le_toNat_iff_getLsbD_eq_true
example : type_of% @BitVec.toNat_lt_iff_getLsbD_eq_false := fun i _ =>
  BitVecHand.toNat_lt_iff_getLsbD_eq_false i
example : type_of% @BitVec.toInt_ediv_toInt_lt_of_nonpos_of_lt_neg_one := fun _ hy =>
  BitVecHand.toInt_ediv_toInt_lt_of_lt_neg_one hy
example : type_of% @BitVec.toInt_ediv_toInt_lt_of_nonneg_of_nonneg := fun _ hy =>
  BitVecHand.toInt_ediv_toInt_lt_of_nonneg_hx hy
example : type_of% @BitVec.toInt_ediv_toInt_lt_of_nonneg_of_nonneg := fun hx _ =>
  BitVecHand.toInt_ediv_toInt_lt_of_nonneg_hy hx
example : type_of% @BitVec.toNat_cpop_setWidth_le_of_le := fun _ => BitVecHand.toNat_cpop_setWidth_le
example : type_of% @BitVec.toInt_umod_neg_add := fun hy hx _ => BitVecHand.toInt_umod_neg_add hy hx
example : type_of% @BitVec.getMsbD_add := BitVecHand.getMsbD_add
example : type_of% @BitVec.getMsbD_sub := BitVecHand.getMsbD_sub
example : type_of% @BitVec.udiv_twoPow_eq_of_lt := fun _ => BitVecHand.udiv_twoPow_eq
example : type_of% @BitVec.clzAuxRec_eq_iff_of_getLsbD_false := fun _ => BitVecHand.clzAuxRec_eq_iff
example : type_of% @BitVec.carry_succ_one := fun i x _ => BitVecHand.carry_succ_one i x
example : type_of% @BitVec.toNat_ushiftRight_lt := fun x n _ => BitVecHand.toNat_ushiftRight_lt x n
example : type_of% @BitVec.ofNat_sub_ofNat_of_le := fun x y _ hlt =>
  BitVecHand.ofNat_sub_ofNat_of_le x y hlt
example : type_of% @BitVec.umod_eq_divRec := fun _ => BitVecHand.umod_eq_divRec
example : type_of% @BitVec.getElem_eq_true_of_lt_of_le := fun _ hlt hle =>
  BitVecHand.getElem_eq_true_of_lt_of_le hlt hle
example : type_of% @BitVec.toNat_shiftConcat_lt_of_lt := fun _ hx =>
  BitVecHand.toNat_shiftConcat_lt_of_lt hx
