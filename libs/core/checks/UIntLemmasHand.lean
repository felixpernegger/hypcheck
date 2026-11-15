import Lean

/-!
Hand pass over cluster `UIntLemmas` (hand6): the 77 unresolved hypotheses of
`Init.Data.UInt.Lemmas` (76) and `Init.Data.UInt.Modular` (1). For hypothesis `hᵢ` of theorem `T`
this file proves `¬T'` (necessary) or, for a dependent hypothesis, `¬∀ indep, Hᵢ`.

58 necessary, 0 removable, 19 independent (neither `T'` nor `¬T'` provable).

`drop% T i` elaborates to `T'` (`T` without binder `i`) and `indep% T i` to `∀ indep, Hᵢ` (all
independent binders), read off the library rather than retyped; `check_hand.py` compares them
with its own construction. Each refutation instantiates the hypothetical `T'` at the witness and
evaluates with `usz`: a case split on `System.Platform.numBits_eq` (`numBits` is opaque, so the
kernel can't compute it), then `simp_all` down to `Nat` arithmetic with concrete sizes. All
witnesses refute `T'` on both platforms (some are platform-dependent terms like `USize.size` or
`2 ^ numBits`).

Necessary (58): the order lemmas (`lt_trans`, `lt_of_le_of_lt`, ...) with `0`/`1`; `lt_add_one`
with `c = -1`; the `ofNatClamp`/`ofNatTruncate` lemmas with `n = USize.size` (`_of_lt`, `_eq_ofNat`)
or `n = 0` (`_of_le`); `toUInt8/16_div/mod(_of_dvd)` with `a = 2^k` or `b = 2^k + 1`;
`ofNat_div/mod` with `a = 2^numBits` or `b = 2^numBits + 1`; `ofNat_lt_iff_lt`/`ofNat_le_iff_le`
with `USize.size`; the dependent `ofNatLT_div/mod/mul` and `UInt8/16.ofNatLT_uSizeToNat`;
`UInt64.toNat_mulMod` with `modulus = 0` and `a = b = 2^32` (`mulMod` wraps to `0`).

Independent (19, in `runs/hand6/UIntLemmas_independent.jsonl`): `T'` (or `∀ indep, Hᵢ`) holds when
`numBits` is one value and fails for the other. Both halves are proved below as support lemmas
(`T.hᵢ_pos : numBits = k → T'`, `T.hᵢ_neg : numBits = k' → ¬T'`). `numBits` is the value of the
opaque `System.Platform.getNumBits : Unit → {n // n = 32 ∨ n = 64}`, and both implementations are
consistent with Lean's logic, so neither `T'` nor `¬T'` is provable (argument, not a Lean proof).
* `UInt64.toUSize_{div,mod}{,_of_toNat_lt}` (ha, hb), `toUSize_mod_of_dvd{,_usizeSize}`,
  `USize.toUInt64_ofNat{,'}`, `USize.ofNatLT_uInt64ToNat`: hold iff `numBits = 64`.
* `USize.toUInt32_mod` (ha, hb), `USize.toUInt32_mod_of_dvd`, `UInt32.toUSize_ofNat{,'}`,
  `UInt32.ofNatLT_uSizeToNat`: hold iff `numBits = 32`.

Run with the lean4 repo's stage1 binary: `lean checks/UIntLemmasHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false

open Lean Meta Elab Term in
/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    let mut dep := #[x]
    for j in [i.getNat+1:xs.size] do
      let t ← inferType xs[j]!
      if dep.any (fun d => t.containsFVar d.fvarId!) then dep := dep.push xs[j]!
    unless dep.size > 1 || body.containsFVar x.fvarId! do
      throwError "binder {i.getNat} of {n} is not dependent"
    mkForallFVars (xs.filter (fun y => !dep.contains y)) (← inferType x)

namespace UIntLemmasHand

theorem clampNat (n : Nat) :
    (USize.ofNatClamp n).toNat = if n < USize.size then n else USize.size - 1 := by
  split
  · exact USize.toNat_ofNatClamp_of_lt ‹_›
  · exact USize.toNat_ofNatClamp_of_le (by omega)

/-- Case split on the platform, then normalize everything to `Nat` with concrete sizes. -/
macro "usz" : tactic => `(tactic| (rcases System.Platform.numBits_eq with hnb | hnb <;>
  simp_all [USize.size, USize.lt_iff_toNat_lt, USize.le_iff_toNat_le, ← USize.toNat_inj, USize.toNat_ofNat',
    USize.toNat_ofNat, USize.toNat_div, USize.toNat_mod, USize.toNat_add, USize.toNat_neg, clampNat,
    Fin.ext_iff, ← BitVec.toNat_inj, USize.toNat_toUInt8, USize.toNat_toUInt16, USize.toNat_toUInt32,
    USize.toNat_toUInt64, ← UInt8.toNat_inj, ← UInt16.toNat_inj, ← UInt32.toNat_inj, ← UInt64.toNat_inj]))

theorem u64_lt (x : UInt64) : x.toNat < 18446744073709551616 := x.toNat_lt
theorem div_lt64 (x : UInt64) (n : Nat) : x.toNat / n < 18446744073709551616 :=
  Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.toNat_lt
theorem mod_lt64 (x : UInt64) (n : Nat) : x.toNat % n < 18446744073709551616 :=
  Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.toNat_lt
theorem usize_lt32 (h : System.Platform.numBits = 32) (x : USize) : x.toNat < 4294967296 := by
  have := x.toNat_lt_size; simp_all [USize.size]
theorem usize_mod32 (h : System.Platform.numBits = 32) (x : USize) (n : Nat) : x.toNat % n < 4294967296 :=
  Nat.lt_of_le_of_lt (Nat.mod_le _ _) (usize_lt32 h x)

/-- `usz` plus the bounds needed for the positive halves of the independent ones. -/
macro "uszp" : tactic => `(tactic| (rcases System.Platform.numBits_eq with hnb | hnb <;>
  simp_all [USize.size, USize.lt_iff_toNat_lt, USize.le_iff_toNat_le, ← USize.toNat_inj, USize.toNat_ofNat',
    USize.toNat_ofNat, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
    UInt32.toNat_ofNat, UInt64.toNat_ofNat, UInt32.size, UInt64.size, u64_lt, div_lt64, mod_lt64,
    usize_lt32, usize_mod32, Nat.mod_eq_of_lt, ← UInt32.toNat_inj, ← UInt64.toNat_inj]))

/-! ## Necessary -/

-- `USize.lt_trans`, idx 3 (`a : a < b`): `a = 1`, `b = 0`, `c = 1`
theorem USize.lt_trans.h3 : ¬ drop% USize.lt_trans 3 := fun h => by
  have := @h 1 0 1 (by usz); clear h; revert this; usz

-- `USize.lt_trans`, idx 4 (`a : b < c`): `a = 0`, `b = 1`, `c = 0`
theorem USize.lt_trans.h4 : ¬ drop% USize.lt_trans 4 := fun h => by
  have := @h 0 1 0 (by usz); clear h; revert this; usz

-- `USize.lt_of_le_of_lt`, idx 3 (`a : a ≤ b`): `a = 1`, `b = 0`, `c = 1`
theorem USize.lt_of_le_of_lt.h3 : ¬ drop% USize.lt_of_le_of_lt 3 := fun h => by
  have := @h 1 0 1 (by usz); clear h; revert this; usz

-- `USize.lt_of_lt_of_le`, idx 4 (`a : b ≤ c`): `a = 0`, `b = 1`, `c = 0`
theorem USize.lt_of_lt_of_le.h4 : ¬ drop% USize.lt_of_lt_of_le 4 := fun h => by
  have := @h 0 1 0 (by usz); clear h; revert this; usz

-- `USize.lt_of_le_of_ne`, idx 2 (`a : a ≤ b`): `a = 1`, `b = 0`
theorem USize.lt_of_le_of_ne.h2 : ¬ drop% USize.lt_of_le_of_ne 2 := fun h => by
  have := @h 1 0 (by usz); clear h; revert this; usz

-- `UInt8.lt_add_one`, idx 1 (`h : c ≠ -1`): `c = -1`: `c + 1 = 0`
theorem UInt8.lt_add_one.h1 : ¬ drop% UInt8.lt_add_one 1 := fun h => by
  have := @h (-1); clear h; revert this; decide

-- `UInt16.lt_add_one`, idx 1 (`h : c ≠ -1`): `c = -1`: `c + 1 = 0`
theorem UInt16.lt_add_one.h1 : ¬ drop% UInt16.lt_add_one 1 := fun h => by
  have := @h (-1); clear h; revert this; decide

-- `UInt32.lt_add_one`, idx 1 (`h : c ≠ -1`): `c = -1`: `c + 1 = 0`
theorem UInt32.lt_add_one.h1 : ¬ drop% UInt32.lt_add_one 1 := fun h => by
  have := @h (-1); clear h; revert this; decide

-- `UInt64.lt_add_one`, idx 1 (`h : c ≠ -1`): `c = -1`: `c + 1 = 0`
theorem UInt64.lt_add_one.h1 : ¬ drop% UInt64.lt_add_one 1 := fun h => by
  have := @h (-1); clear h; revert this; decide

-- `USize.lt_add_one`, idx 1 (`h : c ≠ -1`): `c = -1`: `c + 1 = 0` on both platforms
theorem USize.lt_add_one.h1 : ¬ drop% USize.lt_add_one 1 := fun h => by
  have := @h (-1); clear h; revert this; usz

-- `USize.toNat_ofNat_of_lt_32`, idx 1 (`h : n < 4294967296`): `n = 2^64`: `toNat (ofNat n) = 0` on both platforms
theorem USize.toNat_ofNat_of_lt_32.h1 : ¬ drop% USize.toNat_ofNat_of_lt_32 1 := fun h => by
  have := @h (2^64); clear h; revert this; usz

-- `USize.ofNatClamp_eq_ofNat`, idx 1 (`hn : n < USize.size`): `n = USize.size`: clamp gives `size - 1`, `ofNat` gives `0`
theorem USize.ofNatClamp_eq_ofNat.h1 : ¬ drop% USize.ofNatClamp_eq_ofNat 1 := fun h => by
  have := @h USize.size; clear h; revert this; usz

-- `USize.toNat_ofNatClamp_of_lt`, idx 1 (`hn : n < USize.size`): `n = USize.size`: `toNat = size - 1 ≠ size`
theorem USize.toNat_ofNatClamp_of_lt.h1 : ¬ drop% USize.toNat_ofNatClamp_of_lt 1 := fun h => by
  have := @h USize.size; clear h; revert this; usz

-- `USize.toUInt8_ofNatClamp_of_lt`, idx 1 (`hn : n < USize.size`): `n = USize.size`: LHS is `UInt8.size - 1`, `UInt8.ofNat USize.size = 0`
theorem USize.toUInt8_ofNatClamp_of_lt.h1 : ¬ drop% USize.toUInt8_ofNatClamp_of_lt 1 := fun h => by
  have := @h USize.size; clear h; revert this; usz

-- `USize.toUInt16_ofNatClamp_of_lt`, idx 1 (`hn : n < USize.size`): `n = USize.size`: LHS is `UInt16.size - 1`, `UInt16.ofNat USize.size = 0`
theorem USize.toUInt16_ofNatClamp_of_lt.h1 : ¬ drop% USize.toUInt16_ofNatClamp_of_lt 1 := fun h => by
  have := @h USize.size; clear h; revert this; usz

-- `USize.toUInt32_ofNatClamp_of_lt`, idx 1 (`hn : n < USize.size`): `n = USize.size`: LHS is `UInt32.size - 1`, `UInt32.ofNat USize.size = 0`
theorem USize.toUInt32_ofNatClamp_of_lt.h1 : ¬ drop% USize.toUInt32_ofNatClamp_of_lt 1 := fun h => by
  have := @h USize.size; clear h; revert this; usz

-- `USize.toNat_ofNatClamp_of_le`, idx 1 (`hn : USize.size ≤ n`): `n = 0`: LHS is `0`, RHS `size - 1 ≠ 0`
theorem USize.toNat_ofNatClamp_of_le.h1 : ¬ drop% USize.toNat_ofNatClamp_of_le 1 := fun h => by
  have := @h 0; clear h; revert this; usz

-- `USize.toFin_ofNatClamp_of_le`, idx 1 (`hn : USize.size ≤ n`): `n = 0`: LHS is `0`, RHS `size - 1 ≠ 0`
theorem USize.toFin_ofNatClamp_of_le.h1 : ¬ drop% USize.toFin_ofNatClamp_of_le 1 := fun h => by
  have := @h 0; clear h; revert this; usz

-- `USize.toBitVec_ofNatClamp_of_le`, idx 1 (`hn : USize.size ≤ n`): `n = 0`: LHS is `0`, RHS `size - 1 ≠ 0`
theorem USize.toBitVec_ofNatClamp_of_le.h1 : ¬ drop% USize.toBitVec_ofNatClamp_of_le 1 := fun h => by
  have := @h 0; clear h; revert this; usz

-- `USize.toUInt8_ofNatClamp_of_le`, idx 1 (`hn : USize.size ≤ n`): `n = 0`: LHS is `0`, RHS `size - 1 ≠ 0`
theorem USize.toUInt8_ofNatClamp_of_le.h1 : ¬ drop% USize.toUInt8_ofNatClamp_of_le 1 := fun h => by
  have := @h 0; clear h; revert this; usz

-- `USize.toUInt16_ofNatClamp_of_le`, idx 1 (`hn : USize.size ≤ n`): `n = 0`: LHS is `0`, RHS `size - 1 ≠ 0`
theorem USize.toUInt16_ofNatClamp_of_le.h1 : ¬ drop% USize.toUInt16_ofNatClamp_of_le 1 := fun h => by
  have := @h 0; clear h; revert this; usz

-- `USize.toUInt32_ofNatClamp_of_le`, idx 1 (`hn : USize.size ≤ n`): `n = 0`: LHS is `0`, RHS `size - 1 ≠ 0`
theorem USize.toUInt32_ofNatClamp_of_le.h1 : ¬ drop% USize.toUInt32_ofNatClamp_of_le 1 := fun h => by
  have := @h 0; clear h; revert this; usz

-- `USize.toUInt64_ofNatClamp_of_le`, idx 1 (`hn : USize.size ≤ n`): `n = 0`: LHS is `0`, RHS `size - 1 ≠ 0`
theorem USize.toUInt64_ofNatClamp_of_le.h1 : ¬ drop% USize.toUInt64_ofNatClamp_of_le 1 := fun h => by
  have := @h 0; clear h; revert this; usz

-- `USize.ofNatTruncate_eq_ofNat`, idx 1 (`hn : n < USize.size`): `n = USize.size`: clamp gives `size - 1`, `ofNat` gives `0`
theorem USize.ofNatTruncate_eq_ofNat.h1 : ¬ drop% USize.ofNatTruncate_eq_ofNat 1 := fun h => by
  have := @h USize.size; clear h; revert this; usz

-- `USize.toNat_ofNatTruncate_of_lt`, idx 1 (`hn : n < USize.size`): `n = USize.size`: `toNat = size - 1 ≠ size`
theorem USize.toNat_ofNatTruncate_of_lt.h1 : ¬ drop% USize.toNat_ofNatTruncate_of_lt 1 := fun h => by
  have := @h USize.size; clear h; revert this; usz

-- `USize.toUInt8_ofNatTruncate_of_lt`, idx 1 (`hn : n < USize.size`): `n = USize.size`: LHS is `UInt8.size - 1`, `UInt8.ofNat USize.size = 0`
theorem USize.toUInt8_ofNatTruncate_of_lt.h1 : ¬ drop% USize.toUInt8_ofNatTruncate_of_lt 1 := fun h => by
  have := @h USize.size; clear h; revert this; usz

-- `USize.toUInt16_ofNatTruncate_of_lt`, idx 1 (`hn : n < USize.size`): `n = USize.size`: LHS is `UInt16.size - 1`, `UInt16.ofNat USize.size = 0`
theorem USize.toUInt16_ofNatTruncate_of_lt.h1 : ¬ drop% USize.toUInt16_ofNatTruncate_of_lt 1 := fun h => by
  have := @h USize.size; clear h; revert this; usz

-- `USize.toUInt32_ofNatTruncate_of_lt`, idx 1 (`hn : n < USize.size`): `n = USize.size`: LHS is `UInt32.size - 1`, `UInt32.ofNat USize.size = 0`
theorem USize.toUInt32_ofNatTruncate_of_lt.h1 : ¬ drop% USize.toUInt32_ofNatTruncate_of_lt 1 := fun h => by
  have := @h USize.size; clear h; revert this; usz

-- `USize.toNat_ofNatTruncate_of_le`, idx 1 (`hn : USize.size ≤ n`): `n = 0`: LHS is `0`, RHS `size - 1 ≠ 0`
theorem USize.toNat_ofNatTruncate_of_le.h1 : ¬ drop% USize.toNat_ofNatTruncate_of_le 1 := fun h => by
  have := @h 0; clear h; revert this; usz

-- `USize.toFin_ofNatTruncate_of_le`, idx 1 (`hn : USize.size ≤ n`): `n = 0`: LHS is `0`, RHS `size - 1 ≠ 0`
theorem USize.toFin_ofNatTruncate_of_le.h1 : ¬ drop% USize.toFin_ofNatTruncate_of_le 1 := fun h => by
  have := @h 0; clear h; revert this; usz

-- `USize.toBitVec_ofNatTruncate_of_le`, idx 1 (`hn : USize.size ≤ n`): `n = 0`: LHS is `0`, RHS `size - 1 ≠ 0`
theorem USize.toBitVec_ofNatTruncate_of_le.h1 : ¬ drop% USize.toBitVec_ofNatTruncate_of_le 1 := fun h => by
  have := @h 0; clear h; revert this; usz

-- `USize.toUInt8_ofNatTruncate_of_le`, idx 1 (`hn : USize.size ≤ n`): `n = 0`: LHS is `0`, RHS `size - 1 ≠ 0`
theorem USize.toUInt8_ofNatTruncate_of_le.h1 : ¬ drop% USize.toUInt8_ofNatTruncate_of_le 1 := fun h => by
  have := @h 0; clear h; revert this; usz

-- `USize.toUInt16_ofNatTruncate_of_le`, idx 1 (`hn : USize.size ≤ n`): `n = 0`: LHS is `0`, RHS `size - 1 ≠ 0`
theorem USize.toUInt16_ofNatTruncate_of_le.h1 : ¬ drop% USize.toUInt16_ofNatTruncate_of_le 1 := fun h => by
  have := @h 0; clear h; revert this; usz

-- `USize.toUInt32_ofNatTruncate_of_le`, idx 1 (`hn : USize.size ≤ n`): `n = 0`: LHS is `0`, RHS `size - 1 ≠ 0`
theorem USize.toUInt32_ofNatTruncate_of_le.h1 : ¬ drop% USize.toUInt32_ofNatTruncate_of_le 1 := fun h => by
  have := @h 0; clear h; revert this; usz

-- `USize.toUInt64_ofNatTruncate_of_le`, idx 1 (`hn : USize.size ≤ n`): `n = 0`: LHS is `0`, RHS `size - 1 ≠ 0`
theorem USize.toUInt64_ofNatTruncate_of_le.h1 : ¬ drop% USize.toUInt64_ofNatTruncate_of_le 1 := fun h => by
  have := @h 0; clear h; revert this; usz

-- `USize.toUInt8_div`, idx 2 (`ha : a < 256`): `a = 256`, `b = 2`: `128` vs `0 / 2 = 0`
theorem USize.toUInt8_div.h2 : ¬ drop% USize.toUInt8_div 2 := fun h => by
  have := @h 256 2 (by usz); clear h; revert this; usz

-- `USize.toUInt8_div`, idx 3 (`hb : b < 256`): `a = 2`, `b = 257`: `0` vs `2 / 1 = 2`
theorem USize.toUInt8_div.h3 : ¬ drop% USize.toUInt8_div 3 := fun h => by
  have := @h 2 257 (by usz); clear h; revert this; usz

-- `USize.toUInt8_mod`, idx 2 (`ha : a < 256`): `a = 256`, `b = 3`: `1` vs `0 % 3 = 0`
theorem USize.toUInt8_mod.h2 : ¬ drop% USize.toUInt8_mod 2 := fun h => by
  have := @h 256 3 (by usz); clear h; revert this; usz

-- `USize.toUInt8_mod`, idx 3 (`hb : b < 256`): `a = 2`, `b = 257`: `2` vs `2 % 1 = 0`
theorem USize.toUInt8_mod.h3 : ¬ drop% USize.toUInt8_mod 3 := fun h => by
  have := @h 2 257 (by usz); clear h; revert this; usz

-- `USize.toUInt8_mod_of_dvd`, idx 2 (`hb : b.toNat ∣ 256`): `a = 256`, `b = 3`: `1` vs `0 % 3 = 0`
theorem USize.toUInt8_mod_of_dvd.h2 : ¬ drop% USize.toUInt8_mod_of_dvd 2 := fun h => by
  have := @h 256 3; clear h; revert this; usz

-- `USize.toUInt16_div`, idx 2 (`ha : a < 65536`): `a = 65536`, `b = 2`: `32768` vs `0 / 2 = 0`
theorem USize.toUInt16_div.h2 : ¬ drop% USize.toUInt16_div 2 := fun h => by
  have := @h 65536 2 (by usz); clear h; revert this; usz

-- `USize.toUInt16_div`, idx 3 (`hb : b < 65536`): `a = 2`, `b = 65537`: `0` vs `2 / 1 = 2`
theorem USize.toUInt16_div.h3 : ¬ drop% USize.toUInt16_div 3 := fun h => by
  have := @h 2 65537 (by usz); clear h; revert this; usz

-- `USize.toUInt16_mod`, idx 2 (`ha : a < 65536`): `a = 65536`, `b = 3`: `1` vs `0 % 3 = 0`
theorem USize.toUInt16_mod.h2 : ¬ drop% USize.toUInt16_mod 2 := fun h => by
  have := @h 65536 3 (by usz); clear h; revert this; usz

-- `USize.toUInt16_mod`, idx 3 (`hb : b < 65536`): `a = 2`, `b = 65537`: `2` vs `2 % 1 = 0`
theorem USize.toUInt16_mod.h3 : ¬ drop% USize.toUInt16_mod 3 := fun h => by
  have := @h 2 65537 (by usz); clear h; revert this; usz

-- `USize.toUInt16_mod_of_dvd`, idx 2 (`hb : b.toNat ∣ 65536`): `a = 65536`, `b = 3`: `1` vs `0 % 3 = 0`
theorem USize.toUInt16_mod_of_dvd.h2 : ¬ drop% USize.toUInt16_mod_of_dvd 2 := fun h => by
  have := @h 65536 3; clear h; revert this; usz

-- `USize.ofNat_div`, idx 2 (`ha : a < 2 ^ System.Platform.numBits`): `a = 2^numBits`, `b = 2`: `ofNat (2^(numBits-1)) ≠ 0 / 2`
theorem USize.ofNat_div.h2 : ¬ drop% USize.ofNat_div 2 := fun h => by
  have := @h (2^System.Platform.numBits) 2 (by usz); clear h; revert this; usz

-- `USize.ofNat_div`, idx 3 (`hb : b < 2 ^ System.Platform.numBits`): `a = 2`, `b = 2^numBits + 1`: `0` vs `2 / 1 = 2`
theorem USize.ofNat_div.h3 : ¬ drop% USize.ofNat_div 3 := fun h => by
  have := @h 2 (2^System.Platform.numBits+1) (by usz); clear h; revert this; usz

-- `USize.ofNat_mod`, idx 2 (`ha : a < 2 ^ System.Platform.numBits`): `a = 2^numBits`, `b = 3`: `2^numBits % 3 = 1` vs `0 % 3 = 0`
theorem USize.ofNat_mod.h2 : ¬ drop% USize.ofNat_mod 2 := fun h => by
  have := @h (2^System.Platform.numBits) 3 (by usz); clear h; revert this; usz

-- `USize.ofNat_mod`, idx 3 (`hb : b < 2 ^ System.Platform.numBits`): `a = 2`, `b = 2^numBits + 1`: `2` vs `2 % 1 = 0`
theorem USize.ofNat_mod.h3 : ¬ drop% USize.ofNat_mod 3 := fun h => by
  have := @h 2 (2^System.Platform.numBits+1) (by usz); clear h; revert this; usz

-- `USize.ofNatLT_div`, idx 3 (`hb : b < 2 ^ System.Platform.numBits`) (dependent): dependent; `∀ indep, Hᵢ` fails at `b = 2^numBits`
theorem USize.ofNatLT_div.h3 : ¬ indep% USize.ofNatLT_div 3 := fun h => by
  have := @h 0 (2^System.Platform.numBits) (by usz); clear h; revert this; usz

-- `USize.ofNatLT_mod`, idx 3 (`hb : b < 2 ^ System.Platform.numBits`) (dependent): dependent; `∀ indep, Hᵢ` fails at `b = 2^numBits`
theorem USize.ofNatLT_mod.h3 : ¬ indep% USize.ofNatLT_mod 3 := fun h => by
  have := @h 0 (2^System.Platform.numBits) (by usz); clear h; revert this; usz

-- `USize.ofNatLT_mul`, idx 3 (`hb : b < 2 ^ System.Platform.numBits`) (dependent): dependent; `∀ indep, Hᵢ` fails at `a = 0`, `b = 2^numBits`
theorem USize.ofNatLT_mul.h3 : ¬ indep% USize.ofNatLT_mul 3 := fun h => by
  have := @h 0 (2^System.Platform.numBits) (by usz) (by usz); clear h; revert this; usz

-- `USize.ofNatLT_mul`, idx 4 (`hab : a * b < 2 ^ System.Platform.numBits`) (dependent): dependent; `∀ indep, Hᵢ` fails at `a = b = 2^numBits - 1`
theorem USize.ofNatLT_mul.h4 : ¬ indep% USize.ofNatLT_mul 4 := fun h => by
  have := @h (2^System.Platform.numBits-1) (2^System.Platform.numBits-1) (by usz) (by usz); clear h; revert this; usz

-- `USize.ofNat_lt_iff_lt`, idx 2 (`ha : a < USize.size`): `a = USize.size`, `b = 1`: `ofNat a = 0 < 1` but `¬ a < 1`
theorem USize.ofNat_lt_iff_lt.h2 : ¬ drop% USize.ofNat_lt_iff_lt 2 := fun h => by
  have := @h USize.size 1 (by usz); clear h; revert this; usz

-- `USize.ofNat_le_iff_le`, idx 3 (`hb : b < USize.size`): `a = 1`, `b = USize.size`: `¬ 1 ≤ ofNat b = 0` but `1 ≤ b`
theorem USize.ofNat_le_iff_le.h3 : ¬ drop% USize.ofNat_le_iff_le 3 := fun h => by
  have := @h 1 USize.size (by usz); clear h; revert this; usz

-- `UInt8.ofNatLT_uSizeToNat`, idx 1 (`h : n.toNat < UInt8.size`) (dependent): dependent; `∀ n : USize, n.toNat < 256` fails at `n = 256`
theorem UInt8.ofNatLT_uSizeToNat.h1 : ¬ indep% UInt8.ofNatLT_uSizeToNat 1 := fun h => by
  have := @h 256; clear h; revert this; usz

-- `UInt16.ofNatLT_uSizeToNat`, idx 1 (`h : n.toNat < UInt16.size`) (dependent): dependent; `∀ n : USize, n.toNat < 65536` fails at `n = 65536`
theorem UInt16.ofNatLT_uSizeToNat.h1 : ¬ indep% UInt16.ofNatLT_uSizeToNat 1 := fun h => by
  have := @h 65536; clear h; revert this; usz

-- `UInt64.toNat_mulMod`, idx 3 (`h : modulus ≠ 0`): `a = b = 2^32`, `modulus = 0`: `mulMod` wraps to `0`, RHS `2^64`
theorem UInt64.toNat_mulMod.h3 : ¬ drop% UInt64.toNat_mulMod 3 := fun h => by
  have := @h 4294967296 4294967296 0; clear h; revert this; decide

/-! ## Independent: kernel-checked halves (support lemmas, not verdicts) -/

-- `UInt32.ofNatLT_uSizeToNat`, idx 1 (`h : n.toNat < UInt32.size`): dependent; `∀ n : USize, n.toNat < 2^32` holds iff `numBits = 32` (fails at `n = 2^32` when `numBits = 64`)
theorem UInt32.ofNatLT_uSizeToNat.h1_pos : System.Platform.numBits = 32 → indep% UInt32.ofNatLT_uSizeToNat 1 := by
  intro hnb; intros; uszp
theorem UInt32.ofNatLT_uSizeToNat.h1_neg : System.Platform.numBits = 64 → ¬ indep% UInt32.ofNatLT_uSizeToNat 1 := fun hnb h => by
  have := @h 4294967296; clear h; revert this; uszp

-- `USize.ofNatLT_uInt64ToNat`, idx 1 (`h : n.toNat < USize.size`): dependent; `∀ n : UInt64, n.toNat < USize.size` holds iff `numBits = 64` (fails at `n = 2^32` when `numBits = 32`)
theorem USize.ofNatLT_uInt64ToNat.h1_pos : System.Platform.numBits = 64 → indep% USize.ofNatLT_uInt64ToNat 1 := by
  intro hnb; intros; uszp
theorem USize.ofNatLT_uInt64ToNat.h1_neg : System.Platform.numBits = 32 → ¬ indep% USize.ofNatLT_uInt64ToNat 1 := fun hnb h => by
  have := @h 4294967296; clear h; revert this; uszp

-- `UInt32.toUSize_ofNat'`, idx 1 (`hn : n < UInt32.size`): T' holds iff `numBits = 32` (`toUSize` after truncation to 32 bits equals `USize.ofNat` then); fails at `n = 2^32` when `numBits = 64`
theorem UInt32.toUSize_ofNat'.h1_pos : System.Platform.numBits = 32 → drop% UInt32.toUSize_ofNat' 1 := by
  intro hnb; intros; uszp
theorem UInt32.toUSize_ofNat'.h1_neg : System.Platform.numBits = 64 → ¬ drop% UInt32.toUSize_ofNat' 1 := fun hnb h => by
  have := @h 4294967296; clear h; revert this; uszp

-- `UInt32.toUSize_ofNat`, idx 1 (`hn : n < 4294967296`): T' holds iff `numBits = 32` (`toUSize` after truncation to 32 bits equals `USize.ofNat` then); fails at `n = 2^32` when `numBits = 64`
theorem UInt32.toUSize_ofNat.h1_pos : System.Platform.numBits = 32 → drop% UInt32.toUSize_ofNat 1 := by
  intro hnb; intros; uszp
theorem UInt32.toUSize_ofNat.h1_neg : System.Platform.numBits = 64 → ¬ drop% UInt32.toUSize_ofNat 1 := fun hnb h => by
  have := @h 4294967296; clear h; revert this; uszp

-- `USize.toUInt64_ofNat'`, idx 1 (`hn : n < USize.size`): T' holds iff `numBits = 64` (`USize.ofNat` and `UInt64.ofNat` both reduce mod 2^64); fails at `n = 2^32` when `numBits = 32`
theorem USize.toUInt64_ofNat'.h1_pos : System.Platform.numBits = 64 → drop% USize.toUInt64_ofNat' 1 := by
  intro hnb; intros; uszp
theorem USize.toUInt64_ofNat'.h1_neg : System.Platform.numBits = 32 → ¬ drop% USize.toUInt64_ofNat' 1 := fun hnb h => by
  have := @h 4294967296; clear h; revert this; uszp

-- `USize.toUInt64_ofNat`, idx 1 (`hn : n < 4294967296`): T' holds iff `numBits = 64` (`USize.ofNat` and `UInt64.ofNat` both reduce mod 2^64); fails at `n = 2^32` when `numBits = 32`
theorem USize.toUInt64_ofNat.h1_pos : System.Platform.numBits = 64 → drop% USize.toUInt64_ofNat 1 := by
  intro hnb; intros; uszp
theorem USize.toUInt64_ofNat.h1_neg : System.Platform.numBits = 32 → ¬ drop% USize.toUInt64_ofNat 1 := fun hnb h => by
  have := @h 4294967296; clear h; revert this; uszp

-- `UInt64.toUSize_div`, idx 2 (`ha : a < 4294967296`): T' holds iff `numBits = 64` (`toUSize` is injective then); fails at `a = 4294967296`, `b = 2` when `numBits = 32`
theorem UInt64.toUSize_div.h2_pos : System.Platform.numBits = 64 → drop% UInt64.toUSize_div 2 := by
  intro hnb; intros; uszp
theorem UInt64.toUSize_div.h2_neg : System.Platform.numBits = 32 → ¬ drop% UInt64.toUSize_div 2 := fun hnb h => by
  have := @h 4294967296 2 (by usz); clear h; revert this; uszp

-- `UInt64.toUSize_div`, idx 3 (`hb : b < 4294967296`): T' holds iff `numBits = 64` (`toUSize` is injective then); fails at `a = 2`, `b = 2^32 + 1` when `numBits = 32`
theorem UInt64.toUSize_div.h3_pos : System.Platform.numBits = 64 → drop% UInt64.toUSize_div 3 := by
  intro hnb; intros; uszp
theorem UInt64.toUSize_div.h3_neg : System.Platform.numBits = 32 → ¬ drop% UInt64.toUSize_div 3 := fun hnb h => by
  have := @h 2 4294967297 (by usz); clear h; revert this; uszp

-- `UInt64.toUSize_div_of_toNat_lt`, idx 2 (`ha : a.toNat < USize.size`): T' holds iff `numBits = 64` (`toUSize` is injective then); fails at `a = 4294967296`, `b = 2` when `numBits = 32`
theorem UInt64.toUSize_div_of_toNat_lt.h2_pos : System.Platform.numBits = 64 → drop% UInt64.toUSize_div_of_toNat_lt 2 := by
  intro hnb; intros; uszp
theorem UInt64.toUSize_div_of_toNat_lt.h2_neg : System.Platform.numBits = 32 → ¬ drop% UInt64.toUSize_div_of_toNat_lt 2 := fun hnb h => by
  have := @h 4294967296 2 (by usz); clear h; revert this; uszp

-- `UInt64.toUSize_div_of_toNat_lt`, idx 3 (`hb : b.toNat < USize.size`): T' holds iff `numBits = 64` (`toUSize` is injective then); fails at `a = 2`, `b = 2^32 + 1` when `numBits = 32`
theorem UInt64.toUSize_div_of_toNat_lt.h3_pos : System.Platform.numBits = 64 → drop% UInt64.toUSize_div_of_toNat_lt 3 := by
  intro hnb; intros; uszp
theorem UInt64.toUSize_div_of_toNat_lt.h3_neg : System.Platform.numBits = 32 → ¬ drop% UInt64.toUSize_div_of_toNat_lt 3 := fun hnb h => by
  have := @h 2 4294967297 (by usz); clear h; revert this; uszp

-- `UInt64.toUSize_mod`, idx 2 (`ha : a < 4294967296`): T' holds iff `numBits = 64` (`toUSize` is injective then); fails at `a = 4294967296`, `b = 3` when `numBits = 32`
theorem UInt64.toUSize_mod.h2_pos : System.Platform.numBits = 64 → drop% UInt64.toUSize_mod 2 := by
  intro hnb; intros; uszp
theorem UInt64.toUSize_mod.h2_neg : System.Platform.numBits = 32 → ¬ drop% UInt64.toUSize_mod 2 := fun hnb h => by
  have := @h 4294967296 3 (by usz); clear h; revert this; uszp

-- `UInt64.toUSize_mod`, idx 3 (`hb : b < 4294967296`): T' holds iff `numBits = 64` (`toUSize` is injective then); fails at `a = 2`, `b = 2^32 + 1` when `numBits = 32`
theorem UInt64.toUSize_mod.h3_pos : System.Platform.numBits = 64 → drop% UInt64.toUSize_mod 3 := by
  intro hnb; intros; uszp
theorem UInt64.toUSize_mod.h3_neg : System.Platform.numBits = 32 → ¬ drop% UInt64.toUSize_mod 3 := fun hnb h => by
  have := @h 2 4294967297 (by usz); clear h; revert this; uszp

-- `UInt64.toUSize_mod_of_toNat_lt`, idx 2 (`ha : a.toNat < USize.size`): T' holds iff `numBits = 64` (`toUSize` is injective then); fails at `a = 4294967296`, `b = 3` when `numBits = 32`
theorem UInt64.toUSize_mod_of_toNat_lt.h2_pos : System.Platform.numBits = 64 → drop% UInt64.toUSize_mod_of_toNat_lt 2 := by
  intro hnb; intros; uszp
theorem UInt64.toUSize_mod_of_toNat_lt.h2_neg : System.Platform.numBits = 32 → ¬ drop% UInt64.toUSize_mod_of_toNat_lt 2 := fun hnb h => by
  have := @h 4294967296 3 (by usz); clear h; revert this; uszp

-- `UInt64.toUSize_mod_of_toNat_lt`, idx 3 (`hb : b.toNat < USize.size`): T' holds iff `numBits = 64` (`toUSize` is injective then); fails at `a = 2`, `b = 2^32 + 1` when `numBits = 32`
theorem UInt64.toUSize_mod_of_toNat_lt.h3_pos : System.Platform.numBits = 64 → drop% UInt64.toUSize_mod_of_toNat_lt 3 := by
  intro hnb; intros; uszp
theorem UInt64.toUSize_mod_of_toNat_lt.h3_neg : System.Platform.numBits = 32 → ¬ drop% UInt64.toUSize_mod_of_toNat_lt 3 := fun hnb h => by
  have := @h 2 4294967297 (by usz); clear h; revert this; uszp

-- `UInt64.toUSize_mod_of_dvd`, idx 2 (`hb : b.toNat ∣ 4294967296`): T' holds iff `numBits = 64` (`toUSize` is injective then); fails at `a = 2^32`, `b = 3` when `numBits = 32`
theorem UInt64.toUSize_mod_of_dvd.h2_pos : System.Platform.numBits = 64 → drop% UInt64.toUSize_mod_of_dvd 2 := by
  intro hnb; intros; uszp
theorem UInt64.toUSize_mod_of_dvd.h2_neg : System.Platform.numBits = 32 → ¬ drop% UInt64.toUSize_mod_of_dvd 2 := fun hnb h => by
  have := @h 4294967296 3; clear h; revert this; uszp

-- `UInt64.toUSize_mod_of_dvd_usizeSize`, idx 2 (`hb : b.toNat ∣ USize.size`): T' holds iff `numBits = 64` (`toUSize` is injective then); fails at `a = 2^32`, `b = 3` when `numBits = 32`
theorem UInt64.toUSize_mod_of_dvd_usizeSize.h2_pos : System.Platform.numBits = 64 → drop% UInt64.toUSize_mod_of_dvd_usizeSize 2 := by
  intro hnb; intros; uszp
theorem UInt64.toUSize_mod_of_dvd_usizeSize.h2_neg : System.Platform.numBits = 32 → ¬ drop% UInt64.toUSize_mod_of_dvd_usizeSize 2 := fun hnb h => by
  have := @h 4294967296 3; clear h; revert this; uszp

-- `USize.toUInt32_mod`, idx 2 (`ha : a < 4294967296`): T' holds iff `numBits = 32` (`toUInt32` is injective then; also the remaining `hb : b < 4294967296` is `b < 0` there); fails at `a = 2^32`, `b = 3` when `numBits = 64`
theorem USize.toUInt32_mod.h2_pos : System.Platform.numBits = 32 → drop% USize.toUInt32_mod 2 := by
  intro hnb; intros; uszp
theorem USize.toUInt32_mod.h2_neg : System.Platform.numBits = 64 → ¬ drop% USize.toUInt32_mod 2 := fun hnb h => by
  have := @h 4294967296 3 (by usz); clear h; revert this; uszp

-- `USize.toUInt32_mod`, idx 3 (`hb : b < 4294967296`): T' holds iff `numBits = 32` (`toUInt32` is injective then; also the remaining `ha : a < 4294967296` is `a < 0` there); fails at `a = 2`, `b = 2^32 + 1` when `numBits = 64`
theorem USize.toUInt32_mod.h3_pos : System.Platform.numBits = 32 → drop% USize.toUInt32_mod 3 := by
  intro hnb; intros; uszp
theorem USize.toUInt32_mod.h3_neg : System.Platform.numBits = 64 → ¬ drop% USize.toUInt32_mod 3 := fun hnb h => by
  have := @h 2 4294967297 (by usz); clear h; revert this; uszp

-- `USize.toUInt32_mod_of_dvd`, idx 2 (`hb : b.toNat ∣ 4294967296`): T' holds iff `numBits = 32` (`toUInt32` is injective then); fails at `a = 2^32`, `b = 3` when `numBits = 64`
theorem USize.toUInt32_mod_of_dvd.h2_pos : System.Platform.numBits = 32 → drop% USize.toUInt32_mod_of_dvd 2 := by
  intro hnb; intros; uszp
theorem USize.toUInt32_mod_of_dvd.h2_neg : System.Platform.numBits = 64 → ¬ drop% USize.toUInt32_mod_of_dvd 2 := fun hnb h => by
  have := @h 4294967296 3; clear h; revert this; uszp

end UIntLemmasHand
