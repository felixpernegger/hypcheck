import Lean

/-!
Hand pass over cluster `SIntFixed` (hand7): the 72 unresolved hypotheses of `Int8/16/32/64` lemmas in
`Init.Data.SInt.Lemmas` (6 dependent). For hypothesis `hᵢ` of theorem `T` this file proves `¬T'`
(necessary) or, for a dependent hypothesis, `¬∀ indep, Hᵢ`.

62 necessary, 0 removable, 10 independent (neither `T'` nor `¬T'` provable).

`drop% T i` elaborates to `T'` (`T` without binder `i`) and `indep% T i` to `∀ indep, Hᵢ` (all
independent binders), read off the library rather than retyped; `check_hand.py` compares them with its
own construction. Each refutation instantiates the hypothetical `T'` at the witness and evaluates:
fixed widths with `decide`; statements mentioning `ISize` with `isz` (case split on
`System.Platform.numBits_eq`, since `numBits` is opaque, then `simp_all` down to concrete `Int`
arithmetic, then `decide`). All ISize witnesses refute `T'` on both platforms.

The tool's small-value search missed these because the counterexamples sit at the edges of the range:
`minValue`/`maxValue` with `±1` (wrap-around in `sub`, `minValue / -1` overflow), `b = maxValue + 2`
for `ofInt_tmod`, `n = minValue - 1` / `maxValue + 1` for the conversions to `ISize`.

Independent (10, in `runs/hand7/SIntFixed_independent.jsonl`): `T'` (or `∀ indep, Hᵢ`) holds when
`numBits` is one value and fails for the other. Both halves are proved below as support lemmas
(`T.hᵢ_pos`, `T.hᵢ_neg`). `numBits` is the value of the opaque `System.Platform.getNumBits`, and both
implementations are consistent with Lean's logic, so neither `T'` nor `¬T'` is provable (argument,
not a Lean proof).
* `Int32.toISize_div_of_ne_{left,right}`, `Int32.toISize_ofInt` (h₁, h₂), `Int32.toISize_ofNat{,'}`,
  `Int32.toISize_neg_of_ne`, `Int32.ofIntLE_iSizeToInt` (h₁, h₂): hold iff `numBits = 32`
  (`Int32.toISize` is then a bijection compatible with the operations).
* `Int32.toISize_ne_minValue`: holds iff `numBits = 64`.

Run with the lean4 repo's stage1 binary: `lean checks/SIntFixedHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false

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

namespace SIntFixedHand

/-- Case split on the platform, normalize to `Int` via `toInt` with concrete sizes, then `decide`. -/
macro "isz" : tactic => `(tactic| (rcases System.Platform.numBits_eq with hnb | hnb <;>
  simp_all [← ISize.toInt_inj, ISize.toInt_ofInt, ISize.toInt_neg, ISize.toInt_ofNat, ISize.toInt_ofNat',
    ISize.toInt_div, ISize.size, ISize.toInt_minValue, Int8.toInt_toISize, Int16.toInt_toISize,
    Int32.toInt_toISize, Int64.toInt_toISize, Int8.toInt_maxValue, Int16.toInt_maxValue, Int32.toInt_maxValue,
    Int8.toInt_minValue, Int16.toInt_minValue, Int32.toInt_minValue] <;> decide))

/-- For the `numBits = 32` halves: both sides normalized to `Int.bmod _ (2^32)`. -/
macro "isz32" : tactic => `(tactic| (simp_all [← ISize.toInt_inj, ISize.toInt_ofInt, ISize.toInt_neg,
    ISize.toInt_ofNat, ISize.toInt_ofNat', ISize.toInt_div, ISize.size, ISize.toInt_minValue,
    Int32.toInt_toISize, Int32.toInt_ofInt, Int32.toInt_ofNat', Int32.toInt_ofNat, Int32.toInt_neg,
    Int32.toInt_div, Int32.size]))

/-! ## Necessary -/

-- `Int8.ofIntLE_iSizeToInt`, idx 1 (`h₁ : Int8.minValue.toInt ≤ x.toInt`) (dependent): dependent; `∀ x : ISize, -128 ≤ x.toInt` fails at `x = -129` on both platforms
theorem Int8.ofIntLE_iSizeToInt.h1 : ¬ indep% Int8.ofIntLE_iSizeToInt 1 := fun h => by
  have := @h (ISize.ofInt (-129)) (by isz); clear h; revert this; isz

-- `Int8.ofIntLE_iSizeToInt`, idx 2 (`h₂ : x.toInt ≤ Int8.maxValue.toInt`) (dependent): dependent; `∀ x : ISize, x.toInt ≤ 127` fails at `x = 128` on both platforms
theorem Int8.ofIntLE_iSizeToInt.h2 : ¬ indep% Int8.ofIntLE_iSizeToInt 2 := fun h => by
  have := @h (ISize.ofInt 128) (by isz); clear h; revert this; isz

-- `Int16.ofIntLE_iSizeToInt`, idx 1 (`h₁ : Int16.minValue.toInt ≤ x.toInt`) (dependent): dependent; `∀ x : ISize, -32768 ≤ x.toInt` fails at `x = -32769` on both platforms
theorem Int16.ofIntLE_iSizeToInt.h1 : ¬ indep% Int16.ofIntLE_iSizeToInt 1 := fun h => by
  have := @h (ISize.ofInt (-32769)) (by isz); clear h; revert this; isz

-- `Int16.ofIntLE_iSizeToInt`, idx 2 (`h₂ : x.toInt ≤ Int16.maxValue.toInt`) (dependent): dependent; `∀ x : ISize, x.toInt ≤ 32767` fails at `x = 32768` on both platforms
theorem Int16.ofIntLE_iSizeToInt.h2 : ¬ indep% Int16.ofIntLE_iSizeToInt 2 := fun h => by
  have := @h (ISize.ofInt 32768) (by isz); clear h; revert this; isz

-- `Int64.toISize_ofIntClamp`, idx 1 (`h₁ : -2 ^ 63 ≤ n`): `n = -2^63 - 1`: clamps to `Int64.minValue`; LHS/RHS toInt are `-2^63`/`2^63-1` (64-bit), `0`/`-1` (32-bit)
theorem Int64.toISize_ofIntClamp.h1 : ¬ drop% Int64.toISize_ofIntClamp 1 := fun h => by
  have := @h (-2^63-1) (by decide); clear h; revert this; isz

-- `Int8.toISize_neg_of_ne`, idx 1 (`hx : x ≠ -128`): `x = -128`: `-x = x` in Int8, but `-x.toISize = 128` on both platforms
theorem Int8.toISize_neg_of_ne.h1 : ¬ drop% Int8.toISize_neg_of_ne 1 := fun h => by
  have := @h (-128); clear h; revert this; isz

-- `Int16.toISize_neg_of_ne`, idx 1 (`hx : x ≠ -32768`): `x = -32768`: `-x = x` in Int16, but `-x.toISize = 32768` on both platforms
theorem Int16.toISize_neg_of_ne.h1 : ¬ drop% Int16.toISize_neg_of_ne 1 := fun h => by
  have := @h (-32768); clear h; revert this; isz

-- `Int8.toISize_ofInt`, idx 1 (`h₁ : Int8.minValue.toInt ≤ n`): `n = -129`: `Int8.ofInt n = 127`, `ISize.ofInt n = -129` on both platforms
theorem Int8.toISize_ofInt.h1 : ¬ drop% Int8.toISize_ofInt 1 := fun h => by
  have := @h (-129) (by decide); clear h; revert this; isz

-- `Int8.toISize_ofNat`, idx 1 (`h : n ≤ 127`): `n = 128`: LHS `-128`, RHS `128` on both platforms
theorem Int8.toISize_ofNat.h1 : ¬ drop% Int8.toISize_ofNat 1 := fun h => by
  have := @h 128; clear h; revert this; isz

-- `Int16.toISize_ofInt`, idx 1 (`h₁ : Int16.minValue.toInt ≤ n`): `n = -32769`: `Int16.ofInt n = 32767`, `ISize.ofInt n = -32769` on both platforms
theorem Int16.toISize_ofInt.h1 : ¬ drop% Int16.toISize_ofInt 1 := fun h => by
  have := @h (-32769) (by decide); clear h; revert this; isz

-- `Int16.toISize_ofNat`, idx 1 (`h : n ≤ 32767`): `n = 32768`: LHS `-32768`, RHS `32768` on both platforms
theorem Int16.toISize_ofNat.h1 : ¬ drop% Int16.toISize_ofNat 1 := fun h => by
  have := @h 32768; clear h; revert this; isz

-- `Int64.toISize_ofIntTruncate`, idx 1 (`h₁ : -2 ^ 63 ≤ n`): `n = -2^63 - 1`: clamps to `Int64.minValue`; LHS/RHS toInt are `-2^63`/`2^63-1` (64-bit), `0`/`-1` (32-bit)
theorem Int64.toISize_ofIntTruncate.h1 : ¬ drop% Int64.toISize_ofIntTruncate 1 := fun h => by
  have := @h (-2^63-1) (by decide); clear h; revert this; isz

-- `Int8.toInt_div_of_ne_left`, idx 2 (`h : a ≠ Int8.minValue`): `a = minValue`, `b = -1`: `a / b = minValue` (overflow), `tdiv` gives `128`
theorem Int8.toInt_div_of_ne_left.h2 : ¬ drop% Int8.toInt_div_of_ne_left 2 := fun h => by
  have := @h Int8.minValue (-1); clear h; revert this; decide

-- `Int16.toInt_div_of_ne_left`, idx 2 (`h : a ≠ Int16.minValue`): `a = minValue`, `b = -1`: `a / b = minValue` (overflow), `tdiv` gives `32768`
theorem Int16.toInt_div_of_ne_left.h2 : ¬ drop% Int16.toInt_div_of_ne_left 2 := fun h => by
  have := @h Int16.minValue (-1); clear h; revert this; decide

-- `Int32.toInt_div_of_ne_left`, idx 2 (`h : a ≠ Int32.minValue`): `a = minValue`, `b = -1`: `a / b = minValue` (overflow), `tdiv` gives `2147483648`
theorem Int32.toInt_div_of_ne_left.h2 : ¬ drop% Int32.toInt_div_of_ne_left 2 := fun h => by
  have := @h Int32.minValue (-1); clear h; revert this; decide

-- `Int64.toInt_div_of_ne_left`, idx 2 (`h : a ≠ Int64.minValue`): `a = minValue`, `b = -1`: `a / b = minValue` (overflow), `tdiv` gives `9223372036854775808`
theorem Int64.toInt_div_of_ne_left.h2 : ¬ drop% Int64.toInt_div_of_ne_left 2 := fun h => by
  have := @h Int64.minValue (-1); clear h; revert this; decide

-- `Int8.toInt_div_of_ne_right`, idx 2 (`h : b ≠ -1`): `a = minValue`, `b = -1`: `a / b = minValue` (overflow), `tdiv` gives `128`
theorem Int8.toInt_div_of_ne_right.h2 : ¬ drop% Int8.toInt_div_of_ne_right 2 := fun h => by
  have := @h Int8.minValue (-1); clear h; revert this; decide

-- `Int16.toInt_div_of_ne_right`, idx 2 (`h : b ≠ -1`): `a = minValue`, `b = -1`: `a / b = minValue` (overflow), `tdiv` gives `32768`
theorem Int16.toInt_div_of_ne_right.h2 : ¬ drop% Int16.toInt_div_of_ne_right 2 := fun h => by
  have := @h Int16.minValue (-1); clear h; revert this; decide

-- `Int32.toInt_div_of_ne_right`, idx 2 (`h : b ≠ -1`): `a = minValue`, `b = -1`: `a / b = minValue` (overflow), `tdiv` gives `2147483648`
theorem Int32.toInt_div_of_ne_right.h2 : ¬ drop% Int32.toInt_div_of_ne_right 2 := fun h => by
  have := @h Int32.minValue (-1); clear h; revert this; decide

-- `Int64.toInt_div_of_ne_right`, idx 2 (`h : b ≠ -1`): `a = minValue`, `b = -1`: `a / b = minValue` (overflow), `tdiv` gives `9223372036854775808`
theorem Int64.toInt_div_of_ne_right.h2 : ¬ drop% Int64.toInt_div_of_ne_right 2 := fun h => by
  have := @h Int64.minValue (-1); clear h; revert this; decide

-- `Int8.toInt16_div_of_ne_left`, idx 2 (`ha : a ≠ Int8.minValue`): `a = minValue`, `b = -1`: LHS `-128`, RHS `128` (no overflow in Int16)
theorem Int8.toInt16_div_of_ne_left.h2 : ¬ drop% Int8.toInt16_div_of_ne_left 2 := fun h => by
  have := @h Int8.minValue (-1); clear h; revert this; decide

-- `Int8.toInt32_div_of_ne_left`, idx 2 (`ha : a ≠ Int8.minValue`): `a = minValue`, `b = -1`: LHS `-128`, RHS `128` (no overflow in Int32)
theorem Int8.toInt32_div_of_ne_left.h2 : ¬ drop% Int8.toInt32_div_of_ne_left 2 := fun h => by
  have := @h Int8.minValue (-1); clear h; revert this; decide

-- `Int8.toInt64_div_of_ne_left`, idx 2 (`ha : a ≠ Int8.minValue`): `a = minValue`, `b = -1`: LHS `-128`, RHS `128` (no overflow in Int64)
theorem Int8.toInt64_div_of_ne_left.h2 : ¬ drop% Int8.toInt64_div_of_ne_left 2 := fun h => by
  have := @h Int8.minValue (-1); clear h; revert this; decide

-- `Int8.toISize_div_of_ne_left`, idx 2 (`ha : a ≠ Int8.minValue`): `a = minValue`, `b = -1`: LHS `-128`, RHS `128` (no overflow in ISize on either platform)
theorem Int8.toISize_div_of_ne_left.h2 : ¬ drop% Int8.toISize_div_of_ne_left 2 := fun h => by
  have := @h Int8.minValue (-1); clear h; revert this; isz

-- `Int16.toInt32_div_of_ne_left`, idx 2 (`ha : a ≠ Int16.minValue`): `a = minValue`, `b = -1`: LHS `-32768`, RHS `32768` (no overflow in Int32)
theorem Int16.toInt32_div_of_ne_left.h2 : ¬ drop% Int16.toInt32_div_of_ne_left 2 := fun h => by
  have := @h Int16.minValue (-1); clear h; revert this; decide

-- `Int16.toInt64_div_of_ne_left`, idx 2 (`ha : a ≠ Int16.minValue`): `a = minValue`, `b = -1`: LHS `-32768`, RHS `32768` (no overflow in Int64)
theorem Int16.toInt64_div_of_ne_left.h2 : ¬ drop% Int16.toInt64_div_of_ne_left 2 := fun h => by
  have := @h Int16.minValue (-1); clear h; revert this; decide

-- `Int16.toISize_div_of_ne_left`, idx 2 (`ha : a ≠ Int16.minValue`): `a = minValue`, `b = -1`: LHS `-32768`, RHS `32768` (no overflow in ISize on either platform)
theorem Int16.toISize_div_of_ne_left.h2 : ¬ drop% Int16.toISize_div_of_ne_left 2 := fun h => by
  have := @h Int16.minValue (-1); clear h; revert this; isz

-- `Int32.toInt64_div_of_ne_left`, idx 2 (`ha : a ≠ Int32.minValue`): `a = minValue`, `b = -1`: LHS `-2147483648`, RHS `2147483648` (no overflow in Int64)
theorem Int32.toInt64_div_of_ne_left.h2 : ¬ drop% Int32.toInt64_div_of_ne_left 2 := fun h => by
  have := @h Int32.minValue (-1); clear h; revert this; decide

-- `Int8.toInt16_div_of_ne_right`, idx 2 (`hb : b ≠ -1`): `a = minValue`, `b = -1`: LHS `-128`, RHS `128` (no overflow in Int16)
theorem Int8.toInt16_div_of_ne_right.h2 : ¬ drop% Int8.toInt16_div_of_ne_right 2 := fun h => by
  have := @h Int8.minValue (-1); clear h; revert this; decide

-- `Int8.toInt32_div_of_ne_right`, idx 2 (`hb : b ≠ -1`): `a = minValue`, `b = -1`: LHS `-128`, RHS `128` (no overflow in Int32)
theorem Int8.toInt32_div_of_ne_right.h2 : ¬ drop% Int8.toInt32_div_of_ne_right 2 := fun h => by
  have := @h Int8.minValue (-1); clear h; revert this; decide

-- `Int8.toInt64_div_of_ne_right`, idx 2 (`hb : b ≠ -1`): `a = minValue`, `b = -1`: LHS `-128`, RHS `128` (no overflow in Int64)
theorem Int8.toInt64_div_of_ne_right.h2 : ¬ drop% Int8.toInt64_div_of_ne_right 2 := fun h => by
  have := @h Int8.minValue (-1); clear h; revert this; decide

-- `Int8.toISize_div_of_ne_right`, idx 2 (`hb : b ≠ -1`): `a = minValue`, `b = -1`: LHS `-128`, RHS `128` (no overflow in ISize on either platform)
theorem Int8.toISize_div_of_ne_right.h2 : ¬ drop% Int8.toISize_div_of_ne_right 2 := fun h => by
  have := @h Int8.minValue (-1); clear h; revert this; isz

-- `Int16.toInt32_div_of_ne_right`, idx 2 (`hb : b ≠ -1`): `a = minValue`, `b = -1`: LHS `-32768`, RHS `32768` (no overflow in Int32)
theorem Int16.toInt32_div_of_ne_right.h2 : ¬ drop% Int16.toInt32_div_of_ne_right 2 := fun h => by
  have := @h Int16.minValue (-1); clear h; revert this; decide

-- `Int16.toInt64_div_of_ne_right`, idx 2 (`hb : b ≠ -1`): `a = minValue`, `b = -1`: LHS `-32768`, RHS `32768` (no overflow in Int64)
theorem Int16.toInt64_div_of_ne_right.h2 : ¬ drop% Int16.toInt64_div_of_ne_right 2 := fun h => by
  have := @h Int16.minValue (-1); clear h; revert this; decide

-- `Int16.toISize_div_of_ne_right`, idx 2 (`hb : b ≠ -1`): `a = minValue`, `b = -1`: LHS `-32768`, RHS `32768` (no overflow in ISize on either platform)
theorem Int16.toISize_div_of_ne_right.h2 : ¬ drop% Int16.toISize_div_of_ne_right 2 := fun h => by
  have := @h Int16.minValue (-1); clear h; revert this; isz

-- `Int32.toInt64_div_of_ne_right`, idx 2 (`hb : b ≠ -1`): `a = minValue`, `b = -1`: LHS `-2147483648`, RHS `2147483648` (no overflow in Int64)
theorem Int32.toInt64_div_of_ne_right.h2 : ¬ drop% Int32.toInt64_div_of_ne_right 2 := fun h => by
  have := @h Int32.minValue (-1); clear h; revert this; decide

-- `Int16.sub_nonneg_of_le`, idx 2 (`hb : 0 ≤ b`): `a = maxValue`, `b = -1`: `a - b` wraps to `minValue < 0`
theorem Int16.sub_nonneg_of_le.h2 : ¬ drop% Int16.sub_nonneg_of_le 2 := fun h => by
  have := @h Int16.maxValue (-1) (by decide); clear h; revert this; decide

-- `Int32.sub_nonneg_of_le`, idx 2 (`hb : 0 ≤ b`): `a = maxValue`, `b = -1`: `a - b` wraps to `minValue < 0`
theorem Int32.sub_nonneg_of_le.h2 : ¬ drop% Int32.sub_nonneg_of_le 2 := fun h => by
  have := @h Int32.maxValue (-1) (by decide); clear h; revert this; decide

-- `Int64.sub_nonneg_of_le`, idx 2 (`hb : 0 ≤ b`): `a = maxValue`, `b = -1`: `a - b` wraps to `minValue < 0`
theorem Int64.sub_nonneg_of_le.h2 : ¬ drop% Int64.sub_nonneg_of_le 2 := fun h => by
  have := @h Int64.maxValue (-1) (by decide); clear h; revert this; decide

-- `Int8.toNatClampNeg_sub_of_le`, idx 3 (`hab : b ≤ a`): `a = minValue`, `b = 1`: LHS `maxValue.toNatClampNeg`, RHS `0 - 1 = 0`
theorem Int8.toNatClampNeg_sub_of_le.h3 : ¬ drop% Int8.toNatClampNeg_sub_of_le 3 := fun h => by
  have := @h Int8.minValue 1 (by decide); clear h; revert this; decide

-- `Int16.toNatClampNeg_sub_of_le`, idx 3 (`hab : b ≤ a`): `a = minValue`, `b = 1`: LHS `maxValue.toNatClampNeg`, RHS `0 - 1 = 0`
theorem Int16.toNatClampNeg_sub_of_le.h3 : ¬ drop% Int16.toNatClampNeg_sub_of_le 3 := fun h => by
  have := @h Int16.minValue 1 (by decide); clear h; revert this; decide

-- `Int32.toNatClampNeg_sub_of_le`, idx 3 (`hab : b ≤ a`): `a = minValue`, `b = 1`: LHS `maxValue.toNatClampNeg`, RHS `0 - 1 = 0`
theorem Int32.toNatClampNeg_sub_of_le.h3 : ¬ drop% Int32.toNatClampNeg_sub_of_le 3 := fun h => by
  have := @h Int32.minValue 1 (by decide); clear h; revert this; decide

-- `Int64.toNatClampNeg_sub_of_le`, idx 3 (`hab : b ≤ a`): `a = minValue`, `b = 1`: LHS `maxValue.toNatClampNeg`, RHS `0 - 1 = 0`
theorem Int64.toNatClampNeg_sub_of_le.h3 : ¬ drop% Int64.toNatClampNeg_sub_of_le 3 := fun h => by
  have := @h Int64.minValue 1 (by decide); clear h; revert this; decide

-- `Int8.toInt_sub_of_le`, idx 3 (`h : b ≤ a`): `a = minValue`, `b = 1`: `a - b` wraps to `maxValue`
theorem Int8.toInt_sub_of_le.h3 : ¬ drop% Int8.toInt_sub_of_le 3 := fun h => by
  have := @h Int8.minValue 1 (by decide); clear h; revert this; decide

-- `Int16.toInt_sub_of_le`, idx 2 (`hb : 0 ≤ b`): `a = maxValue`, `b = -1`: `a - b` wraps to `minValue`
theorem Int16.toInt_sub_of_le.h2 : ¬ drop% Int16.toInt_sub_of_le 2 := fun h => by
  have := @h Int16.maxValue (-1) (by decide); clear h; revert this; decide

-- `Int16.toInt_sub_of_le`, idx 3 (`h : b ≤ a`): `a = minValue`, `b = 1`: `a - b` wraps to `maxValue`
theorem Int16.toInt_sub_of_le.h3 : ¬ drop% Int16.toInt_sub_of_le 3 := fun h => by
  have := @h Int16.minValue 1 (by decide); clear h; revert this; decide

-- `Int32.toInt_sub_of_le`, idx 2 (`hb : 0 ≤ b`): `a = maxValue`, `b = -1`: `a - b` wraps to `minValue`
theorem Int32.toInt_sub_of_le.h2 : ¬ drop% Int32.toInt_sub_of_le 2 := fun h => by
  have := @h Int32.maxValue (-1) (by decide); clear h; revert this; decide

-- `Int32.toInt_sub_of_le`, idx 3 (`h : b ≤ a`): `a = minValue`, `b = 1`: `a - b` wraps to `maxValue`
theorem Int32.toInt_sub_of_le.h3 : ¬ drop% Int32.toInt_sub_of_le 3 := fun h => by
  have := @h Int32.minValue 1 (by decide); clear h; revert this; decide

-- `Int64.toInt_sub_of_le`, idx 2 (`hb : 0 ≤ b`): `a = maxValue`, `b = -1`: `a - b` wraps to `minValue`
theorem Int64.toInt_sub_of_le.h2 : ¬ drop% Int64.toInt_sub_of_le 2 := fun h => by
  have := @h Int64.maxValue (-1) (by decide); clear h; revert this; decide

-- `Int64.toInt_sub_of_le`, idx 3 (`h : b ≤ a`): `a = minValue`, `b = 1`: `a - b` wraps to `maxValue`
theorem Int64.toInt_sub_of_le.h3 : ¬ drop% Int64.toInt_sub_of_le 3 := fun h => by
  have := @h Int64.minValue 1 (by decide); clear h; revert this; decide

-- `Int8.sub_le`, idx 3 (`hab : b ≤ a`): `a = minValue`, `b = 1`: `a - b` wraps to `maxValue`
theorem Int8.sub_le.h3 : ¬ drop% Int8.sub_le 3 := fun h => by
  have := @h Int8.minValue 1 (by decide); clear h; revert this; decide

-- `Int16.sub_le`, idx 3 (`hab : b ≤ a`): `a = minValue`, `b = 1`: `a - b` wraps to `maxValue`
theorem Int16.sub_le.h3 : ¬ drop% Int16.sub_le 3 := fun h => by
  have := @h Int16.minValue 1 (by decide); clear h; revert this; decide

-- `Int32.sub_le`, idx 3 (`hab : b ≤ a`): `a = minValue`, `b = 1`: `a - b` wraps to `maxValue`
theorem Int32.sub_le.h3 : ¬ drop% Int32.sub_le 3 := fun h => by
  have := @h Int32.minValue 1 (by decide); clear h; revert this; decide

-- `Int64.sub_le`, idx 3 (`hab : b ≤ a`): `a = minValue`, `b = 1`: `a - b` wraps to `maxValue`
theorem Int64.sub_le.h3 : ¬ drop% Int64.sub_le 3 := fun h => by
  have := @h Int64.minValue 1 (by decide); clear h; revert this; decide

-- `Int8.sub_lt`, idx 3 (`hab : b ≤ a`): `a = minValue`, `b = 1`: `a - b` wraps to `maxValue`
theorem Int8.sub_lt.h3 : ¬ drop% Int8.sub_lt 3 := fun h => by
  have := @h Int8.minValue 1 (by decide); clear h; revert this; decide

-- `Int16.sub_lt`, idx 3 (`hab : b ≤ a`): `a = minValue`, `b = 1`: `a - b` wraps to `maxValue`
theorem Int16.sub_lt.h3 : ¬ drop% Int16.sub_lt 3 := fun h => by
  have := @h Int16.minValue 1 (by decide); clear h; revert this; decide

-- `Int32.sub_lt`, idx 3 (`hab : b ≤ a`): `a = minValue`, `b = 1`: `a - b` wraps to `maxValue`
theorem Int32.sub_lt.h3 : ¬ drop% Int32.sub_lt 3 := fun h => by
  have := @h Int32.minValue 1 (by decide); clear h; revert this; decide

-- `Int64.sub_lt`, idx 3 (`hab : b ≤ a`): `a = minValue`, `b = 1`: `a - b` wraps to `maxValue`
theorem Int64.sub_lt.h3 : ¬ drop% Int64.sub_lt 3 := fun h => by
  have := @h Int64.minValue 1 (by decide); clear h; revert this; decide

-- `Int8.ofInt_tmod`, idx 5 (`hb₂ : b ≤ Int8.maxValue.toInt`): `a = 127`, `b = 129`: `ofInt b = -127`, so RHS `127 % -127 = 0`, LHS `127`
theorem Int8.ofInt_tmod.h5 : ¬ drop% Int8.ofInt_tmod 5 := fun h => by
  have := @h 127 129 (by decide) (by decide) (by decide); clear h; revert this; decide

-- `Int16.ofInt_tmod`, idx 5 (`hb₂ : b ≤ Int16.maxValue.toInt`): `a = 32767`, `b = 32769`: `ofInt b = -32767`, so RHS `32767 % -32767 = 0`, LHS `32767`
theorem Int16.ofInt_tmod.h5 : ¬ drop% Int16.ofInt_tmod 5 := fun h => by
  have := @h 32767 32769 (by decide) (by decide) (by decide); clear h; revert this; decide

-- `Int32.ofInt_tmod`, idx 5 (`hb₂ : b ≤ Int32.maxValue.toInt`): `a = 2147483647`, `b = 2147483649`: `ofInt b = -2147483647`, so RHS `2147483647 % -2147483647 = 0`, LHS `2147483647`
theorem Int32.ofInt_tmod.h5 : ¬ drop% Int32.ofInt_tmod 5 := fun h => by
  have := @h 2147483647 2147483649 (by decide) (by decide) (by decide); clear h; revert this; decide

-- `Int64.ofInt_tmod`, idx 5 (`hb₂ : b ≤ Int64.maxValue.toInt`): `a = 9223372036854775807`, `b = 9223372036854775809`: `ofInt b = -9223372036854775807`, so RHS `9223372036854775807 % -9223372036854775807 = 0`, LHS `9223372036854775807`
theorem Int64.ofInt_tmod.h5 : ¬ drop% Int64.ofInt_tmod 5 := fun h => by
  have := @h 9223372036854775807 9223372036854775809 (by decide) (by decide) (by decide); clear h; revert this; decide

/-! ## Independent: kernel-checked halves (support lemmas, not verdicts) -/

-- `Int32.ofIntLE_iSizeToInt`, idx 1 (`h₁ : Int32.minValue.toInt ≤ x.toInt`) (dependent): dependent; `∀ x : ISize, -2^31 ≤ x.toInt` holds iff `numBits = 32`; fails at `x = -2^31 - 1` when `numBits = 64`
theorem Int32.ofIntLE_iSizeToInt.h1_pos : System.Platform.numBits = 32 → indep% Int32.ofIntLE_iSizeToInt 1 := by
  intro hnb x _; have := x.two_pow_numBits_le_toInt; simp_all
theorem Int32.ofIntLE_iSizeToInt.h1_neg : System.Platform.numBits = 64 → ¬ indep% Int32.ofIntLE_iSizeToInt 1 := fun hnb h => by
  have := @h (ISize.ofInt (-2^31-1)) (by isz); clear h; revert this; isz

-- `Int32.ofIntLE_iSizeToInt`, idx 2 (`h₂ : x.toInt ≤ Int32.maxValue.toInt`) (dependent): dependent; `∀ x : ISize, x.toInt ≤ 2^31 - 1` holds iff `numBits = 32`; fails at `x = 2^31` when `numBits = 64`
theorem Int32.ofIntLE_iSizeToInt.h2_pos : System.Platform.numBits = 32 → indep% Int32.ofIntLE_iSizeToInt 2 := by
  intro hnb x _; have := x.toInt_lt_two_pow_numBits; simp_all [Int32.toInt_maxValue]; omega
theorem Int32.ofIntLE_iSizeToInt.h2_neg : System.Platform.numBits = 64 → ¬ indep% Int32.ofIntLE_iSizeToInt 2 := fun hnb h => by
  have := @h (ISize.ofInt (2^31)) (by isz); clear h; revert this; isz

-- `Int32.toISize_neg_of_ne`, idx 1 (`hx : x ≠ -2147483648`): T' holds iff `numBits = 32` (`Int32.toISize` is then a ring isomorphism); fails at `x = -2^31` when `numBits = 64` (LHS `-2^31`, RHS `2^31`)
theorem Int32.toISize_neg_of_ne.h1_pos : System.Platform.numBits = 32 → drop% Int32.toISize_neg_of_ne 1 := by
  intro hnb; intros; isz32
theorem Int32.toISize_neg_of_ne.h1_neg : System.Platform.numBits = 64 → ¬ drop% Int32.toISize_neg_of_ne 1 := fun hnb h => by
  have := @h (-2147483648); clear h; revert this; isz

-- `Int32.toISize_ofInt`, idx 1 (`h₁ : Int32.minValue.toInt ≤ n`): T' holds iff `numBits = 32` (both sides are `n` reduced mod `2^32` then); fails at `n = -2^31 - 1` when `numBits = 64`
theorem Int32.toISize_ofInt.h1_pos : System.Platform.numBits = 32 → drop% Int32.toISize_ofInt 1 := by
  intro hnb; intros; isz32
theorem Int32.toISize_ofInt.h1_neg : System.Platform.numBits = 64 → ¬ drop% Int32.toISize_ofInt 1 := fun hnb h => by
  have := @h (-2^31-1) (by decide); clear h; revert this; isz

-- `Int32.toISize_ofInt`, idx 2 (`h₂ : n ≤ Int32.maxValue.toInt`): T' holds iff `numBits = 32` (both sides are `n` reduced mod `2^32` then); fails at `n = 2^31` when `numBits = 64`
theorem Int32.toISize_ofInt.h2_pos : System.Platform.numBits = 32 → drop% Int32.toISize_ofInt 2 := by
  intro hnb; intros; isz32
theorem Int32.toISize_ofInt.h2_neg : System.Platform.numBits = 64 → ¬ drop% Int32.toISize_ofInt 2 := fun hnb h => by
  have := @h (2^31) (by decide); clear h; revert this; isz

-- `Int32.toISize_ofNat'`, idx 1 (`h : ↑n ≤ Int32.maxValue.toInt`): T' holds iff `numBits = 32` (both sides are `n` reduced mod `2^32` then); fails at `n = 2^31` when `numBits = 64` (LHS `-2^31`, RHS `2^31`)
theorem Int32.toISize_ofNat'.h1_pos : System.Platform.numBits = 32 → drop% Int32.toISize_ofNat' 1 := by
  intro hnb; intros; isz32
theorem Int32.toISize_ofNat'.h1_neg : System.Platform.numBits = 64 → ¬ drop% Int32.toISize_ofNat' 1 := fun hnb h => by
  have := @h (2^31); clear h; revert this; isz

-- `Int32.toISize_ofNat`, idx 1 (`h : n ≤ 2147483647`): T' holds iff `numBits = 32` (both sides are `n` reduced mod `2^32` then); fails at `n = 2^31` when `numBits = 64` (LHS `-2^31`, RHS `2^31`)
theorem Int32.toISize_ofNat.h1_pos : System.Platform.numBits = 32 → drop% Int32.toISize_ofNat 1 := by
  intro hnb; intros; isz32
theorem Int32.toISize_ofNat.h1_neg : System.Platform.numBits = 64 → ¬ drop% Int32.toISize_ofNat 1 := fun hnb h => by
  have := @h (2^31); clear h; revert this; isz

-- `Int32.toISize_ne_minValue`, idx 1 (`ha : a ≠ Int32.minValue`): T' (`∀ a : Int32, a.toISize ≠ ISize.minValue`) holds iff `numBits = 64` (`a.toInt ≥ -2^31 > -2^63`); fails at `a = minValue` when `numBits = 32`
theorem Int32.toISize_ne_minValue.h1_pos : System.Platform.numBits = 64 → drop% Int32.toISize_ne_minValue 1 := by
  intro hnb a; have := a.le_toInt; rw [ne_eq, ← ISize.toInt_inj, ISize.toInt_minValue, Int32.toInt_toISize, hnb]; omega
theorem Int32.toISize_ne_minValue.h1_neg : System.Platform.numBits = 32 → ¬ drop% Int32.toISize_ne_minValue 1 := fun hnb h => by
  have := @h Int32.minValue; clear h; revert this; isz

-- `Int32.toISize_div_of_ne_left`, idx 2 (`ha : a ≠ Int32.minValue`): T' holds iff `numBits = 32` (`Int32.toISize` is then a ring isomorphism compatible with `/`); fails at `a = minValue`, `b = -1` when `numBits = 64` (LHS `-2^31`, RHS `2^31`)
theorem Int32.toISize_div_of_ne_left.h2_pos : System.Platform.numBits = 32 → drop% Int32.toISize_div_of_ne_left 2 := by
  intro hnb; intros; isz32
theorem Int32.toISize_div_of_ne_left.h2_neg : System.Platform.numBits = 64 → ¬ drop% Int32.toISize_div_of_ne_left 2 := fun hnb h => by
  have := @h Int32.minValue (-1); clear h; revert this; isz

-- `Int32.toISize_div_of_ne_right`, idx 2 (`hb : b ≠ -1`): T' holds iff `numBits = 32` (`Int32.toISize` is then a ring isomorphism compatible with `/`); fails at `a = minValue`, `b = -1` when `numBits = 64` (LHS `-2^31`, RHS `2^31`)
theorem Int32.toISize_div_of_ne_right.h2_pos : System.Platform.numBits = 32 → drop% Int32.toISize_div_of_ne_right 2 := by
  intro hnb; intros; isz32
theorem Int32.toISize_div_of_ne_right.h2_neg : System.Platform.numBits = 64 → ¬ drop% Int32.toISize_div_of_ne_right 2 := fun hnb h => by
  have := @h Int32.minValue (-1); clear h; revert this; isz

end SIntFixedHand
