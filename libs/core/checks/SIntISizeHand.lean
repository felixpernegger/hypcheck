import Lean

/-!
Hand pass over cluster `SIntISize` (hand7): the 150 unresolved hypotheses of `ISize.*` lemmas in
`Init.Data.SInt.Lemmas` (44 of them dependent). For hypothesis `hᵢ` of theorem `T` this file
proves `¬T'` (necessary) or, for a dependent hypothesis, `¬∀ indep, Hᵢ`.

140 necessary, 0 removable, 10 independent (neither `T'` nor `¬T'` provable).

`drop% T i` elaborates to `T'` (`T` without binder `i`) and `indep% T i` to `∀ indep, Hᵢ` (all
independent binders), read off the library rather than retyped; `check_hand.py` compares them
with its own construction. Each refutation instantiates the hypothetical `T'` at the witness and
evaluates with `isz`: a case split on `System.Platform.numBits_eq` (`numBits` is opaque, so the
kernel can't compute it), then `simp_all` down to `Int` arithmetic (`bmod`, `tdiv`, `tmod`) with
concrete sizes. Every witness refutes `T'` on both platforms; several are platform-dependent terms
(`ISize.minValue.toInt - 1`, `ISize.maxValue.toInt + 1`, `ISize.minValue`), the others are
literals that wrap on both platforms (`2^64`, `2^64 + 1`, `-2^63 - 1`, ...).

Necessary (140): the order lemmas with `0`/`1`; the `0 ≤ x` hypotheses with `-1`; the bound
hypotheses of `ofInt`/`ofNat`/`ofIntClamp` lemmas with a value just outside the range or a
wrapping literal; `a ≠ minValue`/`b ≠ -1` of `toInt_div_of_ne_*` with `minValue / -1`; the
`sub` lemmas with `maxValue - (-1)` and `minValue - 1`; the 44 dependent `ofIntLE` bounds, whose
`∀ indep, Hᵢ` fails just outside the range.

Independent (10, in `runs/hand7/SIntISize_independent.jsonl`): `T'` (or `∀ indep, Hᵢ`) holds when
`numBits` is one value and fails for the other. Both halves are proved below as support lemmas
(`T.hᵢ_pos : numBits = k → T'`, `T.hᵢ_neg : numBits = k' → ¬T'`). `numBits` is the value of the
opaque `System.Platform.getNumBits : Unit → {n // n = 32 ∨ n = 64}`, and both implementations are
consistent with Lean's logic, so neither `T'` nor `¬T'` is provable (argument, not a Lean proof).
All of them concern `ISize.toInt64`, which is injective and a homomorphism when `numBits = 64`:
* hold iff `numBits = 64`: `toInt64_ofInt` (h₁, h₂), `toInt64_ofNat'`, `toInt64_ofNat`,
  `toInt64_neg_of_ne`, `toInt64_div_of_ne_left`, `toInt64_div_of_ne_right`, and the dependent
  `ofIntLE_int64ToInt` (h₁, h₂: every `Int64` is in `ISize` range);
* holds iff `numBits = 32`: `toInt64_ne_minValue` (no `ISize` reaches `Int64.minValue`).

Run with the lean4 repo's stage1 binary: `lean checks/SIntISizeHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

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

namespace SIntISizeHand

theorem clampInt (n : Int) : (ISize.ofIntClamp n).toInt =
    if ISize.minValue.toInt ≤ n then (if n ≤ ISize.maxValue.toInt then n else ISize.maxValue.toInt)
    else ISize.minValue.toInt := by
  unfold ISize.ofIntClamp
  split
  · split <;> simp [ISize.toInt_ofIntLE]
  · rfl

theorem tu1 : ISize.toUSize 1 = 1 := rfl
theorem tu0 : ISize.toUSize 0 = 0 := rfl

/-- Normalize everything to `Int`/`Nat` arithmetic, given `hnb : numBits = k` in context. -/
macro "iszs" : tactic => `(tactic| simp_all [ISize.size, ← ISize.toInt_inj, ISize.toInt_ofInt,
    ISize.toInt_ofNat', ISize.toInt_ofNat, ISize.toInt_minValue, ISize.toInt_maxValue,
    ISize.le_iff_toInt_le, ISize.lt_iff_toInt_lt, ISize.toInt_neg, ISize.toInt_div, ISize.toInt_sub,
    ISize.toInt_add, ISize.toInt_mod, clampInt, ISize.toNatClampNeg, ← Int64.toInt_inj, Int64.toInt_ofInt,
    Int64.toInt_ofNat', Int64.toInt_ofNat, Int64.size, Int64.toInt_neg, Int64.toInt_div, Int64.toInt_minValue,
    ← Int8.toInt_inj, ← Int16.toInt_inj, ← Int32.toInt_inj, ISize.toInt_toInt8, ISize.toInt_toInt16,
    ISize.toInt_toInt32, ISize.toInt_toInt64, Int8.toInt_ofInt, Int16.toInt_ofInt, Int32.toInt_ofInt,
    Int8.size, Int16.size, Int32.size, ← BitVec.toInt_inj, BitVec.toInt_ofInt, ISize.toInt_toBitVec,
    ISize.toUSize_ofNat, USize.le_iff_toNat_le, USize.size, ISize.toNat_toBitVec, ISize.toUSize_ofNat',
    USize.toNat_ofNat', tu0, tu1, BitVec.toInt_ofNat', Int64.toInt_maxValue, -ISize.toNat_toInt])

/-- Case split on the platform, then `iszs`. -/
macro "isz" : tactic => `(tactic| (rcases System.Platform.numBits_eq with hnb | hnb <;> iszs))

/-! ## Necessary -/

-- `ISize.le_antisymm`, idx 2 (`a : a ≤ b`): `a = 1`, `b = 0`
theorem ISize.le_antisymm.h2 : ¬ drop% ISize.le_antisymm 2 := fun h => by
  have := @h 1 0 (by isz); clear h; revert this; isz

-- `ISize.le_antisymm`, idx 3 (`a : b ≤ a`): `a = 0`, `b = 1`
theorem ISize.le_antisymm.h3 : ¬ drop% ISize.le_antisymm 3 := fun h => by
  have := @h 0 1 (by isz); clear h; revert this; isz

-- `ISize.le_of_eq`, idx 2 (`a : a = b`): `a = 1`, `b = 0`: `1 ≤ 0` fails
theorem ISize.le_of_eq.h2 : ¬ drop% ISize.le_of_eq 2 := fun h => by
  have := @h 1 0; clear h; revert this; isz

-- `ISize.le_of_lt`, idx 2 (`a : a < b`): `a = 1`, `b = 0`
theorem ISize.le_of_lt.h2 : ¬ drop% ISize.le_of_lt 2 := fun h => by
  have := @h 1 0; clear h; revert this; isz

-- `ISize.le_trans`, idx 3 (`a : a ≤ b`): `a = 1`, `b = 0`, `c = 0`
theorem ISize.le_trans.h3 : ¬ drop% ISize.le_trans 3 := fun h => by
  have := @h 1 0 0 (by isz); clear h; revert this; isz

-- `ISize.le_trans`, idx 4 (`a : b ≤ c`): `a = 1`, `b = 1`, `c = 0`
theorem ISize.le_trans.h4 : ¬ drop% ISize.le_trans 4 := fun h => by
  have := @h 1 1 0 (by isz); clear h; revert this; isz

-- `ISize.lt_asymm`, idx 2 (`a : a < b`): `a = 1`, `b = 0`: `b < a` holds
theorem ISize.lt_asymm.h2 : ¬ drop% ISize.lt_asymm 2 := fun h => by
  have := @h 1 0; clear h; revert this; isz

-- `ISize.lt_of_le_of_lt`, idx 3 (`a : a ≤ b`): `a = 1`, `b = 0`, `c = 1`
theorem ISize.lt_of_le_of_lt.h3 : ¬ drop% ISize.lt_of_le_of_lt 3 := fun h => by
  have := @h 1 0 1 (by isz); clear h; revert this; isz

-- `ISize.lt_of_le_of_ne`, idx 2 (`a : a ≤ b`): `a = 1`, `b = 0`
theorem ISize.lt_of_le_of_ne.h2 : ¬ drop% ISize.lt_of_le_of_ne 2 := fun h => by
  have := @h 1 0 (by isz); clear h; revert this; isz

-- `ISize.lt_of_lt_of_le`, idx 4 (`a : b ≤ c`): `a = 0`, `b = 1`, `c = 0`
theorem ISize.lt_of_lt_of_le.h4 : ¬ drop% ISize.lt_of_lt_of_le 4 := fun h => by
  have := @h 0 1 0 (by isz); clear h; revert this; isz

-- `ISize.lt_or_eq_of_le`, idx 2 (`a : a ≤ b`): `a = 1`, `b = 0`
theorem ISize.lt_or_eq_of_le.h2 : ¬ drop% ISize.lt_or_eq_of_le 2 := fun h => by
  have := @h 1 0; clear h; revert this; isz

-- `ISize.lt_trans`, idx 3 (`a : a < b`): `a = 1`, `b = 0`, `c = 1`
theorem ISize.lt_trans.h3 : ¬ drop% ISize.lt_trans 3 := fun h => by
  have := @h 1 0 1 (by isz); clear h; revert this; isz

-- `ISize.lt_trans`, idx 4 (`a : b < c`): `a = 0`, `b = 1`, `c = 0`
theorem ISize.lt_trans.h4 : ¬ drop% ISize.lt_trans 4 := fun h => by
  have := @h 0 1 0 (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_eq_ofInt`, idx 1 (`h₁ : ISize.minValue.toInt ≤ n`) (dependent): dependent; `∀ n, n ≤ maxValue.toInt → minValue.toInt ≤ n` fails at `n = minValue.toInt - 1`
theorem ISize.ofIntLE_eq_ofInt.h1 : ¬ indep% ISize.ofIntLE_eq_ofInt 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_eq_ofInt`, idx 2 (`h₂ : n ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ n, minValue.toInt ≤ n → n ≤ maxValue.toInt` fails at `n = maxValue.toInt + 1`
theorem ISize.ofIntLE_eq_ofInt.h2 : ¬ indep% ISize.ofIntLE_eq_ofInt 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_eq_ofIntClamp`, idx 1 (`h₁ : ISize.minValue.toInt ≤ x`) (dependent): dependent; `∀ n, n ≤ maxValue.toInt → minValue.toInt ≤ n` fails at `n = minValue.toInt - 1`
theorem ISize.ofIntLE_eq_ofIntClamp.h1 : ¬ indep% ISize.ofIntLE_eq_ofIntClamp 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_eq_ofIntClamp`, idx 2 (`h₂ : x ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ n, minValue.toInt ≤ n → n ≤ maxValue.toInt` fails at `n = maxValue.toInt + 1`
theorem ISize.ofIntLE_eq_ofIntClamp.h2 : ¬ indep% ISize.ofIntLE_eq_ofIntClamp 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_eq_ofIntTruncate`, idx 1 (`h₁ : ISize.minValue.toInt ≤ x`) (dependent): dependent; `∀ n, n ≤ maxValue.toInt → minValue.toInt ≤ n` fails at `n = minValue.toInt - 1`
theorem ISize.ofIntLE_eq_ofIntTruncate.h1 : ¬ indep% ISize.ofIntLE_eq_ofIntTruncate 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_eq_ofIntTruncate`, idx 2 (`h₂ : x ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ n, minValue.toInt ≤ n → n ≤ maxValue.toInt` fails at `n = maxValue.toInt + 1`
theorem ISize.ofIntLE_eq_ofIntTruncate.h2 : ¬ indep% ISize.ofIntLE_eq_ofIntTruncate 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toBitVec_ofIntLE`, idx 1 (`h₁ : ISize.minValue.toInt ≤ x`) (dependent): dependent; `∀ n, n ≤ maxValue.toInt → minValue.toInt ≤ n` fails at `n = minValue.toInt - 1`
theorem ISize.toBitVec_ofIntLE.h1 : ¬ indep% ISize.toBitVec_ofIntLE 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toBitVec_ofIntLE`, idx 2 (`h₂ : x ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ n, minValue.toInt ≤ n → n ≤ maxValue.toInt` fails at `n = maxValue.toInt + 1`
theorem ISize.toBitVec_ofIntLE.h2 : ¬ indep% ISize.toBitVec_ofIntLE 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toInt8_ofIntLE`, idx 1 (`h₁ : ISize.minValue.toInt ≤ n`) (dependent): dependent; `∀ n, n ≤ maxValue.toInt → minValue.toInt ≤ n` fails at `n = minValue.toInt - 1`
theorem ISize.toInt8_ofIntLE.h1 : ¬ indep% ISize.toInt8_ofIntLE 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toInt8_ofIntLE`, idx 2 (`h₂ : n ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ n, minValue.toInt ≤ n → n ≤ maxValue.toInt` fails at `n = maxValue.toInt + 1`
theorem ISize.toInt8_ofIntLE.h2 : ¬ indep% ISize.toInt8_ofIntLE 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toInt16_ofIntLE`, idx 1 (`h₁ : ISize.minValue.toInt ≤ n`) (dependent): dependent; `∀ n, n ≤ maxValue.toInt → minValue.toInt ≤ n` fails at `n = minValue.toInt - 1`
theorem ISize.toInt16_ofIntLE.h1 : ¬ indep% ISize.toInt16_ofIntLE 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toInt16_ofIntLE`, idx 2 (`h₂ : n ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ n, minValue.toInt ≤ n → n ≤ maxValue.toInt` fails at `n = maxValue.toInt + 1`
theorem ISize.toInt16_ofIntLE.h2 : ¬ indep% ISize.toInt16_ofIntLE 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toInt32_ofIntLE`, idx 1 (`h₁ : ISize.minValue.toInt ≤ n`) (dependent): dependent; `∀ n, n ≤ maxValue.toInt → minValue.toInt ≤ n` fails at `n = minValue.toInt - 1`
theorem ISize.toInt32_ofIntLE.h1 : ¬ indep% ISize.toInt32_ofIntLE 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toInt32_ofIntLE`, idx 2 (`h₂ : n ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ n, minValue.toInt ≤ n → n ≤ maxValue.toInt` fails at `n = maxValue.toInt + 1`
theorem ISize.toInt32_ofIntLE.h2 : ¬ indep% ISize.toInt32_ofIntLE 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toInt64_ofIntLE`, idx 1 (`h₁ : ISize.minValue.toInt ≤ n`) (dependent): dependent; `∀ n, n ≤ maxValue.toInt → minValue.toInt ≤ n` fails at `n = minValue.toInt - 1`
theorem ISize.toInt64_ofIntLE.h1 : ¬ indep% ISize.toInt64_ofIntLE 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toInt64_ofIntLE`, idx 2 (`h₂ : n ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ n, minValue.toInt ≤ n → n ≤ maxValue.toInt` fails at `n = maxValue.toInt + 1`
theorem ISize.toInt64_ofIntLE.h2 : ¬ indep% ISize.toInt64_ofIntLE 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toInt_ofIntLE`, idx 1 (`h₁ : ISize.minValue.toInt ≤ x`) (dependent): dependent; `∀ n, n ≤ maxValue.toInt → minValue.toInt ≤ n` fails at `n = minValue.toInt - 1`
theorem ISize.toInt_ofIntLE.h1 : ¬ indep% ISize.toInt_ofIntLE 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toInt_ofIntLE`, idx 2 (`h₂ : x ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ n, minValue.toInt ≤ n → n ≤ maxValue.toInt` fails at `n = maxValue.toInt + 1`
theorem ISize.toInt_ofIntLE.h2 : ¬ indep% ISize.toInt_ofIntLE 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toNatClampNeg_ofIntLE`, idx 1 (`h₁ : ISize.minValue.toInt ≤ n`) (dependent): dependent; `∀ n, n ≤ maxValue.toInt → minValue.toInt ≤ n` fails at `n = minValue.toInt - 1`
theorem ISize.toNatClampNeg_ofIntLE.h1 : ¬ indep% ISize.toNatClampNeg_ofIntLE 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toNatClampNeg_ofIntLE`, idx 2 (`h₂ : n ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ n, minValue.toInt ≤ n → n ≤ maxValue.toInt` fails at `n = maxValue.toInt + 1`
theorem ISize.toNatClampNeg_ofIntLE.h2 : ¬ indep% ISize.toNatClampNeg_ofIntLE 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_add`, idx 2 (`hab₁ : ISize.minValue.toInt ≤ a + b`) (dependent): dependent; `∀ a b, a + b ≤ maxValue.toInt → minValue.toInt ≤ a + b` fails at `a = minValue.toInt - 1`, `b = 0`
theorem ISize.ofIntLE_add.h2 : ¬ indep% ISize.ofIntLE_add 2 := fun h => by
  have := @h (ISize.minValue.toInt - 1) 0 (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_add`, idx 3 (`hab₂ : a + b ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ a b, minValue.toInt ≤ a + b → a + b ≤ maxValue.toInt` fails at `a = maxValue.toInt + 1`, `b = 0`
theorem ISize.ofIntLE_add.h3 : ¬ indep% ISize.ofIntLE_add 3 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) 0 (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_sub`, idx 2 (`hab₁ : ISize.minValue.toInt ≤ a - b`) (dependent): dependent; `∀ a b, a - b ≤ maxValue.toInt → minValue.toInt ≤ a - b` fails at `a = minValue.toInt - 1`, `b = 0`
theorem ISize.ofIntLE_sub.h2 : ¬ indep% ISize.ofIntLE_sub 2 := fun h => by
  have := @h (ISize.minValue.toInt - 1) 0 (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_sub`, idx 3 (`hab₂ : a - b ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ a b, minValue.toInt ≤ a - b → a - b ≤ maxValue.toInt` fails at `a = maxValue.toInt + 1`, `b = 0`
theorem ISize.ofIntLE_sub.h3 : ¬ indep% ISize.ofIntLE_sub 3 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) 0 (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_mul`, idx 2 (`hab₁ : ISize.minValue.toInt ≤ a * b`) (dependent): dependent; `∀ a b, a * b ≤ maxValue.toInt → minValue.toInt ≤ a * b` fails at `a = minValue.toInt - 1`, `b = 1`
theorem ISize.ofIntLE_mul.h2 : ¬ indep% ISize.ofIntLE_mul 2 := fun h => by
  have := @h (ISize.minValue.toInt - 1) 1 (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_mul`, idx 3 (`hab₂ : a * b ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ a b, minValue.toInt ≤ a * b → a * b ≤ maxValue.toInt` fails at `a = maxValue.toInt + 1`, `b = 1`
theorem ISize.ofIntLE_mul.h3 : ¬ indep% ISize.ofIntLE_mul 3 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) 1 (by isz); clear h; revert this; isz

-- `ISize.ofInt_eq_ofIntLE_div`, idx 2 (`ha₁ : ISize.minValue.toInt ≤ a`) (dependent): dependent; `∀ indep, minValue.toInt ≤ a` fails at `a = minValue.toInt - 1`, `b = 0`
theorem ISize.ofInt_eq_ofIntLE_div.h2 : ¬ indep% ISize.ofInt_eq_ofIntLE_div 2 := fun h => by
  have := @h (ISize.minValue.toInt - 1) 0 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_eq_ofIntLE_div`, idx 3 (`ha₂ : a ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ indep, a ≤ maxValue.toInt` fails at `a = maxValue.toInt + 1`, `b = 0`
theorem ISize.ofInt_eq_ofIntLE_div.h3 : ¬ indep% ISize.ofInt_eq_ofIntLE_div 3 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) 0 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_eq_ofIntLE_div`, idx 4 (`hb₁ : ISize.minValue.toInt ≤ b`) (dependent): dependent; `∀ indep, minValue.toInt ≤ b` fails at `a = 0`, `b = minValue.toInt - 1`
theorem ISize.ofInt_eq_ofIntLE_div.h4 : ¬ indep% ISize.ofInt_eq_ofIntLE_div 4 := fun h => by
  have := @h 0 (ISize.minValue.toInt - 1) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_eq_ofIntLE_div`, idx 5 (`hb₂ : b ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ indep, b ≤ maxValue.toInt` fails at `a = 0`, `b = maxValue.toInt + 1`
theorem ISize.ofInt_eq_ofIntLE_div.h5 : ¬ indep% ISize.ofInt_eq_ofIntLE_div 5 := fun h => by
  have := @h 0 (ISize.maxValue.toInt + 1) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_eq_ofIntLE_mod`, idx 2 (`ha₁ : ISize.minValue.toInt ≤ a`) (dependent): dependent; `∀ indep, minValue.toInt ≤ a` fails at `a = minValue.toInt - 1`, `b = 0`
theorem ISize.ofInt_eq_ofIntLE_mod.h2 : ¬ indep% ISize.ofInt_eq_ofIntLE_mod 2 := fun h => by
  have := @h (ISize.minValue.toInt - 1) 0 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_eq_ofIntLE_mod`, idx 3 (`ha₂ : a ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ indep, a ≤ maxValue.toInt` fails at `a = maxValue.toInt + 1`, `b = 0`
theorem ISize.ofInt_eq_ofIntLE_mod.h3 : ¬ indep% ISize.ofInt_eq_ofIntLE_mod 3 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) 0 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_eq_ofIntLE_mod`, idx 4 (`hb₁ : ISize.minValue.toInt ≤ b`) (dependent): dependent; `∀ indep, minValue.toInt ≤ b` fails at `a = 0`, `b = minValue.toInt - 1`
theorem ISize.ofInt_eq_ofIntLE_mod.h4 : ¬ indep% ISize.ofInt_eq_ofIntLE_mod 4 := fun h => by
  have := @h 0 (ISize.minValue.toInt - 1) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_eq_ofIntLE_mod`, idx 5 (`hb₂ : b ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ indep, b ≤ maxValue.toInt` fails at `a = 0`, `b = maxValue.toInt + 1`
theorem ISize.ofInt_eq_ofIntLE_mod.h5 : ¬ indep% ISize.ofInt_eq_ofIntLE_mod 5 := fun h => by
  have := @h 0 (ISize.maxValue.toInt + 1) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_le_iff_le`, idx 2 (`ha₁ : ISize.minValue.toInt ≤ a`) (dependent): dependent; `∀ indep, minValue.toInt ≤ a` fails at `a = minValue.toInt - 1`, `b = 0`
theorem ISize.ofIntLE_le_iff_le.h2 : ¬ indep% ISize.ofIntLE_le_iff_le 2 := fun h => by
  have := @h (ISize.minValue.toInt - 1) 0 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_le_iff_le`, idx 3 (`ha₂ : a ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ indep, a ≤ maxValue.toInt` fails at `a = maxValue.toInt + 1`, `b = 0`
theorem ISize.ofIntLE_le_iff_le.h3 : ¬ indep% ISize.ofIntLE_le_iff_le 3 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) 0 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_le_iff_le`, idx 4 (`hb₁ : ISize.minValue.toInt ≤ b`) (dependent): dependent; `∀ indep, minValue.toInt ≤ b` fails at `a = 0`, `b = minValue.toInt - 1`
theorem ISize.ofIntLE_le_iff_le.h4 : ¬ indep% ISize.ofIntLE_le_iff_le 4 := fun h => by
  have := @h 0 (ISize.minValue.toInt - 1) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_le_iff_le`, idx 5 (`hb₂ : b ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ indep, b ≤ maxValue.toInt` fails at `a = 0`, `b = maxValue.toInt + 1`
theorem ISize.ofIntLE_le_iff_le.h5 : ¬ indep% ISize.ofIntLE_le_iff_le 5 := fun h => by
  have := @h 0 (ISize.maxValue.toInt + 1) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_lt_iff_lt`, idx 2 (`ha₁ : ISize.minValue.toInt ≤ a`) (dependent): dependent; `∀ indep, minValue.toInt ≤ a` fails at `a = minValue.toInt - 1`, `b = 0`
theorem ISize.ofIntLE_lt_iff_lt.h2 : ¬ indep% ISize.ofIntLE_lt_iff_lt 2 := fun h => by
  have := @h (ISize.minValue.toInt - 1) 0 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_lt_iff_lt`, idx 3 (`ha₂ : a ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ indep, a ≤ maxValue.toInt` fails at `a = maxValue.toInt + 1`, `b = 0`
theorem ISize.ofIntLE_lt_iff_lt.h3 : ¬ indep% ISize.ofIntLE_lt_iff_lt 3 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) 0 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_lt_iff_lt`, idx 4 (`hb₁ : ISize.minValue.toInt ≤ b`) (dependent): dependent; `∀ indep, minValue.toInt ≤ b` fails at `a = 0`, `b = minValue.toInt - 1`
theorem ISize.ofIntLE_lt_iff_lt.h4 : ¬ indep% ISize.ofIntLE_lt_iff_lt 4 := fun h => by
  have := @h 0 (ISize.minValue.toInt - 1) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofIntLE_lt_iff_lt`, idx 5 (`hb₂ : b ≤ ISize.maxValue.toInt`) (dependent): dependent; `∀ indep, b ≤ maxValue.toInt` fails at `a = 0`, `b = maxValue.toInt + 1`
theorem ISize.ofIntLE_lt_iff_lt.h5 : ¬ indep% ISize.ofIntLE_lt_iff_lt 5 := fun h => by
  have := @h 0 (ISize.maxValue.toInt + 1) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.cast_toNatClampNeg`, idx 1 (`hx : 0 ≤ x`): `x = -1`: `0 ≠ -1`
theorem ISize.cast_toNatClampNeg.h1 : ¬ drop% ISize.cast_toNatClampNeg 1 := fun h => by
  have := @h (-1); clear h; revert this; isz

-- `ISize.ofNat_toNatClampNeg`, idx 1 (`hx : 0 ≤ x`): `x = -1`: `ofNat 0 = 0 ≠ -1`
theorem ISize.ofNat_toNatClampNeg.h1 : ¬ drop% ISize.ofNat_toNatClampNeg 1 := fun h => by
  have := @h (-1); clear h; revert this; isz

-- `ISize.toInt_eq_toNatClampNeg`, idx 1 (`ha : 0 ≤ a`): `a = -1`: `-1 ≠ 0`
theorem ISize.toInt_eq_toNatClampNeg.h1 : ¬ drop% ISize.toInt_eq_toNatClampNeg 1 := fun h => by
  have := @h (-1); clear h; revert this; isz

-- `ISize.toNat_toBitVec_of_le`, idx 1 (`hx : 0 ≤ x`): `x = -1`: `toBitVec.toNat = 2^numBits - 1 ≠ 0`
theorem ISize.toNat_toBitVec_of_le.h1 : ¬ drop% ISize.toNat_toBitVec_of_le 1 := fun h => by
  have := @h (-1); clear h; revert this; isz

-- `ISize.toNat_toUSize_of_le`, idx 1 (`hx : 0 ≤ x`): `x = -1`: `toUSize.toNat = 2^numBits - 1 ≠ 0`
theorem ISize.toNat_toUSize_of_le.h1 : ¬ drop% ISize.toNat_toUSize_of_le 1 := fun h => by
  have := @h (-1); clear h; revert this; isz

-- `ISize.toNat_toBitVec_ofNat_of_lt`, idx 1 (`h : n < 2 ^ 32`): `n = 2^64`: `toBitVec.toNat = 0` on both platforms
theorem ISize.toNat_toBitVec_ofNat_of_lt.h1 : ¬ drop% ISize.toNat_toBitVec_ofNat_of_lt 1 := fun h => by
  have := @h (2^64); clear h; revert this; isz

-- `ISize.toInt_ofInt_of_le`, idx 1 (`hn : -2 ^ 31 ≤ n`): `n = -2^63 - 1`: `toInt (ofInt n)` is `-1` (32-bit) or `2^63 - 1` (64-bit)
theorem ISize.toInt_ofInt_of_le.h1 : ¬ drop% ISize.toInt_ofInt_of_le 1 := fun h => by
  have := @h (-2^63-1) (by isz); clear h; revert this; isz

-- `ISize.toInt_ofInt_of_le`, idx 2 (`hn' : n < 2 ^ 31`): `n = 2^63`: `toInt (ofInt n)` is `0` or `-2^63`
theorem ISize.toInt_ofInt_of_le.h2 : ¬ drop% ISize.toInt_ofInt_of_le 2 := fun h => by
  have := @h (2^63) (by isz); clear h; revert this; isz

-- `ISize.toInt_ofInt_of_two_pow_numBits_le`, idx 1 (`hn : -2 ^ (System.Platform.numBits - 1) ≤ n`): `n = -2^63 - 1`: `toInt (ofInt n)` is `-1` or `2^63 - 1`
theorem ISize.toInt_ofInt_of_two_pow_numBits_le.h1 : ¬ drop% ISize.toInt_ofInt_of_two_pow_numBits_le 1 := fun h => by
  have := @h (-2^63-1) (by isz); clear h; revert this; isz

-- `ISize.toNatClampNeg_ofInt_eq_zero`, idx 1 (`hn : -2 ^ 31 ≤ n`): `n = minValue.toInt - 1`: wraps to `maxValue`, `toNatClampNeg = 2^(numBits-1) - 1 ≠ 0`
theorem ISize.toNatClampNeg_ofInt_eq_zero.h1 : ¬ drop% ISize.toNatClampNeg_ofInt_eq_zero 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toNatClampNeg_ofInt_eq_zero`, idx 2 (`hn' : n ≤ 0`): `n = 1`: `toNatClampNeg = 1`
theorem ISize.toNatClampNeg_ofInt_eq_zero.h2 : ¬ drop% ISize.toNatClampNeg_ofInt_eq_zero 2 := fun h => by
  have := @h 1 (by isz); clear h; revert this; isz

-- `ISize.toNatClampNeg_ofNat_of_lt`, idx 1 (`h : n < 2 ^ 31`): `n = 2^64`: `ofNat n = 0`
theorem ISize.toNatClampNeg_ofNat_of_lt.h1 : ¬ drop% ISize.toNatClampNeg_ofNat_of_lt 1 := fun h => by
  have := @h (2^64); clear h; revert this; isz

-- `ISize.toNatClampNeg_ofNat_of_lt_two_pow_numBits`, idx 1 (`h : n < 2 ^ (System.Platform.numBits - 1)`): `n = 2^64`: `ofNat n = 0`
theorem ISize.toNatClampNeg_ofNat_of_lt_two_pow_numBits.h1 : ¬ drop% ISize.toNatClampNeg_ofNat_of_lt_two_pow_numBits 1 := fun h => by
  have := @h (2^64); clear h; revert this; isz

-- `ISize.toNatClampNeg_neg_ofNat_of_le`, idx 1 (`h : n ≤ 2 ^ 31`): `n = 2^64 - 1`: `-ofNat n = 1`
theorem ISize.toNatClampNeg_neg_ofNat_of_le.h1 : ¬ drop% ISize.toNatClampNeg_neg_ofNat_of_le 1 := fun h => by
  have := @h (2^64-1); clear h; revert this; isz

-- `ISize.toInt_ofNat_of_lt`, idx 1 (`h : n < 2 ^ 31`): `n = 2^64`: `ofNat n = 0`
theorem ISize.toInt_ofNat_of_lt.h1 : ¬ drop% ISize.toInt_ofNat_of_lt 1 := fun h => by
  have := @h (2^64); clear h; revert this; isz

-- `ISize.toInt_neg_ofNat_of_le`, idx 1 (`h : n ≤ 2 ^ 31`): `n = 2^64`: `toInt (-0) = 0 ≠ -2^64`
theorem ISize.toInt_neg_ofNat_of_le.h1 : ¬ drop% ISize.toInt_neg_ofNat_of_le 1 := fun h => by
  have := @h (2^64); clear h; revert this; isz

-- `ISize.toInt_ofIntClamp`, idx 1 (`h₁ : ISize.minValue.toInt ≤ x`): `n = minValue.toInt - 1`: clamps to `minValue`, but the right side is `n` resp. wraps to `maxValue`
theorem ISize.toInt_ofIntClamp.h1 : ¬ drop% ISize.toInt_ofIntClamp 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toInt_ofIntClamp`, idx 2 (`h₂ : x ≤ ISize.maxValue.toInt`): `n = maxValue.toInt + 1`: clamps to `maxValue`, but the right side is `n` resp. wraps to `minValue`
theorem ISize.toInt_ofIntClamp.h2 : ¬ drop% ISize.toInt_ofIntClamp 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toInt_ofIntTruncate`, idx 1 (`h₁ : ISize.minValue.toInt ≤ x`): `n = minValue.toInt - 1`: clamps to `minValue`, but the right side is `n` resp. wraps to `maxValue`
theorem ISize.toInt_ofIntTruncate.h1 : ¬ drop% ISize.toInt_ofIntTruncate 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toInt_ofIntTruncate`, idx 2 (`h₂ : x ≤ ISize.maxValue.toInt`): `n = maxValue.toInt + 1`: clamps to `maxValue`, but the right side is `n` resp. wraps to `minValue`
theorem ISize.toInt_ofIntTruncate.h2 : ¬ drop% ISize.toInt_ofIntTruncate 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toBitVec_ofIntClamp`, idx 1 (`h₁ : ISize.minValue.toInt ≤ n`): `n = minValue.toInt - 1`: clamps to `minValue`, but the right side is `n` resp. wraps to `maxValue`
theorem ISize.toBitVec_ofIntClamp.h1 : ¬ drop% ISize.toBitVec_ofIntClamp 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toBitVec_ofIntClamp`, idx 2 (`h₂ : n ≤ ISize.maxValue.toInt`): `n = maxValue.toInt + 1`: clamps to `maxValue`, but the right side is `n` resp. wraps to `minValue`
theorem ISize.toBitVec_ofIntClamp.h2 : ¬ drop% ISize.toBitVec_ofIntClamp 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toBitVec_ofIntTruncate`, idx 1 (`h₁ : ISize.minValue.toInt ≤ n`): `n = minValue.toInt - 1`: clamps to `minValue`, but the right side is `n` resp. wraps to `maxValue`
theorem ISize.toBitVec_ofIntTruncate.h1 : ¬ drop% ISize.toBitVec_ofIntTruncate 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toBitVec_ofIntTruncate`, idx 2 (`h₂ : n ≤ ISize.maxValue.toInt`): `n = maxValue.toInt + 1`: clamps to `maxValue`, but the right side is `n` resp. wraps to `minValue`
theorem ISize.toBitVec_ofIntTruncate.h2 : ¬ drop% ISize.toBitVec_ofIntTruncate 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toNatClampNeg_ofInt_of_le`, idx 1 (`h₁ : -2 ^ 31 ≤ n`): `n = minValue.toInt - 1`: wraps to `maxValue`, `toNatClampNeg = 2^(numBits-1) - 1`, `n.toNat = 0`
theorem ISize.toNatClampNeg_ofInt_of_le.h1 : ¬ drop% ISize.toNatClampNeg_ofInt_of_le 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toNatClampNeg_ofInt_of_le`, idx 2 (`h₂ : n < 2 ^ 31`): `n = 2^63`: `ofInt n` is `0` or `minValue`, `toNatClampNeg = 0 ≠ 2^63`
theorem ISize.toNatClampNeg_ofInt_of_le.h2 : ¬ drop% ISize.toNatClampNeg_ofInt_of_le 2 := fun h => by
  have := @h (2^63) (by isz); clear h; revert this; isz

-- `ISize.toNatClampNeg_ofInt_of_two_pow_numBits`, idx 1 (`h₁ : -2 ^ (System.Platform.numBits - 1) ≤ n`): `n = minValue.toInt - 1`: wraps to `maxValue`, `toNatClampNeg = 2^(numBits-1) - 1`, `n.toNat = 0`
theorem ISize.toNatClampNeg_ofInt_of_two_pow_numBits.h1 : ¬ drop% ISize.toNatClampNeg_ofInt_of_two_pow_numBits 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toNatClampNeg_ofInt_of_two_pow_numBits`, idx 2 (`h₂ : n < 2 ^ (System.Platform.numBits - 1)`): `n = 2^63`: `ofInt n` is `0` or `minValue`, `toNatClampNeg = 0 ≠ 2^63`
theorem ISize.toNatClampNeg_ofInt_of_two_pow_numBits.h2 : ¬ drop% ISize.toNatClampNeg_ofInt_of_two_pow_numBits 2 := fun h => by
  have := @h (2^63) (by isz); clear h; revert this; isz

-- `ISize.toNatClampNeg_ofIntClamp_of_lt`, idx 1 (`h₁ : n < 2 ^ 31`): `n = 2^63`: clamps to `maxValue`, `2^(numBits-1) - 1 ≠ 2^63`
theorem ISize.toNatClampNeg_ofIntClamp_of_lt.h1 : ¬ drop% ISize.toNatClampNeg_ofIntClamp_of_lt 1 := fun h => by
  have := @h (2^63); clear h; revert this; isz

-- `ISize.toNatClampNeg_ofIntClamp_of_lt_two_pow_numBits`, idx 1 (`h₁ : n < 2 ^ (System.Platform.numBits - 1)`): `n = 2^63`: clamps to `maxValue`, `2^(numBits-1) - 1 ≠ 2^63`
theorem ISize.toNatClampNeg_ofIntClamp_of_lt_two_pow_numBits.h1 : ¬ drop% ISize.toNatClampNeg_ofIntClamp_of_lt_two_pow_numBits 1 := fun h => by
  have := @h (2^63); clear h; revert this; isz

-- `ISize.toNatClampNeg_ofIntTruncate_of_lt`, idx 1 (`h₁ : n < 2 ^ 31`): `n = 2^63`: clamps to `maxValue`, `2^(numBits-1) - 1 ≠ 2^63`
theorem ISize.toNatClampNeg_ofIntTruncate_of_lt.h1 : ¬ drop% ISize.toNatClampNeg_ofIntTruncate_of_lt 1 := fun h => by
  have := @h (2^63); clear h; revert this; isz

-- `ISize.toNatClampNeg_ofIntTruncate_of_lt_two_pow_numBits`, idx 1 (`h₁ : n < 2 ^ (System.Platform.numBits - 1)`): `n = 2^63`: clamps to `maxValue`, `2^(numBits-1) - 1 ≠ 2^63`
theorem ISize.toNatClampNeg_ofIntTruncate_of_lt_two_pow_numBits.h1 : ¬ drop% ISize.toNatClampNeg_ofIntTruncate_of_lt_two_pow_numBits 1 := fun h => by
  have := @h (2^63); clear h; revert this; isz

-- `ISize.toInt8_ofIntClamp`, idx 1 (`h₁ : -2 ^ (System.Platform.numBits - 1) ≤ n`): `n = minValue.toInt - 1`: clamps to `minValue`, and `toInt8` of it is one more than `Int8.ofInt n` (mod `2^8`)
theorem ISize.toInt8_ofIntClamp.h1 : ¬ drop% ISize.toInt8_ofIntClamp 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toInt8_ofIntClamp`, idx 2 (`h₂ : n < 2 ^ (System.Platform.numBits - 1)`): `n = maxValue.toInt + 1`: clamps to `maxValue`, and `toInt8` of it is one less than `Int8.ofInt n` (mod `2^8`)
theorem ISize.toInt8_ofIntClamp.h2 : ¬ drop% ISize.toInt8_ofIntClamp 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toInt8_ofIntTruncate`, idx 1 (`h₁ : -2 ^ (System.Platform.numBits - 1) ≤ n`): `n = minValue.toInt - 1`: clamps to `minValue`, and `toInt8` of it is one more than `Int8.ofInt n` (mod `2^8`)
theorem ISize.toInt8_ofIntTruncate.h1 : ¬ drop% ISize.toInt8_ofIntTruncate 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toInt8_ofIntTruncate`, idx 2 (`h₂ : n < 2 ^ (System.Platform.numBits - 1)`): `n = maxValue.toInt + 1`: clamps to `maxValue`, and `toInt8` of it is one less than `Int8.ofInt n` (mod `2^8`)
theorem ISize.toInt8_ofIntTruncate.h2 : ¬ drop% ISize.toInt8_ofIntTruncate 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toInt16_ofIntClamp`, idx 1 (`h₁ : -2 ^ (System.Platform.numBits - 1) ≤ n`): `n = minValue.toInt - 1`: clamps to `minValue`, and `toInt16` of it is one more than `Int16.ofInt n` (mod `2^16`)
theorem ISize.toInt16_ofIntClamp.h1 : ¬ drop% ISize.toInt16_ofIntClamp 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toInt16_ofIntClamp`, idx 2 (`h₂ : n < 2 ^ (System.Platform.numBits - 1)`): `n = maxValue.toInt + 1`: clamps to `maxValue`, and `toInt16` of it is one less than `Int16.ofInt n` (mod `2^16`)
theorem ISize.toInt16_ofIntClamp.h2 : ¬ drop% ISize.toInt16_ofIntClamp 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toInt16_ofIntTruncate`, idx 1 (`h₁ : -2 ^ (System.Platform.numBits - 1) ≤ n`): `n = minValue.toInt - 1`: clamps to `minValue`, and `toInt16` of it is one more than `Int16.ofInt n` (mod `2^16`)
theorem ISize.toInt16_ofIntTruncate.h1 : ¬ drop% ISize.toInt16_ofIntTruncate 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toInt16_ofIntTruncate`, idx 2 (`h₂ : n < 2 ^ (System.Platform.numBits - 1)`): `n = maxValue.toInt + 1`: clamps to `maxValue`, and `toInt16` of it is one less than `Int16.ofInt n` (mod `2^16`)
theorem ISize.toInt16_ofIntTruncate.h2 : ¬ drop% ISize.toInt16_ofIntTruncate 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toInt32_ofIntClamp`, idx 1 (`h₁ : -2 ^ (System.Platform.numBits - 1) ≤ n`): `n = minValue.toInt - 1`: clamps to `minValue`, and `toInt32` of it is one more than `Int32.ofInt n` (mod `2^32`)
theorem ISize.toInt32_ofIntClamp.h1 : ¬ drop% ISize.toInt32_ofIntClamp 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toInt32_ofIntClamp`, idx 2 (`h₂ : n < 2 ^ (System.Platform.numBits - 1)`): `n = maxValue.toInt + 1`: clamps to `maxValue`, and `toInt32` of it is one less than `Int32.ofInt n` (mod `2^32`)
theorem ISize.toInt32_ofIntClamp.h2 : ¬ drop% ISize.toInt32_ofIntClamp 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toInt32_ofIntTruncate`, idx 1 (`h₁ : -2 ^ (System.Platform.numBits - 1) ≤ n`): `n = minValue.toInt - 1`: clamps to `minValue`, and `toInt32` of it is one more than `Int32.ofInt n` (mod `2^32`)
theorem ISize.toInt32_ofIntTruncate.h1 : ¬ drop% ISize.toInt32_ofIntTruncate 1 := fun h => by
  have := @h (ISize.minValue.toInt - 1) (by isz); clear h; revert this; isz

-- `ISize.toInt32_ofIntTruncate`, idx 2 (`h₂ : n < 2 ^ (System.Platform.numBits - 1)`): `n = maxValue.toInt + 1`: clamps to `maxValue`, and `toInt32` of it is one less than `Int32.ofInt n` (mod `2^32`)
theorem ISize.toInt32_ofIntTruncate.h2 : ¬ drop% ISize.toInt32_ofIntTruncate 2 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) (by isz); clear h; revert this; isz

-- `ISize.toInt64_ne_neg_one`, idx 1 (`ha : a ≠ -1`): `a = -1`
theorem ISize.toInt64_ne_neg_one.h1 : ¬ drop% ISize.toInt64_ne_neg_one 1 := fun h => by
  have := @h (-1); clear h; revert this; isz

-- `ISize.toInt_div_of_ne_left`, idx 2 (`h : a ≠ ISize.minValue`): `a = minValue`, `b = -1`: `minValue / -1 = minValue`, `tdiv` gives `2^(numBits-1)`
theorem ISize.toInt_div_of_ne_left.h2 : ¬ drop% ISize.toInt_div_of_ne_left 2 := fun h => by
  have := @h ISize.minValue (-1); clear h; revert this; isz

-- `ISize.toInt_div_of_ne_right`, idx 2 (`h : b ≠ -1`): `a = minValue`, `b = -1`: `minValue / -1 = minValue`, `tdiv` gives `2^(numBits-1)`
theorem ISize.toInt_div_of_ne_right.h2 : ¬ drop% ISize.toInt_div_of_ne_right 2 := fun h => by
  have := @h ISize.minValue (-1); clear h; revert this; isz

-- `ISize.ofInt_tdiv`, idx 2 (`ha₁ : ISize.minValue.toInt ≤ a`): `a = minValue.toInt - 1`, `b = 2`: `-2^(numBits-2)` vs `maxValue / 2 = 2^(numBits-2) - 1`
theorem ISize.ofInt_tdiv.h2 : ¬ drop% ISize.ofInt_tdiv 2 := fun h => by
  have := @h (ISize.minValue.toInt - 1) 2 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_tdiv`, idx 3 (`ha₂ : a ≤ ISize.maxValue.toInt`): `a = maxValue.toInt + 1`, `b = 2`: `2^(numBits-2)` vs `minValue / 2 = -2^(numBits-2)`
theorem ISize.ofInt_tdiv.h3 : ¬ drop% ISize.ofInt_tdiv 3 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) 2 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_tdiv`, idx 4 (`hb₁ : ISize.minValue.toInt ≤ b`): `a = maxValue.toInt`, `b = minValue.toInt - 1`: `0` vs `maxValue / maxValue = 1`
theorem ISize.ofInt_tdiv.h4 : ¬ drop% ISize.ofInt_tdiv 4 := fun h => by
  have := @h ISize.maxValue.toInt (ISize.minValue.toInt - 1) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_tdiv`, idx 5 (`hb₂ : b ≤ ISize.maxValue.toInt`): `a = minValue.toInt`, `b = maxValue.toInt + 1`: `-1` vs `minValue / minValue = 1`
theorem ISize.ofInt_tdiv.h5 : ¬ drop% ISize.ofInt_tdiv 5 := fun h => by
  have := @h ISize.minValue.toInt (ISize.maxValue.toInt + 1) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_tmod`, idx 2 (`ha₁ : ISize.minValue.toInt ≤ a`): `a = minValue.toInt - 1`, `b = 2`: `-1` vs `maxValue % 2 = 1`
theorem ISize.ofInt_tmod.h2 : ¬ drop% ISize.ofInt_tmod 2 := fun h => by
  have := @h (ISize.minValue.toInt - 1) 2 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_tmod`, idx 3 (`ha₂ : a ≤ ISize.maxValue.toInt`): `a = maxValue.toInt + 1`, `b = 3`: `2` vs `minValue % 3 = -2`
theorem ISize.ofInt_tmod.h3 : ¬ drop% ISize.ofInt_tmod 3 := fun h => by
  have := @h (ISize.maxValue.toInt + 1) 3 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_tmod`, idx 4 (`hb₁ : ISize.minValue.toInt ≤ b`): `a = maxValue.toInt`, `b = minValue.toInt - 1`: `maxValue` vs `maxValue % maxValue = 0`
theorem ISize.ofInt_tmod.h4 : ¬ drop% ISize.ofInt_tmod 4 := fun h => by
  have := @h ISize.maxValue.toInt (ISize.minValue.toInt - 1) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_tmod`, idx 5 (`hb₂ : b ≤ ISize.maxValue.toInt`): `a = 3`, `b = 2^64 + 2`: `3` vs `3 % 2 = 1`
theorem ISize.ofInt_tmod.h5 : ¬ drop% ISize.ofInt_tmod 5 := fun h => by
  have := @h 3 (2^64+2) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofNat_div`, idx 2 (`ha : a < 2 ^ (System.Platform.numBits - 1)`): `a = 2^64 + 1`, `b = 3`: `ofNat ((2^64-1)/3) ≠ 0` vs `1 / 3 = 0`
theorem ISize.ofNat_div.h2 : ¬ drop% ISize.ofNat_div 2 := fun h => by
  have := @h (2^64+1) 3 (by isz); clear h; revert this; isz

-- `ISize.ofNat_div`, idx 3 (`hb : b < 2 ^ (System.Platform.numBits - 1)`): `a = 4`, `b = 2^64 + 2`: `0` vs `4 / 2 = 2`
theorem ISize.ofNat_div.h3 : ¬ drop% ISize.ofNat_div 3 := fun h => by
  have := @h 4 (2^64+2) (by isz); clear h; revert this; isz

-- `ISize.ofNat_mod`, idx 2 (`ha : a < 2 ^ (System.Platform.numBits - 1)`): `a = 2^64 + 1`, `b = 3`: `2` vs `1 % 3 = 1`
theorem ISize.ofNat_mod.h2 : ¬ drop% ISize.ofNat_mod 2 := fun h => by
  have := @h (2^64+1) 3 (by isz); clear h; revert this; isz

-- `ISize.ofNat_mod`, idx 3 (`hb : b < 2 ^ (System.Platform.numBits - 1)`): `a = 3`, `b = 2^64 + 2`: `3` vs `3 % 2 = 1`
theorem ISize.ofNat_mod.h3 : ¬ drop% ISize.ofNat_mod 3 := fun h => by
  have := @h 3 (2^64+2) (by isz); clear h; revert this; isz

-- `ISize.ofNat_le_iff_le`, idx 2 (`ha : a < 2 ^ (System.Platform.numBits - 1)`): `a = 2^64 + 1`, `b = 1`: `1 ≤ 1` but not `a ≤ b`
theorem ISize.ofNat_le_iff_le.h2 : ¬ drop% ISize.ofNat_le_iff_le 2 := fun h => by
  have := @h (2^64+1) 1 (by isz); clear h; revert this; isz

-- `ISize.ofNat_le_iff_le`, idx 3 (`hb : b < 2 ^ (System.Platform.numBits - 1)`): `a = 2`, `b = 2^64 + 1`: not `2 ≤ 1` but `a ≤ b`
theorem ISize.ofNat_le_iff_le.h3 : ¬ drop% ISize.ofNat_le_iff_le 3 := fun h => by
  have := @h 2 (2^64+1) (by isz); clear h; revert this; isz

-- `ISize.ofNat_lt_iff_lt`, idx 2 (`ha : a < 2 ^ (System.Platform.numBits - 1)`): `a = 2^64`, `b = 1`: `0 < 1` but not `a < b`
theorem ISize.ofNat_lt_iff_lt.h2 : ¬ drop% ISize.ofNat_lt_iff_lt 2 := fun h => by
  have := @h (2^64) 1 (by isz); clear h; revert this; isz

-- `ISize.ofNat_lt_iff_lt`, idx 3 (`hb : b < 2 ^ (System.Platform.numBits - 1)`): `a = 0`, `b = 2^64`: not `0 < 0` but `a < b`
theorem ISize.ofNat_lt_iff_lt.h3 : ¬ drop% ISize.ofNat_lt_iff_lt 3 := fun h => by
  have := @h 0 (2^64) (by isz); clear h; revert this; isz

-- `ISize.ofInt_le_iff_le`, idx 2 (`ha₁ : ISize.minValue.toInt ≤ a`): `a = -2^64 + 1`, `b = 0`: not `1 ≤ 0` but `a ≤ b`
theorem ISize.ofInt_le_iff_le.h2 : ¬ drop% ISize.ofInt_le_iff_le 2 := fun h => by
  have := @h (-2^64+1) 0 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_le_iff_le`, idx 3 (`ha₂ : a ≤ ISize.maxValue.toInt`): `a = 2^64`, `b = 1`: `0 ≤ 1` but not `a ≤ b`
theorem ISize.ofInt_le_iff_le.h3 : ¬ drop% ISize.ofInt_le_iff_le 3 := fun h => by
  have := @h (2^64) 1 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_le_iff_le`, idx 4 (`hb₁ : ISize.minValue.toInt ≤ b`): `a = 0`, `b = -2^64`: `0 ≤ 0` but not `a ≤ b`
theorem ISize.ofInt_le_iff_le.h4 : ¬ drop% ISize.ofInt_le_iff_le 4 := fun h => by
  have := @h 0 (-2^64) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_le_iff_le`, idx 5 (`hb₂ : b ≤ ISize.maxValue.toInt`): `a = 1`, `b = 2^64`: not `1 ≤ 0` but `a ≤ b`
theorem ISize.ofInt_le_iff_le.h5 : ¬ drop% ISize.ofInt_le_iff_le 5 := fun h => by
  have := @h 1 (2^64) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_lt_iff_lt`, idx 2 (`ha₁ : ISize.minValue.toInt ≤ a`): `a = -2^64`, `b = 0`: not `0 < 0` but `a < b`
theorem ISize.ofInt_lt_iff_lt.h2 : ¬ drop% ISize.ofInt_lt_iff_lt 2 := fun h => by
  have := @h (-2^64) 0 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_lt_iff_lt`, idx 3 (`ha₂ : a ≤ ISize.maxValue.toInt`): `a = 2^64`, `b = 1`: `0 < 1` but not `a < b`
theorem ISize.ofInt_lt_iff_lt.h3 : ¬ drop% ISize.ofInt_lt_iff_lt 3 := fun h => by
  have := @h (2^64) 1 (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_lt_iff_lt`, idx 4 (`hb₁ : ISize.minValue.toInt ≤ b`): `a = 0`, `b = -2^64 + 1`: `0 < 1` but not `a < b`
theorem ISize.ofInt_lt_iff_lt.h4 : ¬ drop% ISize.ofInt_lt_iff_lt 4 := fun h => by
  have := @h 0 (-2^64+1) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.ofInt_lt_iff_lt`, idx 5 (`hb₂ : b ≤ ISize.maxValue.toInt`): `a = 1`, `b = 2^64`: not `1 < 0` but `a < b`
theorem ISize.ofInt_lt_iff_lt.h5 : ¬ drop% ISize.ofInt_lt_iff_lt 5 := fun h => by
  have := @h 1 (2^64) (by isz) (by isz) (by isz); clear h; revert this; isz

-- `ISize.sub_le`, idx 2 (`hb : 0 ≤ b`): `a = 0`, `b = -1`: `1 ≤ 0` fails
theorem ISize.sub_le.h2 : ¬ drop% ISize.sub_le 2 := fun h => by
  have := @h 0 (-1) (by isz); clear h; revert this; isz

-- `ISize.sub_le`, idx 3 (`hab : b ≤ a`): `a = minValue`, `b = 1`: `a - b = maxValue`
theorem ISize.sub_le.h3 : ¬ drop% ISize.sub_le 3 := fun h => by
  have := @h ISize.minValue 1 (by isz); clear h; revert this; isz

-- `ISize.sub_lt`, idx 2 (`hb : 0 < b`): `a = b = 0`: `0 < 0` fails
theorem ISize.sub_lt.h2 : ¬ drop% ISize.sub_lt 2 := fun h => by
  have := @h 0 0 (by isz); clear h; revert this; isz

-- `ISize.sub_lt`, idx 3 (`hab : b ≤ a`): `a = minValue`, `b = 1`: `a - b = maxValue`
theorem ISize.sub_lt.h3 : ¬ drop% ISize.sub_lt 3 := fun h => by
  have := @h ISize.minValue 1 (by isz); clear h; revert this; isz

-- `ISize.sub_nonneg_of_le`, idx 2 (`hb : 0 ≤ b`): `a = maxValue`, `b = -1`: `a - b = minValue < 0`
theorem ISize.sub_nonneg_of_le.h2 : ¬ drop% ISize.sub_nonneg_of_le 2 := fun h => by
  have := @h ISize.maxValue (-1) (by isz); clear h; revert this; isz

-- `ISize.sub_nonneg_of_le`, idx 3 (`hab : b ≤ a`): `a = 0`, `b = 1`: `a - b = -1`
theorem ISize.sub_nonneg_of_le.h3 : ¬ drop% ISize.sub_nonneg_of_le 3 := fun h => by
  have := @h 0 1 (by isz); clear h; revert this; isz

-- `ISize.toNatClampNeg_sub_of_le`, idx 2 (`hb : 0 ≤ b`): `a = 0`, `b = -1`: `1` vs `0 - 0`
theorem ISize.toNatClampNeg_sub_of_le.h2 : ¬ drop% ISize.toNatClampNeg_sub_of_le 2 := fun h => by
  have := @h 0 (-1) (by isz); clear h; revert this; isz

-- `ISize.toNatClampNeg_sub_of_le`, idx 3 (`hab : b ≤ a`): `a = minValue`, `b = 1`: `a - b = maxValue`, `2^(numBits-1) - 1` vs `0 - 1 = 0`
theorem ISize.toNatClampNeg_sub_of_le.h3 : ¬ drop% ISize.toNatClampNeg_sub_of_le 3 := fun h => by
  have := @h ISize.minValue 1 (by isz); clear h; revert this; isz

-- `ISize.toInt_sub_of_le`, idx 2 (`hb : 0 ≤ b`): `a = maxValue`, `b = -1`: wraps to `minValue`
theorem ISize.toInt_sub_of_le.h2 : ¬ drop% ISize.toInt_sub_of_le 2 := fun h => by
  have := @h ISize.maxValue (-1) (by isz); clear h; revert this; isz

-- `ISize.toInt_sub_of_le`, idx 3 (`h : b ≤ a`): `a = minValue`, `b = 1`: wraps to `maxValue`
theorem ISize.toInt_sub_of_le.h3 : ¬ drop% ISize.toInt_sub_of_le 3 := fun h => by
  have := @h ISize.minValue 1 (by isz); clear h; revert this; isz

-- `ISize.toNatClampNeg_le`, idx 2 (`hab : a ≤ b`): `a = 1`, `b = 0`
theorem ISize.toNatClampNeg_le.h2 : ¬ drop% ISize.toNatClampNeg_le 2 := fun h => by
  have := @h 1 0; clear h; revert this; isz

-- `ISize.toUSize_le`, idx 2 (`ha : 0 ≤ a`): `a = -1`, `b = 0`: `toUSize (-1) = 2^numBits - 1`
theorem ISize.toUSize_le.h2 : ¬ drop% ISize.toUSize_le 2 := fun h => by
  have := @h (-1) 0 (by isz); clear h; revert this; isz

-- `ISize.toUSize_le`, idx 3 (`hab : a ≤ b`): `a = 1`, `b = 0`
theorem ISize.toUSize_le.h3 : ¬ drop% ISize.toUSize_le 3 := fun h => by
  have := @h 1 0 (by isz); clear h; revert this; isz

-- `ISize.zero_le_ofNat_of_lt`, idx 1 (`ha : a < 2 ^ (System.Platform.numBits - 1)`): `a = 2^64 - 1`: `ofNat a = -1`
theorem ISize.zero_le_ofNat_of_lt.h1 : ¬ drop% ISize.zero_le_ofNat_of_lt 1 := fun h => by
  have := @h (2^64-1); clear h; revert this; isz

/-! ## Independent: kernel-checked halves (support lemmas, not verdicts) -/

-- `ISize.toInt64_ofInt`, idx 1 (`h₁ : ISize.minValue.toInt ≤ n`): holds iff `numBits = 64` (fails at `n = minValue.toInt - 1` when `numBits = 32`)
theorem ISize.toInt64_ofInt.h1_pos : System.Platform.numBits = 64 → drop% ISize.toInt64_ofInt 1 := by
  intro hnb n h₂; iszs
theorem ISize.toInt64_ofInt.h1_neg : System.Platform.numBits = 32 → ¬ drop% ISize.toInt64_ofInt 1 := fun hnb h => by
  have := @h (ISize.minValue.toInt - 1) (by iszs); clear h; revert this; iszs

-- `ISize.toInt64_ofInt`, idx 2 (`h₂ : n ≤ ISize.maxValue.toInt`): holds iff `numBits = 64` (fails at `n = maxValue.toInt + 1` when `numBits = 32`)
theorem ISize.toInt64_ofInt.h2_pos : System.Platform.numBits = 64 → drop% ISize.toInt64_ofInt 2 := by
  intro hnb n h₁; iszs
theorem ISize.toInt64_ofInt.h2_neg : System.Platform.numBits = 32 → ¬ drop% ISize.toInt64_ofInt 2 := fun hnb h => by
  have := @h (ISize.maxValue.toInt + 1) (by iszs); clear h; revert this; iszs

-- `ISize.toInt64_ofNat'`, idx 1 (`h : ↑n ≤ ISize.maxValue.toInt`): holds iff `numBits = 64` (fails at `n = 2^31` when `numBits = 32`)
theorem ISize.toInt64_ofNat'.h1_pos : System.Platform.numBits = 64 → drop% ISize.toInt64_ofNat' 1 := by
  intro hnb n; iszs
theorem ISize.toInt64_ofNat'.h1_neg : System.Platform.numBits = 32 → ¬ drop% ISize.toInt64_ofNat' 1 := fun hnb h => by
  have := @h (2^31); clear h; revert this; iszs

-- `ISize.toInt64_ofNat`, idx 1 (`h : n ≤ 2147483647`): holds iff `numBits = 64` (fails at `n = 2^31` when `numBits = 32`)
theorem ISize.toInt64_ofNat.h1_pos : System.Platform.numBits = 64 → drop% ISize.toInt64_ofNat 1 := by
  intro hnb n; iszs
theorem ISize.toInt64_ofNat.h1_neg : System.Platform.numBits = 32 → ¬ drop% ISize.toInt64_ofNat 1 := fun hnb h => by
  have := @h (2^31); clear h; revert this; iszs

-- `ISize.toInt64_neg_of_ne`, idx 1 (`hx : x ≠ ISize.minValue`): holds iff `numBits = 64` (fails at `x = minValue` when `numBits = 32`: `2^31` vs `-2^31`)
theorem ISize.toInt64_neg_of_ne.h1_pos : System.Platform.numBits = 64 → drop% ISize.toInt64_neg_of_ne 1 := by
  intro hnb x; iszs
theorem ISize.toInt64_neg_of_ne.h1_neg : System.Platform.numBits = 32 → ¬ drop% ISize.toInt64_neg_of_ne 1 := fun hnb h => by
  have := @h ISize.minValue; clear h; revert this; iszs

-- `ISize.toInt64_div_of_ne_left`, idx 2 (`ha : a ≠ ISize.minValue`): holds iff `numBits = 64` (fails at `a = minValue`, `b = -1` when `numBits = 32`)
theorem ISize.toInt64_div_of_ne_left.h2_pos : System.Platform.numBits = 64 → drop% ISize.toInt64_div_of_ne_left 2 := by
  intro hnb a b; iszs
theorem ISize.toInt64_div_of_ne_left.h2_neg : System.Platform.numBits = 32 → ¬ drop% ISize.toInt64_div_of_ne_left 2 := fun hnb h => by
  have := @h ISize.minValue (-1); clear h; revert this; iszs

-- `ISize.toInt64_div_of_ne_right`, idx 2 (`hb : b ≠ -1`): holds iff `numBits = 64` (fails at `a = minValue`, `b = -1` when `numBits = 32`)
theorem ISize.toInt64_div_of_ne_right.h2_pos : System.Platform.numBits = 64 → drop% ISize.toInt64_div_of_ne_right 2 := by
  intro hnb a b; iszs
theorem ISize.toInt64_div_of_ne_right.h2_neg : System.Platform.numBits = 32 → ¬ drop% ISize.toInt64_div_of_ne_right 2 := fun hnb h => by
  have := @h ISize.minValue (-1); clear h; revert this; iszs

-- `ISize.toInt64_ne_minValue`, idx 1 (`ha : a ≠ ISize.minValue`): holds iff `numBits = 32` (`a.toInt ≥ -2^31`; fails at `a = minValue` when `numBits = 64`)
theorem ISize.toInt64_ne_minValue.h1_pos : System.Platform.numBits = 32 → drop% ISize.toInt64_ne_minValue 1 := by
  intro hnb a; have := a.two_pow_numBits_le_toInt; iszs; omega
theorem ISize.toInt64_ne_minValue.h1_neg : System.Platform.numBits = 64 → ¬ drop% ISize.toInt64_ne_minValue 1 := fun hnb h => by
  have := @h ISize.minValue; clear h; revert this; iszs

-- `ISize.ofIntLE_int64ToInt`, idx 1 (`h₁ : ISize.minValue.toInt ≤ x.toInt`) (dependent): `∀ x : Int64, x.toInt ≤ maxValue.toInt → minValue.toInt ≤ x.toInt` holds iff `numBits = 64` (fails at `x = Int64.minValue` when `numBits = 32`)
theorem ISize.ofIntLE_int64ToInt.h1_pos : System.Platform.numBits = 64 → indep% ISize.ofIntLE_int64ToInt 1 := by
  intro hnb x h₂; have := x.le_toInt; iszs
theorem ISize.ofIntLE_int64ToInt.h1_neg : System.Platform.numBits = 32 → ¬ indep% ISize.ofIntLE_int64ToInt 1 := fun hnb h => by
  have := @h Int64.minValue (by iszs); clear h; revert this; iszs

-- `ISize.ofIntLE_int64ToInt`, idx 2 (`h₂ : x.toInt ≤ ISize.maxValue.toInt`) (dependent): `∀ x : Int64, minValue.toInt ≤ x.toInt → x.toInt ≤ maxValue.toInt` holds iff `numBits = 64` (fails at `x = Int64.maxValue` when `numBits = 32`)
theorem ISize.ofIntLE_int64ToInt.h2_pos : System.Platform.numBits = 64 → indep% ISize.ofIntLE_int64ToInt 2 := by
  intro hnb x h₁; have := x.toInt_lt; iszs; omega
theorem ISize.ofIntLE_int64ToInt.h2_neg : System.Platform.numBits = 32 → ¬ indep% ISize.ofIntLE_int64ToInt 2 := fun hnb h => by
  have := @h Int64.maxValue (by iszs); clear h; revert this; iszs

end SIntISizeHand
