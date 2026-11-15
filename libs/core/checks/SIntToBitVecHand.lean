import Lean

/-!
Hand pass over cluster `SIntToBitVec` (72 hypotheses of `Init.Data.SInt.IntToBitVec`, hand7).

**No verdicts.** All 72 hypotheses are dependent `h : System.Platform.numBits = k` hypotheses
(`h` occurs in the conclusion via `toBitVec32 h`/`toBitVec64 h`, `BitVec.cast h` or `h ▸ _`), so the
verdict is decided by `∀ indep, Hᵢ`. This file proves, for each of them,
`(∀ indep, numBits = k) ↔ numBits = k`: every independent binder type (`ISize`, `USize`, `Int`,
`Nat`, `Bool`, `Int8/16/32/64`, `BitVec numBits`) is inhabited on both platforms.

`numBits` is `(System.Platform.getNumBits ()).val` with `getNumBits` an `opaque` constant of type
`Unit → {n // n = 32 ∨ n = 64}`; the kernel knows nothing about it beyond its type, and both
`fun _ => ⟨32, _⟩` and `fun _ => ⟨64, _⟩` are valid implementations. So `numBits = 32` and
`numBits = 64` are each neither provable nor refutable, and with the equivalences below so are all 72
`∀ indep, Hᵢ` (and their negations): the hypotheses are independent, recorded in
`runs/hand7/SIntToBitVec_independent.jsonl`. (Argument, not a Lean proof; the equivalences are
kernel-checked.)

`indep% T i` elaborates to `∀ indep, Hᵢ` for hypothesis `i` of `T` (all independent binders, the
same construction as `check_hand.py`), so the statements are read off the library, not retyped.
These declarations are support lemmas, not verdicts.
-/

open Lean Meta Elab Term in
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
    let rest := xs.filter (fun y => !dep.contains y)
    mkForallFVars rest (← inferType x)

namespace SIntToBitVecIndep

-- ISize.toBitVec32_eq_toBitVec, idx 1 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_eq_toBitVec.h1 : indep% ISize.toBitVec32_eq_toBitVec 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_eq_toBitVec, idx 1 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_eq_toBitVec.h1 : indep% ISize.toBitVec64_eq_toBitVec 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.le_iff_toBitVec32_sle, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.le_iff_toBitVec32_sle.h2 : indep% ISize.le_iff_toBitVec32_sle 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.lt_iff_toBitVec32_slt, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.lt_iff_toBitVec32_slt.h2 : indep% ISize.lt_iff_toBitVec32_slt 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.eq_iff_toBitVec32_eq, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.eq_iff_toBitVec32_eq.h2 : indep% ISize.eq_iff_toBitVec32_eq 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.ne_iff_toBitVec32_ne, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.ne_iff_toBitVec32_ne.h2 : indep% ISize.ne_iff_toBitVec32_ne 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_ofNat, idx 0 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_ofNat.h0 : indep% ISize.toBitVec32_ofNat 0 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_ofInt, idx 1 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_ofInt.h1 : indep% ISize.toBitVec32_ofInt 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_add, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_add.h2 : indep% ISize.toBitVec32_add 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_sub, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_sub.h2 : indep% ISize.toBitVec32_sub 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_mul, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_mul.h2 : indep% ISize.toBitVec32_mul 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_div, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_div.h2 : indep% ISize.toBitVec32_div 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_mod, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_mod.h2 : indep% ISize.toBitVec32_mod 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_min, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_min.h2 : indep% ISize.toBitVec32_min 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_max, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_max.h2 : indep% ISize.toBitVec32_max 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_neg, idx 1 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_neg.h1 : indep% ISize.toBitVec32_neg 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_not, idx 1 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_not.h1 : indep% ISize.toBitVec32_not 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_and, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_and.h2 : indep% ISize.toBitVec32_and 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_or, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_or.h2 : indep% ISize.toBitVec32_or 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_xor, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_xor.h2 : indep% ISize.toBitVec32_xor 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_shiftLeft, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_shiftLeft.h2 : indep% ISize.toBitVec32_shiftLeft 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_shiftRight, idx 2 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_shiftRight.h2 : indep% ISize.toBitVec32_shiftRight 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_abs, idx 1 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_abs.h1 : indep% ISize.toBitVec32_abs 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_toInt8, idx 1 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_toInt8.h1 : indep% ISize.toBitVec32_toInt8 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_toInt16, idx 1 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_toInt16.h1 : indep% ISize.toBitVec32_toInt16 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_toInt32, idx 1 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_toInt32.h1 : indep% ISize.toBitVec32_toInt32 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_toInt64, idx 1 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_toInt64.h1 : indep% ISize.toBitVec32_toInt64 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_toUSize, idx 1 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_toUSize.h1 : indep% ISize.toBitVec32_toUSize 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_toISize, idx 1 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_toISize.h1 : indep% USize.toBitVec32_toISize 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- Int8.toBitVec32_toISize, idx 1 (h : System.Platform.numBits = 32)
theorem Int8.toBitVec32_toISize.h1 : indep% Int8.toBitVec32_toISize 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- Int16.toBitVec32_toISize, idx 1 (h : System.Platform.numBits = 32)
theorem Int16.toBitVec32_toISize.h1 : indep% Int16.toBitVec32_toISize 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- Int32.toBitVec32_toISize, idx 1 (h : System.Platform.numBits = 32)
theorem Int32.toBitVec32_toISize.h1 : indep% Int32.toBitVec32_toISize 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- Int64.toBitVec32_toISize, idx 1 (h : System.Platform.numBits = 32)
theorem Int64.toBitVec32_toISize.h1 : indep% Int64.toBitVec32_toISize 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_ofBitVec, idx 1 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_ofBitVec.h1 : indep% ISize.toBitVec32_ofBitVec 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_minValue, idx 0 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_minValue.h0 : indep% ISize.toBitVec32_minValue 0 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec32_maxValue, idx 0 (h : System.Platform.numBits = 32)
theorem ISize.toBitVec32_maxValue.h0 : indep% ISize.toBitVec32_maxValue 0 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- Bool.toBitVec32_toISize, idx 1 (h : System.Platform.numBits = 32)
theorem Bool.toBitVec32_toISize.h1 : indep% Bool.toBitVec32_toISize 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.le_iff_toBitVec64_sle, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.le_iff_toBitVec64_sle.h2 : indep% ISize.le_iff_toBitVec64_sle 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.lt_iff_toBitVec64_slt, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.lt_iff_toBitVec64_slt.h2 : indep% ISize.lt_iff_toBitVec64_slt 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.eq_iff_toBitVec64_eq, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.eq_iff_toBitVec64_eq.h2 : indep% ISize.eq_iff_toBitVec64_eq 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.ne_iff_toBitVec64_ne, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.ne_iff_toBitVec64_ne.h2 : indep% ISize.ne_iff_toBitVec64_ne 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_ofNat, idx 0 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_ofNat.h0 : indep% ISize.toBitVec64_ofNat 0 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_ofInt, idx 1 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_ofInt.h1 : indep% ISize.toBitVec64_ofInt 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_add, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_add.h2 : indep% ISize.toBitVec64_add 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_sub, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_sub.h2 : indep% ISize.toBitVec64_sub 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_mul, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_mul.h2 : indep% ISize.toBitVec64_mul 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_div, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_div.h2 : indep% ISize.toBitVec64_div 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_mod, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_mod.h2 : indep% ISize.toBitVec64_mod 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_min, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_min.h2 : indep% ISize.toBitVec64_min 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_max, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_max.h2 : indep% ISize.toBitVec64_max 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_neg, idx 1 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_neg.h1 : indep% ISize.toBitVec64_neg 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_not, idx 1 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_not.h1 : indep% ISize.toBitVec64_not 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_and, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_and.h2 : indep% ISize.toBitVec64_and 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_or, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_or.h2 : indep% ISize.toBitVec64_or 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_xor, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_xor.h2 : indep% ISize.toBitVec64_xor 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_shiftLeft, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_shiftLeft.h2 : indep% ISize.toBitVec64_shiftLeft 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_shiftRight, idx 2 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_shiftRight.h2 : indep% ISize.toBitVec64_shiftRight 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_abs, idx 1 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_abs.h1 : indep% ISize.toBitVec64_abs 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_toInt8, idx 1 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_toInt8.h1 : indep% ISize.toBitVec64_toInt8 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_toInt16, idx 1 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_toInt16.h1 : indep% ISize.toBitVec64_toInt16 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_toInt32, idx 1 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_toInt32.h1 : indep% ISize.toBitVec64_toInt32 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_toInt64, idx 1 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_toInt64.h1 : indep% ISize.toBitVec64_toInt64 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_toUSize, idx 1 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_toUSize.h1 : indep% ISize.toBitVec64_toUSize 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_toISize, idx 1 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_toISize.h1 : indep% USize.toBitVec64_toISize 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- Int8.toBitVec64_toISize, idx 1 (h : System.Platform.numBits = 64)
theorem Int8.toBitVec64_toISize.h1 : indep% Int8.toBitVec64_toISize 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- Int16.toBitVec64_toISize, idx 1 (h : System.Platform.numBits = 64)
theorem Int16.toBitVec64_toISize.h1 : indep% Int16.toBitVec64_toISize 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- Int32.toBitVec64_toISize, idx 1 (h : System.Platform.numBits = 64)
theorem Int32.toBitVec64_toISize.h1 : indep% Int32.toBitVec64_toISize 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- Int64.toBitVec64_toISize, idx 1 (h : System.Platform.numBits = 64)
theorem Int64.toBitVec64_toISize.h1 : indep% Int64.toBitVec64_toISize 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_ofBitVec, idx 1 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_ofBitVec.h1 : indep% ISize.toBitVec64_ofBitVec 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_minValue, idx 0 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_minValue.h0 : indep% ISize.toBitVec64_minValue 0 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- ISize.toBitVec64_maxValue, idx 0 (h : System.Platform.numBits = 64)
theorem ISize.toBitVec64_maxValue.h0 : indep% ISize.toBitVec64_maxValue 0 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- Bool.toBitVec64_toISize, idx 1 (h : System.Platform.numBits = 64)
theorem Bool.toBitVec64_toISize.h1 : indep% Bool.toBitVec64_toISize 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

end SIntToBitVecIndep
