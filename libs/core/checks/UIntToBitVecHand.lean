import Lean

/-!
Hand pass over cluster `UIntToBitVec` (68 hypotheses of `Init.Data.UInt.IntToBitVec`, hand6).

**No verdicts.** All 68 hypotheses are dependent (`h : System.Platform.numBits = k` occurs in the
conclusion via `toBitVec32 h`/`toBitVec64 h` or `h ▸ _`; `hn : n < USize.size` via
`USize.ofNatLT n hn`), so the verdict is decided by `∀ indep, Hᵢ`. This file proves, for each of
them, that `∀ indep, Hᵢ` is equivalent to a pure platform statement:
* the 66 `numBits = k` hypotheses: `(∀ indep, numBits = k) ↔ numBits = k` (every independent binder
  type, `USize`, `Nat`, `UInt8/16/32/64`, `Bool`, `BitVec numBits`, `Fin USize.size`, is inhabited
  on both platforms);
* the 2 `hn : n < USize.size` hypotheses of `toBitVec32_ofNatLT`/`toBitVec64_ofNatLT`, where
  `indep = {n, h}`: `(∀ n, numBits = k → n < USize.size) ↔ numBits ≠ k` (vacuous on the other
  platform, refuted by `n = USize.size` on this one).

`numBits` is `(System.Platform.getNumBits ()).val` with `getNumBits` an `opaque` constant of type
`Unit → {n // n = 32 ∨ n = 64}`; the kernel knows nothing about it beyond its type, and both
`fun _ => ⟨32, _⟩` and `fun _ => ⟨64, _⟩` are valid implementations. So `numBits = 32` and
`numBits = 64` are each neither provable nor refutable, and with the equivalences below so are all 68
`∀ indep, Hᵢ` (and their negations): the hypotheses are independent, recorded in
`runs/hand6/UIntToBitVec_independent.jsonl`. (Argument, not a Lean proof; the equivalences are
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

namespace UIntToBitVecIndep

-- USize.toBitVec32_eq_toBitVec, idx 1 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_eq_toBitVec.h1 : indep% USize.toBitVec32_eq_toBitVec 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_eq_toBitVec, idx 1 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_eq_toBitVec.h1 : indep% USize.toBitVec64_eq_toBitVec 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.le_iff_toBitVec32_le, idx 2 (h : System.Platform.numBits = 32)
theorem USize.le_iff_toBitVec32_le.h2 : indep% USize.le_iff_toBitVec32_le 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.lt_iff_toBitVec32_lt, idx 2 (h : System.Platform.numBits = 32)
theorem USize.lt_iff_toBitVec32_lt.h2 : indep% USize.lt_iff_toBitVec32_lt 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.eq_iff_toBitVec32_eq, idx 2 (h : System.Platform.numBits = 32)
theorem USize.eq_iff_toBitVec32_eq.h2 : indep% USize.eq_iff_toBitVec32_eq 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.ne_iff_toBitVec32_ne, idx 2 (h : System.Platform.numBits = 32)
theorem USize.ne_iff_toBitVec32_ne.h2 : indep% USize.ne_iff_toBitVec32_ne 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_ofNat, idx 0 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_ofNat.h0 : indep% USize.toBitVec32_ofNat 0 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_add, idx 2 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_add.h2 : indep% USize.toBitVec32_add 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_sub, idx 2 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_sub.h2 : indep% USize.toBitVec32_sub 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_mul, idx 2 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_mul.h2 : indep% USize.toBitVec32_mul 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_div, idx 2 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_div.h2 : indep% USize.toBitVec32_div 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_mod, idx 2 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_mod.h2 : indep% USize.toBitVec32_mod 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_neg, idx 1 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_neg.h1 : indep% USize.toBitVec32_neg 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_min, idx 2 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_min.h2 : indep% USize.toBitVec32_min 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_max, idx 2 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_max.h2 : indep% USize.toBitVec32_max 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_not, idx 1 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_not.h1 : indep% USize.toBitVec32_not 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_and, idx 2 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_and.h2 : indep% USize.toBitVec32_and 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_or, idx 2 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_or.h2 : indep% USize.toBitVec32_or 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_xor, idx 2 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_xor.h2 : indep% USize.toBitVec32_xor 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_shiftLeft, idx 2 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_shiftLeft.h2 : indep% USize.toBitVec32_shiftLeft 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_shiftRight, idx 2 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_shiftRight.h2 : indep% USize.toBitVec32_shiftRight 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_toUInt8, idx 1 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_toUInt8.h1 : indep% USize.toBitVec32_toUInt8 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_toUInt16, idx 1 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_toUInt16.h1 : indep% USize.toBitVec32_toUInt16 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_toUInt32, idx 1 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_toUInt32.h1 : indep% USize.toBitVec32_toUInt32 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_toUInt64, idx 1 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_toUInt64.h1 : indep% USize.toBitVec32_toUInt64 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- UInt8.toBitVec32_toUSize, idx 1 (h : System.Platform.numBits = 32)
theorem UInt8.toBitVec32_toUSize.h1 : indep% UInt8.toBitVec32_toUSize 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- UInt16.toBitVec32_toUSize, idx 1 (h : System.Platform.numBits = 32)
theorem UInt16.toBitVec32_toUSize.h1 : indep% UInt16.toBitVec32_toUSize 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- UInt32.toBitVec32_toUSize, idx 1 (h : System.Platform.numBits = 32)
theorem UInt32.toBitVec32_toUSize.h1 : indep% UInt32.toBitVec32_toUSize 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- UInt64.toBitVec32_toUSize, idx 1 (h : System.Platform.numBits = 32)
theorem UInt64.toBitVec32_toUSize.h1 : indep% UInt64.toBitVec32_toUSize 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_ofNatLT, idx 1 (hn : n < USize.size)
theorem USize.toBitVec32_ofNatLT.h1 : indep% USize.toBitVec32_ofNatLT 1 ↔ System.Platform.numBits ≠ 32 := by
  refine ⟨fun hall h => ?_, fun h _ h' => absurd h' h⟩
  have := @hall USize.size h
  omega

-- USize.toBitVec32_ofNatLT, idx 2 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_ofNatLT.h2 : indep% USize.toBitVec32_ofNatLT 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  exact @hall 0 USize.size_pos

-- USize.toBitVec32_ofFin, idx 1 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_ofFin.h1 : indep% USize.toBitVec32_ofFin 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_ofBitVec, idx 1 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_ofBitVec.h1 : indep% USize.toBitVec32_ofBitVec 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec32_pow, idx 2 (h : System.Platform.numBits = 32)
theorem USize.toBitVec32_pow.h2 : indep% USize.toBitVec32_pow 2 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- Bool.toBitVec32_toUSize, idx 1 (h : System.Platform.numBits = 32)
theorem Bool.toBitVec32_toUSize.h1 : indep% Bool.toBitVec32_toUSize 1 ↔ System.Platform.numBits = 32 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.le_iff_toBitVec64_le, idx 2 (h : System.Platform.numBits = 64)
theorem USize.le_iff_toBitVec64_le.h2 : indep% USize.le_iff_toBitVec64_le 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.lt_iff_toBitVec64_lt, idx 2 (h : System.Platform.numBits = 64)
theorem USize.lt_iff_toBitVec64_lt.h2 : indep% USize.lt_iff_toBitVec64_lt 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.eq_iff_toBitVec64_eq, idx 2 (h : System.Platform.numBits = 64)
theorem USize.eq_iff_toBitVec64_eq.h2 : indep% USize.eq_iff_toBitVec64_eq 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.ne_iff_toBitVec64_ne, idx 2 (h : System.Platform.numBits = 64)
theorem USize.ne_iff_toBitVec64_ne.h2 : indep% USize.ne_iff_toBitVec64_ne 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_ofNat, idx 0 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_ofNat.h0 : indep% USize.toBitVec64_ofNat 0 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_add, idx 2 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_add.h2 : indep% USize.toBitVec64_add 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_sub, idx 2 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_sub.h2 : indep% USize.toBitVec64_sub 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_mul, idx 2 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_mul.h2 : indep% USize.toBitVec64_mul 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_div, idx 2 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_div.h2 : indep% USize.toBitVec64_div 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_mod, idx 2 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_mod.h2 : indep% USize.toBitVec64_mod 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_neg, idx 1 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_neg.h1 : indep% USize.toBitVec64_neg 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_min, idx 2 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_min.h2 : indep% USize.toBitVec64_min 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_max, idx 2 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_max.h2 : indep% USize.toBitVec64_max 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_not, idx 1 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_not.h1 : indep% USize.toBitVec64_not 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_and, idx 2 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_and.h2 : indep% USize.toBitVec64_and 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_or, idx 2 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_or.h2 : indep% USize.toBitVec64_or 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_xor, idx 2 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_xor.h2 : indep% USize.toBitVec64_xor 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_shiftLeft, idx 2 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_shiftLeft.h2 : indep% USize.toBitVec64_shiftLeft 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_shiftRight, idx 2 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_shiftRight.h2 : indep% USize.toBitVec64_shiftRight 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_toUInt8, idx 1 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_toUInt8.h1 : indep% USize.toBitVec64_toUInt8 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_toUInt16, idx 1 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_toUInt16.h1 : indep% USize.toBitVec64_toUInt16 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_toUInt32, idx 1 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_toUInt32.h1 : indep% USize.toBitVec64_toUInt32 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_toUInt64, idx 1 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_toUInt64.h1 : indep% USize.toBitVec64_toUInt64 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- UInt8.toBitVec64_toUSize, idx 1 (h : System.Platform.numBits = 64)
theorem UInt8.toBitVec64_toUSize.h1 : indep% UInt8.toBitVec64_toUSize 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- UInt16.toBitVec64_toUSize, idx 1 (h : System.Platform.numBits = 64)
theorem UInt16.toBitVec64_toUSize.h1 : indep% UInt16.toBitVec64_toUSize 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- UInt32.toBitVec64_toUSize, idx 1 (h : System.Platform.numBits = 64)
theorem UInt32.toBitVec64_toUSize.h1 : indep% UInt32.toBitVec64_toUSize 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- UInt64.toBitVec64_toUSize, idx 1 (h : System.Platform.numBits = 64)
theorem UInt64.toBitVec64_toUSize.h1 : indep% UInt64.toBitVec64_toUSize 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_ofNatLT, idx 1 (hn : n < USize.size)
theorem USize.toBitVec64_ofNatLT.h1 : indep% USize.toBitVec64_ofNatLT 1 ↔ System.Platform.numBits ≠ 64 := by
  refine ⟨fun hall h => ?_, fun h _ h' => absurd h' h⟩
  have := @hall USize.size h
  omega

-- USize.toBitVec64_ofNatLT, idx 2 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_ofNatLT.h2 : indep% USize.toBitVec64_ofNatLT 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  exact @hall 0 USize.size_pos

-- USize.toBitVec64_ofFin, idx 1 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_ofFin.h1 : indep% USize.toBitVec64_ofFin 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_ofBitVec, idx 1 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_ofBitVec.h1 : indep% USize.toBitVec64_ofBitVec 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- USize.toBitVec64_pow, idx 2 (h : System.Platform.numBits = 64)
theorem USize.toBitVec64_pow.h2 : indep% USize.toBitVec64_pow 2 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

-- Bool.toBitVec64_toUSize, idx 1 (h : System.Platform.numBits = 64)
theorem Bool.toBitVec64_toUSize.h1 : indep% Bool.toBitVec64_toUSize 1 ↔ System.Platform.numBits = 64 := by
  refine ⟨fun hall => ?_, fun h => by intros; exact h⟩
  apply hall <;> exact default

end UIntToBitVecIndep
