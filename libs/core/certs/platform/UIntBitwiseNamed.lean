import Lean

/-! Named copies of the `example`s in `checks/UIntBitwiseIndep.lean` (same proofs, stated with
`drop%` instead of retyped), so that the SwapCheck certificates `certs/platform/PCert*_UIntBitwiseNamed`
can refer to them. -/

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



namespace UIntBitwiseNamed

-- `UInt32.toUSize_shiftLeft_of_lt` without `hb`: holds for numBits = 32, fails for 64
theorem UInt32.toUSize_shiftLeft_of_lt.h2_pos : System.Platform.numBits = 32 → drop% UInt32.toUSize_shiftLeft_of_lt 2 := by
  intro hn a b
  apply USize.toNat_inj.1
  have := a.toNat_lt; have := b.toNat_lt
  simp [USize.toNat_shiftLeft, USize.toNat_mod, hn]
theorem UInt32.toUSize_shiftLeft_of_lt.h2_neg : System.Platform.numBits = 64 → ¬ drop% UInt32.toUSize_shiftLeft_of_lt 2 :=
  fun hn h => by have := congrArg USize.toNat (h 1 32); simp [USize.toNat_shiftLeft, USize.toNat_mod, USize.toNat_ofNat, hn] at this

-- `USize.toUInt64_shiftLeft_of_lt` without `hb`: holds for 64, fails for 32
theorem USize.toUInt64_shiftLeft_of_lt.h2_pos : System.Platform.numBits = 64 → drop% USize.toUInt64_shiftLeft_of_lt 2 := by
  intro hn a b
  apply UInt64.toNat_inj.1
  have := a.toNat_lt_two_pow_numBits; have := b.toNat_lt_two_pow_numBits
  simp [USize.toNat_shiftLeft, UInt64.toNat_mod, USize.size_eq_two_pow, hn] at *
theorem USize.toUInt64_shiftLeft_of_lt.h2_neg : System.Platform.numBits = 32 → ¬ drop% USize.toUInt64_shiftLeft_of_lt 2 :=
  fun hn h => by have := congrArg UInt64.toNat (h 1 32); simp [USize.toNat_shiftLeft, UInt64.toNat_mod, USize.size_eq_two_pow, USize.toNat_one, hn] at this

-- `UInt64.toUSize_shiftLeft` without `hb`: holds for 64, fails for 32
theorem UInt64.toUSize_shiftLeft.h2_pos : System.Platform.numBits = 64 → drop% UInt64.toUSize_shiftLeft 2 := by
  intro hn a b
  apply USize.toNat_inj.1
  have := a.toNat_lt; have := b.toNat_lt
  simp [USize.toNat_shiftLeft, hn]
theorem UInt64.toUSize_shiftLeft.h2_neg : System.Platform.numBits = 32 → ¬ drop% UInt64.toUSize_shiftLeft 2 :=
  fun hn h => by have := congrArg USize.toNat (h 1 32); simp [USize.toNat_shiftLeft, USize.toNat_ofNat, hn] at this

-- `USize.toUInt32_shiftLeft` without `hb`: holds for 32, fails for 64
theorem USize.toUInt32_shiftLeft.h2_pos : System.Platform.numBits = 32 → drop% USize.toUInt32_shiftLeft 2 := by
  intro hn a b
  apply UInt32.toNat_inj.1
  have := a.toNat_lt_two_pow_numBits; have := b.toNat_lt_two_pow_numBits
  simp [USize.toNat_shiftLeft, hn] at *
  rw [Nat.mod_eq_of_lt (by omega : a.toNat < 4294967296)]
theorem USize.toUInt32_shiftLeft.h2_neg : System.Platform.numBits = 64 → ¬ drop% USize.toUInt32_shiftLeft 2 :=
  fun hn h => by have := congrArg UInt32.toNat (h 1 32); simp [USize.toNat_shiftLeft, USize.toNat_one, hn] at this

end UIntBitwiseNamed
