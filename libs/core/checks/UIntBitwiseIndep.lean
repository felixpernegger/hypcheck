import Lean

/-! Lean support for the four platform-independent `hb` hypotheses of the UInt shift lemmas
(hand6, UIntBitwise): for each, `T'` is proved under one value of `System.Platform.numBits` and
refuted under the other. Statements are retyped; the `example`s at the end check that each retyped statement is `T'`
(`drop% T i`) up to definitional equality. -/

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


-- `UInt32.toUSize_shiftLeft_of_lt` without `hb`: holds for numBits = 32, fails for 64
example (hn : System.Platform.numBits = 32) : ∀ (a b : UInt32), (a <<< b).toUSize = (a.toUSize <<< b.toUSize) % 4294967296 := by
  intro a b
  apply USize.toNat_inj.1
  have := a.toNat_lt; have := b.toNat_lt
  simp [USize.toNat_shiftLeft, USize.toNat_mod, hn]
example (hn : System.Platform.numBits = 64) : ¬ ∀ (a b : UInt32), (a <<< b).toUSize = (a.toUSize <<< b.toUSize) % 4294967296 :=
  fun h => by have := congrArg USize.toNat (h 1 32); simp [USize.toNat_shiftLeft, USize.toNat_mod, USize.toNat_ofNat, hn] at this

-- `USize.toUInt64_shiftLeft_of_lt` without `hb`: holds for 64, fails for 32
example (hn : System.Platform.numBits = 64) : ∀ (a b : USize), (a <<< b).toUInt64 = (a.toUInt64 <<< b.toUInt64) % UInt64.ofNat USize.size := by
  intro a b
  apply UInt64.toNat_inj.1
  have := a.toNat_lt_two_pow_numBits; have := b.toNat_lt_two_pow_numBits
  simp [USize.toNat_shiftLeft, UInt64.toNat_mod, USize.size_eq_two_pow, hn] at *
example (hn : System.Platform.numBits = 32) : ¬ ∀ (a b : USize), (a <<< b).toUInt64 = (a.toUInt64 <<< b.toUInt64) % UInt64.ofNat USize.size :=
  fun h => by have := congrArg UInt64.toNat (h 1 32); simp [USize.toNat_shiftLeft, UInt64.toNat_mod, USize.size_eq_two_pow, USize.toNat_one, hn] at this

-- `UInt64.toUSize_shiftLeft` without `hb`: holds for 64, fails for 32
example (hn : System.Platform.numBits = 64) : ∀ (a b : UInt64), (a <<< b).toUSize = a.toUSize <<< b.toUSize := by
  intro a b
  apply USize.toNat_inj.1
  have := a.toNat_lt; have := b.toNat_lt
  simp [USize.toNat_shiftLeft, hn]
example (hn : System.Platform.numBits = 32) : ¬ ∀ (a b : UInt64), (a <<< b).toUSize = a.toUSize <<< b.toUSize :=
  fun h => by have := congrArg USize.toNat (h 1 32); simp [USize.toNat_shiftLeft, USize.toNat_ofNat, hn] at this

-- `USize.toUInt32_shiftLeft` without `hb`: holds for 32, fails for 64
example (hn : System.Platform.numBits = 32) : ∀ (a b : USize), (a <<< b).toUInt32 = a.toUInt32 <<< b.toUInt32 := by
  intro a b
  apply UInt32.toNat_inj.1
  have := a.toNat_lt_two_pow_numBits; have := b.toNat_lt_two_pow_numBits
  simp [USize.toNat_shiftLeft, hn] at *
  rw [Nat.mod_eq_of_lt (by omega : a.toNat < 4294967296)]
example (hn : System.Platform.numBits = 64) : ¬ ∀ (a b : USize), (a <<< b).toUInt32 = a.toUInt32 <<< b.toUInt32 :=
  fun h => by have := congrArg UInt32.toNat (h 1 32); simp [USize.toNat_shiftLeft, USize.toNat_one, hn] at this

/-! Transcription checks: the retyped statements above are `T'`. -/
example : (drop% UInt32.toUSize_shiftLeft_of_lt 2) =
    ∀ (a b : UInt32), (a <<< b).toUSize = (a.toUSize <<< b.toUSize) % 4294967296 := rfl
example : (drop% USize.toUInt64_shiftLeft_of_lt 2) =
    ∀ (a b : USize), (a <<< b).toUInt64 = (a.toUInt64 <<< b.toUInt64) % UInt64.ofNat USize.size := rfl
example : (drop% UInt64.toUSize_shiftLeft 2) =
    ∀ (a b : UInt64), (a <<< b).toUSize = a.toUSize <<< b.toUSize := rfl
example : (drop% USize.toUInt32_shiftLeft 2) =
    ∀ (a b : USize), (a <<< b).toUInt32 = a.toUInt32 <<< b.toUInt32 := rfl
