import Lean.Elab.Command
-- add the library modules your rows need here (e.g. `import Init`, `import Std.Sat.AIG.CNF`); avoid `import Lean`/`import Std` (1.5 GB)
import Init
import Std.Data.String.ToNat

/-!
Hand pass StrDec (hand22, 2026-11-08): 62 hypotheses of private theorems in Init.Data.String.Decode
(UTF-8 decoding: parseFirstByte, assemble₁..₄, utf8DecodeChar?), Init.Data.String.Basic
(push_induction.append_singleton_induction) and Std.Data.String.ToNat (NoRepetition).
55 necessary, 7 removable.

Reusable models (all built here; everything evaluates with decide in the kernel):
- characters 'a' (1 byte), 'é' = U+00E9 (2 bytes), Char.ofNat 0x800 (3 bytes), Char.ofNat 0x10000 and
  Char.ofNat 0x40000 (4 bytes);
- bytes: 0x80 is a continuation byte and no first byte (parseFirstByte 0x80 = invalid), 0 and 0x61 are
  one-byte first bytes, 0xC3 starts two bytes; assembleₖ with a zero leading payload and 0x80
  continuation bytes is overlong (none), with leading payload 1 it gives U+0080 / U+1000 / U+40000;
- byte arrays ByteArray.mk #[0x80] (no decode), #[0xC3, 0xA9] (decodes to 'é'), #[0x61, 0x80, 0x80(, 0x80)]
  (decodes to 'a' while assemble₃/assemble₄ give U+1000/U+40000);
- FirstByte has no DecidableEq: compare constructor indices (StrDecHand.fb_ne);
- NoRepetition is a private structure: go through the private noRepetition_iff (priv%) and decide on
  List Nat infixes ([0, 0], [1, 1, 0, 1]).

Run with the lean4 repo's stage1 binary: runs/hand22/lean.sh checks/StrDecHand.lean.
-/

set_option linter.unusedVariables false

open Lean Meta Elab Term

/-- `_private.M.«0».x` ↦ `_private.M.0.x`: all-digit string components become numeric. -/
def hcFixName : Name → Name
  | .str p s => if !s.isEmpty && s.all Char.isDigit then .num (hcFixName p) s.toNat! else .str (hcFixName p) s
  | .num p k => .num (hcFixName p) k
  | .anonymous => .anonymous

/-- The constant named by `T`: a public name (resolved as usual) or a private one written in full
as `_private.Mod.«0».x` (private names are not reachable by their short name from another module). -/
def hcConst (T : Ident) : TermElabM Name := do
  let n := hcFixName T.getId
  if isPrivateName n then
    unless (← getEnv).contains n do throwError "unknown private constant {n}"
    return n
  realizeGlobalConstNoOverloadWithInfo T

/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep% T i`: `∀ indep, Hᵢ` for the dependent Prop binder `i` of `T` (all independent binders). -/
elab "indep% " T:ident i:num : term => do
  let n ← hcConst T
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

/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← hcConst T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
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

/-- `priv% c`: the constant `c` (public, or private written as `_private.Mod.«0».x`), with fresh
universe levels; use it to mention private definitions and lemmas inside statements and proofs. -/
elab "priv% " c:ident : term => do
  mkConstWithFreshMVarLevels (← hcConst c)

open ByteArray.utf8DecodeChar?

namespace StrDecHand

-- helper: distinct constructor indices (FirstByte has no DecidableEq instance)
theorem fb_ne {a b : FirstByte} (h : a.ctorIdx ≠ b.ctorIdx) : a ≠ b := fun e => h (e ▸ rfl)

/-! ## Char / utf8EncodeChar -/

-- `Char.toBitVec_val_of_utf8Size_eq_one`: c = 'é' (233 needs 8 bits).
theorem toBitVec_val_of_utf8Size_eq_one_1 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».Char.toBitVec_val_of_utf8Size_eq_one 1 := by
  intro h; have := @h 'é'; revert this; decide

-- `Char.toBitVec_val_of_utf8Size_eq_two`: c = U+0800 (needs 12 bits).
theorem toBitVec_val_of_utf8Size_eq_two_1 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».Char.toBitVec_val_of_utf8Size_eq_two 1 := by
  intro h; have := @h (Char.ofNat 0x800); revert this; decide

-- `Char.toBitVec_val_of_utf8Size_eq_three`: c = U+10000 (needs 17 bits).
theorem toBitVec_val_of_utf8Size_eq_three_1 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».Char.toBitVec_val_of_utf8Size_eq_three 1 := by
  intro h; have := @h (Char.ofNat 0x10000); revert this; decide

-- `String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_one` (dependent): 'é' has utf8Size 2.
theorem toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_one_1 :
    ¬ indep0% _private.Init.Data.String.Decode.«0».String.toBitVec_getElem_utf8EncodeChar_zero_of_utf8Size_eq_one 1 := by
  intro h; have := @h 'é'; revert this; decide

-- `String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_one`: 'é' encodes to two bytes.
theorem map_toBitVec_utf8EncodeChar_of_utf8Size_eq_one_1 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».String.map_toBitVec_utf8EncodeChar_of_utf8Size_eq_one 1 := by
  intro h; have := @h 'é'; revert this; decide

/-! ## parseFirstByte -/

-- `ByteArray.utf8DecodeChar?.parseFirstByte_eq_invalid_of_isUTF8ContinuationByte`: b = 0 parses as done.
theorem parseFirstByte_eq_invalid_of_isUTF8ContinuationByte_1 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.parseFirstByte_eq_invalid_of_isUTF8ContinuationByte 1 := by
  intro h; have := @h 0; exact fb_ne (by decide) this

-- `ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_done`: c = 'é', first byte 0xC3 is oneMore.
theorem parseFirstByte_utf8EncodeChar_eq_done_1 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_done 1 := by
  intro h; have := @h 'é'; exact fb_ne (by decide) this

-- `ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_oneMore`: c = 'a' is done.
theorem parseFirstByte_utf8EncodeChar_eq_oneMore_1 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_oneMore 1 := by
  intro h; have := @h 'a'; exact fb_ne (by decide) this

-- `ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_twoMore`: c = 'a' is done.
theorem parseFirstByte_utf8EncodeChar_eq_twoMore_1 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_twoMore 1 := by
  intro h; have := @h 'a'; exact fb_ne (by decide) this

-- `ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_threeMore`: c = 'a' is done.
theorem parseFirstByte_utf8EncodeChar_eq_threeMore_1 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.parseFirstByte_utf8EncodeChar_eq_threeMore 1 := by
  intro h; have := @h 'a'; exact fb_ne (by decide) this

/-! ## assemble₁ -/

-- `ByteArray.utf8DecodeChar?.toBitVec_val_assemble₁` (dependent): w = 128 is not a one-byte first byte.
theorem toBitVec_val_assemble₁_1 :
    ¬ indep0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.toBitVec_val_assemble₁ 1 := by
  intro h; have := @h 128 'a'; exact fb_ne (by decide) this

-- `ByteArray.utf8DecodeChar?.utf8Size_assemble₁` (dependent): w = 128.
theorem utf8Size_assemble₁_2 :
    ¬ indep0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.utf8Size_assemble₁ 2 := by
  intro h; have := @h 128 'a'; exact fb_ne (by decide) this

-- `ByteArray.utf8DecodeChar?.utf8Size_assemble₁`: w = 0, c = 'é' (utf8Size 2).
theorem utf8Size_assemble₁_3 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.utf8Size_assemble₁ 3 := by
  intro h; have := @h 0 'é' rfl; revert this; decide

-- `ByteArray.utf8DecodeChar?.val_assemble₁_le` (dependent): w = 128.
theorem val_assemble₁_le_1 :
    ¬ indep0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.val_assemble₁_le 1 := by
  intro h; have := @h 128 'a'; exact fb_ne (by decide) this

-- `ByteArray.utf8DecodeChar?.val_assemble₁_le`: w = 0, c = 'é' (233 > 127).
theorem val_assemble₁_le_3 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.val_assemble₁_le 3 := by
  intro h; have := @h 0 rfl 'é'; revert this; decide

-- `ByteArray.utf8DecodeChar?.verify₁_eq_isSome_assemble₁` (dependent): w = 128.
theorem verify₁_eq_isSome_assemble₁_1 :
    ¬ indep0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.verify₁_eq_isSome_assemble₁ 1 := by
  intro h; have := @h 128; exact fb_ne (by decide) this

/-! ## assemble₂ / assemble₃ / assemble₄ -/

-- `ByteArray.utf8DecodeChar?.val_assemble₂_le`: c = U+0800 (2048 > 2047).
theorem val_assemble₂_le_3 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.val_assemble₂_le 3 := by
  intro h; have := @h 0 0 (Char.ofNat 0x800); revert this; decide

-- `ByteArray.utf8DecodeChar?.val_assemble₃_le`: c = U+10000 (> 0xffff).
theorem val_assemble₃_le_4 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.val_assemble₃_le 4 := by
  intro h; have := @h 0 0 0 (Char.ofNat 0x10000); revert this; decide

-- `ByteArray.utf8DecodeChar?.helper₆`: c = 'a', o = some 'b', b = 'b'.val.toBitVec.
theorem helper₆_3 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.helper₆ 3 := by
  intro h
  have := @h 'a' (some 'b') 'b'.val.toBitVec (by rintro d ⟨⟩; rfl) rfl
  revert this; decide

-- `ByteArray.utf8DecodeChar?.assemble₂_eq_some_of_toBitVec`: w = 2, x = 0 (no continuation byte), c = U+0080.
theorem assemble₂_eq_some_of_toBitVec_2 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.assemble₂_eq_some_of_toBitVec 2 := by
  intro h; have := @h 2 0 (Char.ofNat 0x80) (by decide) (by decide); revert this; decide

-- `ByteArray.utf8DecodeChar?.assemble₂_eq_some_of_toBitVec`: w = 0, x = 0x80, c = U+0000 (overlong).
theorem assemble₂_eq_some_of_toBitVec_4 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.assemble₂_eq_some_of_toBitVec 4 := by
  intro h; have := @h 0 0x80 (by decide) (Char.ofNat 0) (by decide); revert this; decide

-- `ByteArray.utf8DecodeChar?.assemble₂_eq_some_of_toBitVec`: w = 0, x = 0x80 (decodes to none), c = U+0080.
theorem assemble₂_eq_some_of_toBitVec_5 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.assemble₂_eq_some_of_toBitVec 5 := by
  intro h; have := @h 0 0x80 (by decide) (Char.ofNat 0x80) (by decide); revert this; decide

-- `ByteArray.utf8DecodeChar?.assemble₃_eq_some_of_toBitVec`: w = 1, x = 0, y = 0x80, c = U+1000.
theorem assemble₃_eq_some_of_toBitVec_3 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.assemble₃_eq_some_of_toBitVec 3 := by
  intro h; have := @h 1 0 0x80 (by decide) (Char.ofNat 0x1000) (by decide) (by decide); revert this; decide

-- `ByteArray.utf8DecodeChar?.assemble₃_eq_some_of_toBitVec`: w = 1, x = 0x80, y = 0, c = U+1000.
theorem assemble₃_eq_some_of_toBitVec_4 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.assemble₃_eq_some_of_toBitVec 4 := by
  intro h; have := @h 1 0x80 0 (by decide) (Char.ofNat 0x1000) (by decide) (by decide); revert this; decide

-- `ByteArray.utf8DecodeChar?.assemble₃_eq_some_of_toBitVec`: w = 0, x = y = 0x80, c = U+0000 (overlong).
theorem assemble₃_eq_some_of_toBitVec_6 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.assemble₃_eq_some_of_toBitVec 6 := by
  intro h; have := @h 0 0x80 0x80 (by decide) (by decide) (Char.ofNat 0) (by decide); revert this; decide

-- `ByteArray.utf8DecodeChar?.assemble₃_eq_some_of_toBitVec`: w = 0, x = y = 0x80 (decodes to none), c = U+0800.
theorem assemble₃_eq_some_of_toBitVec_7 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.assemble₃_eq_some_of_toBitVec 7 := by
  intro h; have := @h 0 0x80 0x80 (by decide) (by decide) (Char.ofNat 0x800) (by decide); revert this; decide

-- `ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec`: w = 1, x = 0, y = z = 0x80, c = U+40000.
theorem assemble₄_eq_some_of_toBitVec_4 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec 4 := by
  intro h
  have := @h 1 0 0x80 0x80 (by decide) (by decide) (Char.ofNat 0x40000) (by decide) (by decide)
  revert this; decide

-- `ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec`: w = 1, y = 0, x = z = 0x80, c = U+40000.
theorem assemble₄_eq_some_of_toBitVec_5 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec 5 := by
  intro h
  have := @h 1 0x80 0 0x80 (by decide) (by decide) (Char.ofNat 0x40000) (by decide) (by decide)
  revert this; decide

-- `ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec`: w = 1, z = 0, x = y = 0x80, c = U+40000.
theorem assemble₄_eq_some_of_toBitVec_6 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec 6 := by
  intro h
  have := @h 1 0x80 0x80 0 (by decide) (by decide) (Char.ofNat 0x40000) (by decide) (by decide)
  revert this; decide

-- `ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec`: w = 0, x = y = z = 0x80, c = U+0000 (overlong).
theorem assemble₄_eq_some_of_toBitVec_8 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec 8 := by
  intro h
  have := @h 0 0x80 0x80 0x80 (by decide) (by decide) (by decide) (Char.ofNat 0) (by decide)
  revert this; decide

-- `ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec`: w = 0, x = y = z = 0x80 (decodes to none), c = U+10000.
theorem assemble₄_eq_some_of_toBitVec_9 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.assemble₄_eq_some_of_toBitVec 9 := by
  intro h
  have := @h 0 0x80 0x80 0x80 (by decide) (by decide) (by decide) (Char.ofNat 0x10000) (by decide)
  revert this; decide

/-! ## helper₃ (removable) -/

-- `ByteArray.utf8DecodeChar?.helper₃`: removable; for n ≥ 8 the mask UInt8.ofNat (2 ^ n - 1) is
-- 255, so both sides are x zero-extended to 32 bits.
theorem helper₃_2 : drop% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.helper₃ 2 := by
  intro x n
  by_cases hn : n < 8
  · exact (priv% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar?.helper₃) n hn
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    have hm : UInt8.ofNat (2 ^ (k + 8) - 1) = 255 := by
      apply UInt8.toNat_inj.1
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      simp only [UInt8.toNat_ofNat', Nat.pow_add, Nat.reducePow, UInt8.reduceToNat]
      omega
    have hx : x &&& 255 = x := by revert x; decide
    rw [hm, hx]
    apply BitVec.eq_of_toNat_eq
    have : x.toNat < 2 ^ (k + 8) := by
      have := x.toNat_lt; rw [Nat.pow_add]; have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      simp at *; omega
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt this]

/-! ## utf8DecodeChar? -/

-- `parseFirstByte_eq_done_of_utf8DecodeChar?_eq_some`: b = [0x80], i = 0, c = 'a'.
theorem parseFirstByte_eq_done_of_utf8DecodeChar?_eq_some_3 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».parseFirstByte_eq_done_of_utf8DecodeChar?_eq_some 3 := by
  intro h; have := @h (ByteArray.mk #[0x80]) 0 'a' (by decide) (by decide); exact fb_ne (by decide) this

-- `parseFirstByte_eq_done_of_utf8DecodeChar?_eq_some`: b = [0xC3, 0xA9] decodes to 'é'.
theorem parseFirstByte_eq_done_of_utf8DecodeChar?_eq_some_4 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».parseFirstByte_eq_done_of_utf8DecodeChar?_eq_some 4 := by
  intro h; have := @h (ByteArray.mk #[0xC3, 0xA9]) 0 'é' (by decide) (by decide); exact fb_ne (by decide) this

-- `parseFirstByte_eq_done_of_utf8DecodeChar?_eq_some` (dependent): removable (derivable), a successful
-- decode at i implies i < b.size.
theorem parseFirstByte_eq_done_of_utf8DecodeChar?_eq_some_5 :
    indep% _private.Init.Data.String.Decode.«0».parseFirstByte_eq_done_of_utf8DecodeChar?_eq_some 5 :=
  by intro b i c h _; exact ByteArray.lt_size_of_isSome_utf8DecodeChar? (by simp [h])

-- `parseFirstByte_eq_oneMore_of_utf8DecodeChar?_eq_some`: b = [0x80], i = 0, c = 'é'.
theorem parseFirstByte_eq_oneMore_of_utf8DecodeChar?_eq_some_3 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».parseFirstByte_eq_oneMore_of_utf8DecodeChar?_eq_some 3 := by
  intro h; have := @h (ByteArray.mk #[0x80]) 0 'é' (by decide) (by decide); exact fb_ne (by decide) this

-- `parseFirstByte_eq_oneMore_of_utf8DecodeChar?_eq_some`: b = [0x61] decodes to 'a'.
theorem parseFirstByte_eq_oneMore_of_utf8DecodeChar?_eq_some_4 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».parseFirstByte_eq_oneMore_of_utf8DecodeChar?_eq_some 4 := by
  intro h; have := @h (ByteArray.mk #[0x61]) 0 'a' (by decide) (by decide); exact fb_ne (by decide) this

-- `parseFirstByte_eq_oneMore_of_utf8DecodeChar?_eq_some` (dependent): removable (derivable), a successful
-- decode at i implies i < b.size.
theorem parseFirstByte_eq_oneMore_of_utf8DecodeChar?_eq_some_5 :
    indep% _private.Init.Data.String.Decode.«0».parseFirstByte_eq_oneMore_of_utf8DecodeChar?_eq_some 5 :=
  by intro b i c h _; exact ByteArray.lt_size_of_isSome_utf8DecodeChar? (by simp [h])

-- `parseFirstByte_eq_twoMore_of_utf8DecodeChar?_eq_some`: b = [0x80], i = 0, c = U+0800.
theorem parseFirstByte_eq_twoMore_of_utf8DecodeChar?_eq_some_3 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».parseFirstByte_eq_twoMore_of_utf8DecodeChar?_eq_some 3 := by
  intro h; have := @h (ByteArray.mk #[0x80]) 0 (Char.ofNat 0x800) (by decide) (by decide); exact fb_ne (by decide) this

-- `parseFirstByte_eq_twoMore_of_utf8DecodeChar?_eq_some`: b = [0x61] decodes to 'a'.
theorem parseFirstByte_eq_twoMore_of_utf8DecodeChar?_eq_some_4 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».parseFirstByte_eq_twoMore_of_utf8DecodeChar?_eq_some 4 := by
  intro h; have := @h (ByteArray.mk #[0x61]) 0 'a' (by decide) (by decide); exact fb_ne (by decide) this

-- `parseFirstByte_eq_twoMore_of_utf8DecodeChar?_eq_some` (dependent): removable (derivable), a successful
-- decode at i implies i < b.size.
theorem parseFirstByte_eq_twoMore_of_utf8DecodeChar?_eq_some_5 :
    indep% _private.Init.Data.String.Decode.«0».parseFirstByte_eq_twoMore_of_utf8DecodeChar?_eq_some 5 :=
  by intro b i c h _; exact ByteArray.lt_size_of_isSome_utf8DecodeChar? (by simp [h])

-- `parseFirstByte_eq_threeMore_of_utf8DecodeChar?_eq_some`: b = [0x80], i = 0, c = U+10000.
theorem parseFirstByte_eq_threeMore_of_utf8DecodeChar?_eq_some_3 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».parseFirstByte_eq_threeMore_of_utf8DecodeChar?_eq_some 3 := by
  intro h; have := @h (ByteArray.mk #[0x80]) 0 (Char.ofNat 0x10000) (by decide) (by decide); exact fb_ne (by decide) this

-- `parseFirstByte_eq_threeMore_of_utf8DecodeChar?_eq_some`: b = [0x61] decodes to 'a'.
theorem parseFirstByte_eq_threeMore_of_utf8DecodeChar?_eq_some_4 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».parseFirstByte_eq_threeMore_of_utf8DecodeChar?_eq_some 4 := by
  intro h; have := @h (ByteArray.mk #[0x61]) 0 'a' (by decide) (by decide); exact fb_ne (by decide) this

-- `parseFirstByte_eq_threeMore_of_utf8DecodeChar?_eq_some` (dependent): removable (derivable), a successful
-- decode at i implies i < b.size.
theorem parseFirstByte_eq_threeMore_of_utf8DecodeChar?_eq_some_5 :
    indep% _private.Init.Data.String.Decode.«0».parseFirstByte_eq_threeMore_of_utf8DecodeChar?_eq_some 5 :=
  by intro b i c h _; exact ByteArray.lt_size_of_isSome_utf8DecodeChar? (by simp [h])

-- `utf8DecodeChar?_eq_assemble₁` (dependent): b = [0x80].
theorem utf8DecodeChar?_eq_assemble₁_2 :
    ¬ indep0% _private.Init.Data.String.Decode.«0».utf8DecodeChar?_eq_assemble₁ 2 := by
  intro h; have := @h (ByteArray.mk #[0x80]) (by decide); exact fb_ne (by decide) this

-- `utf8DecodeChar?_eq_assemble₃`: b = [0x61, 0x80, 0x80] decodes to 'a', assemble₃ gives U+1000.
theorem utf8DecodeChar?_eq_assemble₃_2 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».utf8DecodeChar?_eq_assemble₃ 2 := by
  intro h; have := @h (ByteArray.mk #[0x61, 0x80, 0x80]) (by decide); revert this; decide

-- `utf8DecodeChar?_eq_assemble₄`: b = [0x61, 0x80, 0x80, 0x80] decodes to 'a', assemble₄ gives U+40000.
theorem utf8DecodeChar?_eq_assemble₄_2 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».utf8DecodeChar?_eq_assemble₄ 2 := by
  intro h; have := @h (ByteArray.mk #[0x61, 0x80, 0x80, 0x80]) (by decide); revert this; decide

-- `utf8DecodeChar?_append_eq_assemble₁` (dependent): l = [0x80].
theorem utf8DecodeChar?_append_eq_assemble₁_3 :
    ¬ indep0% _private.Init.Data.String.Decode.«0».utf8DecodeChar?_append_eq_assemble₁ 3 := by
  intro h; have := @h [0x80] ByteArray.empty rfl; exact fb_ne (by decide) this

-- `utf8DecodeChar?_append_eq_assemble₄`: l = [0x61, 0x80, 0x80, 0x80], b empty.
theorem utf8DecodeChar?_append_eq_assemble₄_3 :
    ¬ drop0% _private.Init.Data.String.Decode.«0».utf8DecodeChar?_append_eq_assemble₄ 3 := by
  intro h; have := @h [0x61, 0x80, 0x80, 0x80] ByteArray.empty rfl; revert this; decide

-- `ByteArray.utf8DecodeChar_extract_congr_of_le` (dependent): removable (derivable), a successful decode
-- of bytes.extract i j stays successful after appending bytes.extract j j' when j ≤ j'.
theorem utf8DecodeChar_extract_congr_of_le_5 :
    indep% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar_extract_congr_of_le 5 := by
  intro bytes i j j' h hj
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
  have hij : i ≤ j := by
    have := ByteArray.lt_size_of_isSome_utf8DecodeChar? h
    simp only [ByteArray.size_extract] at this
    omega
  have := ByteArray.utf8DecodeChar?_append_eq_some hc (bytes.extract j j')
  rw [← ByteArray.extract_eq_extract_append_extract j hij hj] at this
  simp [this]

-- `ByteArray.utf8DecodeChar_extract_congr_of_le`: removable; this is the public
-- ByteArray.utf8DecodeChar_extract_congr (both decodes succeed, so they agree in either order).
theorem utf8DecodeChar_extract_congr_of_le_6 :
    drop% _private.Init.Data.String.Decode.«0».ByteArray.utf8DecodeChar_extract_congr_of_le 6 :=
  fun i j j' => ByteArray.utf8DecodeChar_extract_congr i j j'

-- `UInt8.utf8ByteSize_eq_utf8ByteSize_parseFirstByte` (dependent): c = 128 is not a first byte.
theorem utf8ByteSize_eq_utf8ByteSize_parseFirstByte_1 :
    ¬ indep0% _private.Init.Data.String.Decode.«0».UInt8.utf8ByteSize_eq_utf8ByteSize_parseFirstByte 1 := by
  intro h; have := @h 128; revert this; decide

/-! ## Init.Data.String.Basic -/

-- `String.push_induction.append_singleton_induction`: motive = fun _ => False, l = [].
theorem append_singleton_induction_2 :
    ¬ drop0% _private.Init.Data.String.Basic.«0».String.push_induction.append_singleton_induction 2 := by
  intro h; exact @h [] (fun _ => False) (fun _ _ x => x)

-- `String.push_induction.append_singleton_induction`: motive = (· = []), l = ['a'].
theorem append_singleton_induction_3 :
    ¬ drop0% _private.Init.Data.String.Basic.«0».String.push_induction.append_singleton_induction 3 := by
  intro h; exact absurd (@h ['a'] (· = []) rfl) (by simp)

/-! ## Std.Data.String.ToNat (NoRepetition a l is ¬ [a, a] <:+: l, via the private noRepetition_iff) -/

-- `NoRepetition.right_of_append`: l = [], m = [0, 0].
theorem right_of_append_4 :
    ¬ drop0% _private.Std.Data.String.ToNat.«0».NoRepetition.right_of_append 4 := by
  intro h; exact (priv% _private.Std.Data.String.ToNat.«0».noRepetition_iff).1 (@h Nat 0 [] [0, 0]) (by decide)

-- `NoRepetition.left_of_append`: l = [0, 0], m = [].
theorem left_of_append_4 :
    ¬ drop0% _private.Std.Data.String.ToNat.«0».NoRepetition.left_of_append 4 := by
  intro h; exact (priv% _private.Std.Data.String.ToNat.«0».noRepetition_iff).1 (@h Nat 0 [0, 0] []) (by decide)

-- `NoRepetition.append_singleton_of_not_suffix`: a = 1, l = [1, 1, 0].
theorem append_singleton_of_not_suffix_3 :
    ¬ drop0% _private.Std.Data.String.ToNat.«0».NoRepetition.append_singleton_of_not_suffix 3 := by
  intro h; exact (priv% _private.Std.Data.String.ToNat.«0».noRepetition_iff).1 (@h Nat 1 [1, 1, 0] (by decide)) (by decide)

-- `NoRepetition.append_singleton_of_not_suffix`: a = 0, l = [0].
theorem append_singleton_of_not_suffix_4 :
    ¬ drop0% _private.Std.Data.String.ToNat.«0».NoRepetition.append_singleton_of_not_suffix 4 := by
  intro h; exact (priv% _private.Std.Data.String.ToNat.«0».noRepetition_iff).1 (@h Nat 0 [0] ((priv% _private.Std.Data.String.ToNat.«0».noRepetition_iff).2 (by decide))) (by decide)

-- `NoRepetition.append_singleton_of_ne`: a = 0, b = 1, l = [0, 0].
theorem append_singleton_of_ne_4 :
    ¬ drop0% _private.Std.Data.String.ToNat.«0».NoRepetition.append_singleton_of_ne 4 := by
  intro h; exact (priv% _private.Std.Data.String.ToNat.«0».noRepetition_iff).1 (@h Nat 0 1 [0, 0] (by decide)) (by decide)

-- `NoRepetition.append_singleton_of_ne`: a = b = 0, l = [0].
theorem append_singleton_of_ne_5 :
    ¬ drop0% _private.Std.Data.String.ToNat.«0».NoRepetition.append_singleton_of_ne 5 := by
  intro h; exact (priv% _private.Std.Data.String.ToNat.«0».noRepetition_iff).1 (@h Nat 0 0 [0] ((priv% _private.Std.Data.String.ToNat.«0».noRepetition_iff).2 (by decide))) (by decide)

-- `noRepetition_append_cons_of_noRepetition_append_singleton`: a = 0, l = [0], m = [].
theorem noRepetition_append_cons_of_noRepetition_append_singleton_4 :
    ¬ drop0% _private.Std.Data.String.ToNat.«0».noRepetition_append_cons_of_noRepetition_append_singleton 4 := by
  intro h; exact (priv% _private.Std.Data.String.ToNat.«0».noRepetition_iff).1 (@h Nat 0 [0] [] ((priv% _private.Std.Data.String.ToNat.«0».noRepetition_iff).2 (by decide))) (by decide)

-- `noRepetition_append_cons_of_noRepetition_append_singleton`: a = 0, l = [], m = [0].
theorem noRepetition_append_cons_of_noRepetition_append_singleton_5 :
    ¬ drop0% _private.Std.Data.String.ToNat.«0».noRepetition_append_cons_of_noRepetition_append_singleton 5 := by
  intro h; exact (priv% _private.Std.Data.String.ToNat.«0».noRepetition_iff).1 (@h Nat 0 [] [0] ((priv% _private.Std.Data.String.ToNat.«0».noRepetition_iff).2 (by decide))) (by decide)

end StrDecHand
