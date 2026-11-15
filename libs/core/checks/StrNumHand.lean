import Std
import Lean

/-!
Hand pass `StrNum` (hand21, 2026-11-08): the 29 hypotheses of `Std.Data.String.ToNat` and
`Std.Data.String.ToInt` (numeral parsing of `String` and `String.Slice`) that the tool left open.
All 29 are necessary; each is refuted by a one- or two-character string.

`decide` gets stuck on the `forIn` loop of `isNat`, so the helpers in namespace `StrNumHand`
evaluate `isNat`/`toNat?`/`isInt`/`toInt?` on `""`, `"a"`, `"1"`, `"-1"`, `"_1"`, `"1_"` through the
library's `String.isNat_iff`, `toNat?_eq_some_ofDigitChars`, `isInt_iff` and `toInt?_minus_append`.
Slices are `"…".toSlice`, which agree with the string by `rfl` (`String.isNat_toSlice` etc.).

Run with the lean4 repo's stage1 binary: `runs/hand21/lean.sh checks/StrNumHand.lean`.
-/

set_option linter.unusedVariables false

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

open Lean Meta Elab Term in
/-- `drop0% T i`: `drop% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => Level.zero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

open Lean Meta Elab Term in
/-- `indep0% T i`: `indep% T i` with all universe parameters of `T` set to `0` (for refutations). -/
elab "indep0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
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

namespace StrNumHand

/-! ### Evaluations -/

theorem isNat_empty : ("" : String).isNat = false := by simp [← Bool.not_eq_true, String.isNat_iff]
theorem isNat_a : ("a" : String).isNat = false := by simp [← Bool.not_eq_true, String.isNat_iff]
theorem isNat_us1 : ("_1" : String).isNat = false := by simp [← Bool.not_eq_true, String.isNat_iff]
theorem isNat_1us : ("1_" : String).isNat = false := by simp [← Bool.not_eq_true, String.isNat_iff]
theorem isNat_m1 : ("-1" : String).isNat = false := by simp [← Bool.not_eq_true, String.isNat_iff]
theorem isNat_1 : ("1" : String).isNat = true := by simp [String.isNat_iff]; decide
theorem isNat_2 : ("2" : String).isNat = true := by simp [String.isNat_iff]; decide

theorem toNat_1 : ("1" : String).toNat? = some 1 := by
  rw [String.toNat?_eq_some_ofDigitChars isNat_1]; simp [Nat.ofDigitChars]
theorem toNat_a : ("a" : String).toNat? = none := String.toNat?_eq_none isNat_a
theorem toNat_empty : ("" : String).toNat? = none := String.toNat?_eq_none isNat_empty
theorem toNat_m1 : ("-1" : String).toNat? = none := String.toNat?_eq_none isNat_m1
theorem toNat_us1 : ("_1" : String).toNat? = none := String.toNat?_eq_none isNat_us1
theorem toNat_1us : ("1_" : String).toNat? = none := String.toNat?_eq_none isNat_1us

theorem isInt_a : ("a" : String).isInt = false := by
  simp only [← Bool.not_eq_true, String.isInt_iff, isNat_a, Bool.false_eq_true, false_or,
    not_exists, not_and]
  intro x h
  have := congrArg String.toList h
  simp at this
theorem isInt_empty : ("" : String).isInt = false := by
  simp only [← Bool.not_eq_true, String.isInt_iff, isNat_empty, Bool.false_eq_true, false_or,
    not_exists, not_and]
  intro x h
  have := congrArg String.toList h
  simp at this
theorem isInt_1 : ("1" : String).isInt = true := String.isInt_of_isNat isNat_1

theorem toInt_a : ("a" : String).toInt? = none := String.toInt?_eq_none isInt_a
theorem toInt_empty : ("" : String).toInt? = none := String.toInt?_eq_none isInt_empty
theorem toInt_1 : ("1" : String).toInt? = some 1 := String.toInt?_eq_some_of_toNat?_eq_some toNat_1
theorem toInt_m1 : ("-1" : String).toInt? = some (-1) := by
  rw [show ("-1" : String) = "-" ++ "1" from rfl, String.toInt?_minus_append, toNat_1]; rfl

theorem append_e_us_1 : ("" ++ "_" ++ "1" : String) = "_1" := rfl
theorem append_1_us_e : ("1" ++ "_" ++ "" : String) = "1_" := rfl
theorem append_e_us_e : ("" ++ "_" ++ "" : String) = "_" := rfl

/-! ### `String` (Std.Data.String.ToNat) -/

-- `String.toNat?_append_underscore_append_eq_some`: `s = ""`, `t = "1"`; `"_1"` is no numeral.
theorem toNat?_append_underscore_append_eq_some_4 :
    ¬ drop0% String.toNat?_append_underscore_append_eq_some 4 := by
  intro h
  have := h (s := "") (t := "1") (n := 0) (m := 1) toNat_1
  rw [append_e_us_1, toNat_us1] at this
  exact absurd this (by simp)

-- `String.toNat?_append_underscore_append_eq_some`: `s = "1"`, `t = ""`; `"1_"` is no numeral.
theorem toNat?_append_underscore_append_eq_some_5 :
    ¬ drop0% String.toNat?_append_underscore_append_eq_some 5 := by
  intro h
  have := h (s := "1") (t := "") (n := 1) (m := 0) toNat_1
  rw [append_1_us_e, toNat_1us] at this
  exact absurd this (by simp)

-- `String.isNat_of_isDigit`: `s = ""` (all characters are digits vacuously).
theorem isNat_of_isDigit_1 : ¬ drop0% String.isNat_of_isDigit 1 := by
  intro h
  have := h (s := "") (by simp)
  rw [isNat_empty] at this; exact absurd this (by simp)

-- `String.isNat_of_isDigit`: `s = "a"`.
theorem isNat_of_isDigit_2 : ¬ drop0% String.isNat_of_isDigit 2 := by
  intro h
  have := h (s := "a") (by decide)
  rw [isNat_a] at this; exact absurd this (by simp)

-- `String.isNat_of_toNat?_eq_some`: `s = "a"`.
theorem isNat_of_toNat?_eq_some_2 : ¬ drop0% String.isNat_of_toNat?_eq_some 2 := by
  intro h
  have := h (s := "a") (n := 0)
  rw [isNat_a] at this; exact absurd this (by simp)

-- `String.toNat?_eq_none`: `s = "1"`.
theorem toNat?_eq_none_1 : ¬ drop0% String.toNat?_eq_none 1 := by
  intro h
  have := h (s := "1")
  rw [toNat_1] at this; exact absurd this (by simp)

-- `String.toNat?_eq_some_ofDigitChars`: `s = "a"`.
theorem toNat?_eq_some_ofDigitChars_1 : ¬ drop0% String.toNat?_eq_some_ofDigitChars 1 := by
  intro h
  have := h (s := "a")
  rw [toNat_a] at this; exact absurd this (by simp)

-- `String.isNat_append_underscore_append`: `s = ""`, `t = "1"`.
theorem isNat_append_underscore_append_2 : ¬ drop0% String.isNat_append_underscore_append 2 := by
  intro h
  have := h (s := "") (t := "1") isNat_1
  rw [append_e_us_1, isNat_us1] at this; exact absurd this (by simp)

-- `String.isNat_append_underscore_append`: `s = "1"`, `t = ""`.
theorem isNat_append_underscore_append_3 : ¬ drop0% String.isNat_append_underscore_append 3 := by
  intro h
  have := h (s := "1") (t := "") isNat_1
  rw [append_1_us_e, isNat_1us] at this; exact absurd this (by simp)

/-! ### `String` (Std.Data.String.ToInt) -/

-- `String.isInt_of_toInt?_eq_some`: `s = "a"`.
theorem isInt_of_toInt?_eq_some_2 : ¬ drop0% String.isInt_of_toInt?_eq_some 2 := by
  intro h
  have := h (s := "a") (a := 0)
  rw [isInt_a] at this; exact absurd this (by simp)

-- `String.toInt?_eq_some_of_toNat?_eq_some`: `s = "a"`, `a = 0`.
theorem toInt?_eq_some_of_toNat?_eq_some_2 : ¬ drop0% String.toInt?_eq_some_of_toNat?_eq_some 2 := by
  intro h
  have := h (s := "a") (a := 0)
  rw [toInt_a] at this; exact absurd this (by simp)

-- `String.isInt_of_isNat`: `s = "a"`.
theorem isInt_of_isNat_1 : ¬ drop0% String.isInt_of_isNat 1 := by
  intro h
  have := h (s := "a")
  rw [isInt_a] at this; exact absurd this (by simp)

-- `String.toInt?_eq_none`: `s = "1"`.
theorem toInt?_eq_none_1 : ¬ drop0% String.toInt?_eq_none 1 := by
  intro h
  have := h (s := "1")
  rw [toInt_1] at this; exact absurd this (by simp)

-- `String.toInt?_eq_toNat?_of_startsWith_eq_false`: `s = "-1"` parses as an `Int` but not as a `Nat`.
theorem toInt?_eq_toNat?_of_startsWith_eq_false_1 :
    ¬ drop0% String.toInt?_eq_toNat?_of_startsWith_eq_false 1 := by
  intro h
  have := h (s := "-1")
  rw [toInt_m1, toNat_m1] at this; exact absurd this (by simp)

/-! ### `String.Slice` (both files); slices are `"…".toSlice` -/

-- `String.Slice.isNat_of_isDigit`: `s = "".toSlice`.
theorem Slice.isNat_of_isDigit_1 : ¬ drop0% String.Slice.isNat_of_isDigit 1 := by
  intro h
  have := h (s := "".toSlice) (by simp)
  rw [String.isNat_toSlice, isNat_empty] at this; exact absurd this (by simp)

-- `String.Slice.isNat_of_isDigit`: `s = "a".toSlice`.
theorem Slice.isNat_of_isDigit_2 : ¬ drop0% String.Slice.isNat_of_isDigit 2 := by
  intro h
  have := h (s := "a".toSlice) (by simp [← Bool.not_eq_true, ← String.Slice.isEmpty_copy])
  rw [String.isNat_toSlice, isNat_a] at this; exact absurd this (by simp)

-- `String.Slice.isNat_of_toNat?_eq_some`: `s = "a".toSlice`.
theorem Slice.isNat_of_toNat?_eq_some_2 : ¬ drop0% String.Slice.isNat_of_toNat?_eq_some 2 := by
  intro h
  have := h (s := "a".toSlice) (n := 0)
  rw [String.isNat_toSlice, isNat_a] at this; exact absurd this (by simp)

-- `String.Slice.toNat?_eq_none`: `s = "1".toSlice`.
theorem Slice.toNat?_eq_none_1 : ¬ drop0% String.Slice.toNat?_eq_none 1 := by
  intro h
  have := h (s := "1".toSlice)
  rw [String.toNat?_toSlice, toNat_1] at this; exact absurd this (by simp)

-- `String.Slice.toNat?_eq_some_ofDigitChars`: `s = "a".toSlice`.
theorem Slice.toNat?_eq_some_ofDigitChars_1 : ¬ drop0% String.Slice.toNat?_eq_some_ofDigitChars 1 := by
  intro h
  have := h (s := "a".toSlice)
  rw [String.toNat?_toSlice, toNat_a] at this; exact absurd this (by simp)

-- `String.Slice.isNat_congr`: `s = "1".toSlice`, `t = "a".toSlice`.
theorem Slice.isNat_congr_2 : ¬ drop0% String.Slice.isNat_congr 2 := by
  intro h
  have := h (s := "1".toSlice) (t := "a".toSlice)
  rw [String.isNat_toSlice, String.isNat_toSlice, isNat_1, isNat_a] at this; exact absurd this (by simp)

-- `String.Slice.toNat?_congr`: `s = "1".toSlice`, `t = "a".toSlice`.
theorem Slice.toNat?_congr_2 : ¬ drop0% String.Slice.toNat?_congr 2 := by
  intro h
  have := h (s := "1".toSlice) (t := "a".toSlice)
  rw [String.toNat?_toSlice, String.toNat?_toSlice, toNat_1, toNat_a] at this; exact absurd this (by simp)

-- `String.Slice.toInt?_eq_of_eq_minus_append`: `s = "".toSlice`, `t = "1"`.
theorem Slice.toInt?_eq_of_eq_minus_append_2 : ¬ drop0% String.Slice.toInt?_eq_of_eq_minus_append 2 := by
  intro h
  have := h (s := "".toSlice) (t := "1")
  rw [String.toInt?_toSlice, toInt_empty, toNat_1] at this; exact absurd this (by simp)

-- `String.Slice.isInt_of_toInt?_eq_some`: `s = "a".toSlice`.
theorem Slice.isInt_of_toInt?_eq_some_2 : ¬ drop0% String.Slice.isInt_of_toInt?_eq_some 2 := by
  intro h
  have := h (s := "a".toSlice) (a := 0)
  rw [String.isInt_toSlice, isInt_a] at this; exact absurd this (by simp)

-- `String.Slice.toInt?_eq_none`: `s = "1".toSlice`.
theorem Slice.toInt?_eq_none_1 : ¬ drop0% String.Slice.toInt?_eq_none 1 := by
  intro h
  have := h (s := "1".toSlice)
  rw [String.toInt?_toSlice, toInt_1] at this; exact absurd this (by simp)

-- `String.Slice.isInt_of_isNat`: `s = "a".toSlice`.
theorem Slice.isInt_of_isNat_1 : ¬ drop0% String.Slice.isInt_of_isNat 1 := by
  intro h
  have := h (s := "a".toSlice)
  rw [String.isInt_toSlice, isInt_a] at this; exact absurd this (by simp)

-- `String.Slice.toInt?_eq_some_of_toNat?_eq_some`: `s = "a".toSlice`, `a = 0`.
theorem Slice.toInt?_eq_some_of_toNat?_eq_some_2 :
    ¬ drop0% String.Slice.toInt?_eq_some_of_toNat?_eq_some 2 := by
  intro h
  have := h (s := "a".toSlice) (a := 0)
  rw [String.toInt?_toSlice, toInt_a] at this; exact absurd this (by simp)

-- `String.Slice.toInt?_eq_toNat?_of_startsWith_eq_false`: `s = "-1".toSlice`.
theorem Slice.toInt?_eq_toNat?_of_startsWith_eq_false_1 :
    ¬ drop0% String.Slice.toInt?_eq_toNat?_of_startsWith_eq_false 1 := by
  intro h
  have := h (s := "-1".toSlice)
  rw [String.toInt?_toSlice, String.toNat?_toSlice, toInt_m1, toNat_m1] at this
  exact absurd this (by simp)

-- `String.Slice.toInt?_congr`: `s = "1".toSlice`, `t = "a".toSlice`.
theorem Slice.toInt?_congr_2 : ¬ drop0% String.Slice.toInt?_congr 2 := by
  intro h
  have := h (s := "1".toSlice) (t := "a".toSlice)
  rw [String.toInt?_toSlice, String.toInt?_toSlice, toInt_1, toInt_a] at this; exact absurd this (by simp)

-- `String.Slice.isInt_congr`: `s = "1".toSlice`, `t = "a".toSlice`.
theorem Slice.isInt_congr_2 : ¬ drop0% String.Slice.isInt_congr 2 := by
  intro h
  have := h (s := "1".toSlice) (t := "a".toSlice)
  rw [String.isInt_toSlice, String.isInt_toSlice, isInt_1, isInt_a] at this; exact absurd this (by simp)

end StrNumHand
