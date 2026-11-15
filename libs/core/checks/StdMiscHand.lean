import Std
import Lean

/-!
Hand pass `StdMisc` (hand14): the 28 unresolved hypotheses of `Std.Time`, `Std.Http` and `Std.Sync`.
27 necessary, 1 removable.

* `Nonempty α` of the `Nonempty (Mutex/RecursiveMutex/SharedMutex α)` instances: each holds an
  `IO.Ref α`, whose field `h : Nonempty α` makes `… Empty` empty.
* Structure `ext` lemmas: two values differing in exactly the dropped field (`t0`/`tH`/…, `a0`/`aY`/…,
  `d10`/`d00`/`d11`), refuted by `decide`.
* Removable: `c < '\x80'` of `not_quotedStringChar_of_not_qdtext_not_dquote_backslash`, implied by the
  sibling lemma `quotedStringChar_lt_0x80` for the other characters.

Run with the lean4 repo's stage1 binary: `runs/hand14/lean.sh checks/StdMiscHand.lean`.
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


open Std Std.Time

namespace StdMiscHand

/-! ## Std.Sync -/

-- `Std.instNonemptyMutex`: `Mutex Empty` holds an `IO.Ref Empty`, whose field `h : Nonempty Empty` is false.
theorem instNonemptyMutex_1 : ¬ drop0% Std.instNonemptyMutex 1 := by
  intro H; obtain ⟨m⟩ := @H Empty; cases m; rename_i r _; exact r.h.elim nofun

-- `Std.instNonemptyRecursiveMutex`: as for `Mutex`.
theorem instNonemptyRecursiveMutex_1 : ¬ drop0% Std.instNonemptyRecursiveMutex 1 := by
  intro H; obtain ⟨m⟩ := @H Empty; cases m; rename_i r _; exact r.h.elim nofun

-- `Std.instNonemptySharedMutex`: as for `Mutex`.
theorem instNonemptySharedMutex_1 : ¬ drop0% Std.instNonemptySharedMutex 1 := by
  intro H; obtain ⟨m⟩ := @H Empty; cases m; rename_i r _; exact r.h.elim nofun

/-! ## Std.Http -/

-- `Std.Http.Internal.Char.quotedStringChar_lt_0x80`: without the premise every char is `< '\x80'`; `'é'` isn't.
theorem quotedStringChar_lt_0x80_1 : ¬ drop0% Std.Http.Internal.Char.quotedStringChar_lt_0x80 1 :=
  fun H => absurd (H (c := 'é')) (by decide)

-- `Std.Http.Internal.Char.not_quotedStringChar_of_not_qdtext_not_dquote_backslash`: removable, for
-- `c ≥ '\x80'` the conclusion follows from the sibling lemma (a quoted-string char is `< '\x80'`).
theorem not_quotedStringChar_of_not_qdtext_not_dquote_backslash_1 :
    drop% Std.Http.Internal.Char.not_quotedStringChar_of_not_qdtext_not_dquote_backslash 1 := by
  intro c hq
  by_cases hlt : c < '\x80'
  · exact Std.Http.Internal.Char.not_quotedStringChar_of_not_qdtext_not_dquote_backslash c hlt hq
  · exact fun h => hlt (Std.Http.Internal.Char.quotedStringChar_lt_0x80 h)

-- `Std.Internal.MultiMap.findIdxFrom_lt_size`: on the empty multimap the claim is `_ < 0`.
theorem findIdxFrom_lt_size_6 : ¬ drop0% Std.Internal.MultiMap.findIdxFrom_lt_size 6 :=
  fun H => Nat.not_lt_zero _ (H (α := Nat) (β := Nat) ⟨#[]⟩ 0 0)

-- `Std.Internal.MultiMap.findIdxFrom_zero_lt_size`: on the empty multimap the claim is `_ < 0`.
theorem findIdxFrom_zero_lt_size_5 : ¬ drop0% Std.Internal.MultiMap.findIdxFrom_zero_lt_size 5 :=
  fun H => Nat.not_lt_zero _ (H (α := Nat) (β := Nat) (map := ⟨#[]⟩) (key := 0))

-- `Std.Http.URI.isValidUTF8_of_isAsciiByte`: the byte array `[0xFF]` is not valid UTF-8.
theorem isValidUTF8_of_isAsciiByte_1 : ¬ drop0% Std.Http.URI.isValidUTF8_of_isAsciiByte 1 :=
  fun H => absurd (H ⟨#[255]⟩) (by decide)

-- `Std.Http.URI.all_of_all_of_imp`: `p = q = false` on `[0]` satisfies `imp` but not the conclusion.
theorem all_of_all_of_imp_3 : ¬ drop0% Std.Http.URI.all_of_all_of_imp 3 :=
  fun H => absurd (H (b := ⟨#[0]⟩) (p := fun _ => false) (q := fun _ => false) (fun _ h => h)) (by simp)

-- `Std.Http.URI.all_of_all_of_imp`: `p = true`, `q = false` on `[0]` satisfies `h` but not the conclusion.
theorem all_of_all_of_imp_4 : ¬ drop0% Std.Http.URI.all_of_all_of_imp 4 :=
  fun H => absurd (H (b := ⟨#[0]⟩) (p := fun _ => true) (q := fun _ => false) (by simp)) (by simp)

-- `Std.Http.Header.Name.ext`: names `a` and `b` differ.
theorem Header_Name_ext_2 : ¬ drop0% Std.Http.Header.Name.ext 2 := fun H =>
  absurd (congrArg Std.Http.Header.Name.value (H (x := { value := "a" }) (y := { value := "b" })))
    (by decide)

/-! ## Std.Time -/

-- `Std.Time.Weekday.toOrdinal.inj`: Monday ≠ Tuesday.
theorem Weekday_toOrdinal_inj_2 : ¬ drop0% Std.Time.Weekday.toOrdinal.inj 2 :=
  fun H => absurd (H (a := .monday) (b := .tuesday)) (by decide)

-- `Std.Time.Month.Ordinal.difference_eq`: month 12 has `val = 12 > 11`.
theorem Month_Ordinal_difference_eq_2 : ¬ indep0% Std.Time.Month.Ordinal.difference_eq 2 :=
  fun H => absurd (H (leap := false) (month := 12)) (by decide)

-- `Std.Time.Internal.UnitVal.ext`: `0 ≠ 1`.
theorem UnitVal_ext_3 : ¬ drop0% Std.Time.Internal.UnitVal.ext 3 :=
  fun H => absurd (H (α := 1) (x := ⟨0⟩) (y := ⟨1⟩)) (by decide)

-- `Std.Time.TimeZone.Offset.ext`: offsets of 0 s and 1 s differ.
theorem Offset_ext_2 : ¬ drop0% Std.Time.TimeZone.Offset.ext 2 :=
  fun H => absurd (H (x := .ofSeconds 0) (y := .ofSeconds 1)) (by decide)

-- `Std.Time.WallTime.ext`: wall times 0 s and 1 s differ.
theorem WallTime_ext_2 : ¬ drop0% Std.Time.WallTime.ext 2 :=
  fun H => absurd (H (x := .ofSeconds 0) (y := .ofSeconds 1)) (by decide)

-- `Std.Time.Timestamp.ext`: timestamps 0 s and 1 s differ.
theorem Timestamp_ext_2 : ¬ drop0% Std.Time.Timestamp.ext 2 :=
  fun H => absurd (H (x := .ofSecondsSinceUnixEpoch 0) (y := .ofSecondsSinceUnixEpoch 1)) (by decide)

/-- Durations (1 s, 0 ns), (0 s, 0 ns), (1 s, 1 ns). -/
def d10 : Duration := ⟨1, ⟨0, by decide⟩, by decide⟩
def d00 : Duration := ⟨0, ⟨0, by decide⟩, by decide⟩
def d11 : Duration := ⟨1, ⟨1, by decide⟩, by decide⟩

-- `Std.Time.Duration.ext`: same nanoseconds, different seconds.
theorem Duration_ext_2 : ¬ drop0% Std.Time.Duration.ext 2 := fun H => by
  have := H (x := d10) (y := d00); revert this; decide

-- `Std.Time.Duration.ext`: same seconds, different nanoseconds.
theorem Duration_ext_3 : ¬ drop0% Std.Time.Duration.ext 3 := fun H => by
  have := H (x := d10) (y := d11); revert this; decide

/-- Times differing in exactly one component from `default` (00:00:00.0). -/
def t0 : PlainTime := default
def tH : PlainTime := { t0 with hour := 1 }
def tM : PlainTime := { t0 with minute := 1 }
def tS : PlainTime := { t0 with second := 1 }
def tN : PlainTime := { t0 with nanosecond := 1 }

-- `Std.Time.PlainTime.ext`: times differing only in the hour.
theorem PlainTime_ext_2 : ¬ drop0% Std.Time.PlainTime.ext 2 := fun H => by
  have := H (x := t0) (y := tH); revert this; decide

-- `Std.Time.PlainTime.ext`: times differing only in the minute.
theorem PlainTime_ext_3 : ¬ drop0% Std.Time.PlainTime.ext 3 := fun H => by
  have := H (x := t0) (y := tM); revert this; decide

-- `Std.Time.PlainTime.ext`: times differing only in the second.
theorem PlainTime_ext_4 : ¬ drop0% Std.Time.PlainTime.ext 4 := fun H => by
  have := H (x := t0) (y := tS); revert this; decide

-- `Std.Time.PlainTime.ext`: times differing only in the nanosecond.
theorem PlainTime_ext_5 : ¬ drop0% Std.Time.PlainTime.ext 5 := fun H => by
  have := H (x := t0) (y := tN); revert this; decide

/-- Dates 2000-01-01 and the three dates differing from it in one component. -/
def a0 : PlainDate := ⟨2000, 1, 1, by decide⟩
def aY : PlainDate := ⟨2001, 1, 1, by decide⟩
def aM : PlainDate := ⟨2000, 2, 1, by decide⟩
def aD : PlainDate := ⟨2000, 1, 2, by decide⟩

-- `Std.Time.PlainDate.ext`: dates differing only in the year.
theorem PlainDate_ext_2 : ¬ drop0% Std.Time.PlainDate.ext 2 := fun H => by
  have := H (x := a0) (y := aY); revert this; decide

-- `Std.Time.PlainDate.ext`: dates differing only in the month.
theorem PlainDate_ext_3 : ¬ drop0% Std.Time.PlainDate.ext 3 := fun H => by
  have := H (x := a0) (y := aM); revert this; decide

-- `Std.Time.PlainDate.ext`: dates differing only in the day.
theorem PlainDate_ext_4 : ¬ drop0% Std.Time.PlainDate.ext 4 := fun H => by
  have := H (x := a0) (y := aD); revert this; decide

-- `Std.Time.PlainDateTime.ext`: date-times differing only in the date.
theorem PlainDateTime_ext_2 : ¬ drop0% Std.Time.PlainDateTime.ext 2 := fun H => by
  have := H (x := ⟨a0, t0⟩) (y := ⟨aD, t0⟩); revert this; decide

-- `Std.Time.PlainDateTime.ext`: date-times differing only in the time.
theorem PlainDateTime_ext_3 : ¬ drop0% Std.Time.PlainDateTime.ext 3 := fun H => by
  have := H (x := ⟨a0, t0⟩) (y := ⟨a0, tH⟩); revert this; decide

end StdMiscHand
