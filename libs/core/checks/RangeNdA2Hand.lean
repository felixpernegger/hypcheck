import Lean

/-!
Hand pass `RangeNdA2` (hand8): the 152 non-dependent hypotheses of the `Std.Roo.*`, `Std.Ric.*` and
`Std.Rio.*` lemmas in `Init.Data.Range.Polymorphic.Lemmas` that the tool left open. For hypothesis
`hᵢ` of theorem `T` each declaration proves `¬T'` (`drop0% T i`, universes `0`; necessary) or `T'`
(`drop% T i`, universe parameters kept; removable).

100 necessary, 52 removable, 0 independent, 0 opaque, 0 left unresolved.

Necessary: a model satisfies every other hypothesis (instance search finds them) and the conclusion
is evaluated to something false; range `toList`s are evaluated by unfolding the iterator
(`range_eval`), which needs only `LawfulUpwardEnumerable` + finiteness of the model.
* `LawfulUpwardEnumerableLT/LE` (`NLT2`/`NLE2`: Nat whose `<`/`≤` misses `(1, 3)` and `(0, 5)`, so
  ranges stop early or skip members), `LawfulUpwardEnumerableLeast?` (`NLeast`, least = 1),
  `LinearlyUpwardEnumerable` (`NMerge`: `succ 0 = succ 3 = 4`), `LawfulUpwardEnumerable` (`NBack`:
  `succMany? 1 1 = some 0`; `M0` for `Ric.isEmpty`), `Rxc/Rxo.LawfulHasSize` (`NSz`, size 0),
  `LawfulUpwardEnumerableLE` in `Ric.isEmpty_iff_forall_not_mem` (`UF`, one point with empty `≤`).
* `LawfulMonad` (17): `CM` (bind only counts, ignores the continuation): the range loop wraps `f` in
  one more bind than the list/array loop or the unfolded right-hand side (`cm_unfold`).
* `forIn'_congr` `hi`/`h`, `mem_of_mem_of_le` `hmem`: Nat; `isSome_succMany?_*` `h`: `U0`.

Removable (52):
* `pairwise_toList_upwardEnumerableLt`, `nodup_toList`, `pairwise_toList_ne`, `pairwise_toList_lt/le`
  without the `LE`/`LT`/`Least?` law not occurring in the conclusion, and
  `isSome_succMany?_of_lt_length_toList`/`_size_toArray` without `…LE/LT`: the list of a range
  iterator is a chain of successors of its start, whatever the bound check is (`rxc_chain`,
  `rxo_chain`, `rxc_isSome`, `rxo_isSome`).
* `Ric/Rio.length_toList`, `size_toArray` without `…LE/LT`: `LawfulHasSize` states the iterator's own
  recursion (`rxc_length`, `rxo_length`).
* `Ric/Rio.toList/toArray_succ_eq_map` without `LinearlyUpwardEnumerable`: it follows from
  `LawfulUpwardEnumerable`, `LawfulUpwardEnumerableLeast?` and `InfinitelyUpwardEnumerable`
  (`lin_of_least`: everything lies on the repetition-free successor chain of `least`).
* `Ric.toList_eq_match_rcc`, `…_toList_rcc`, `…_ite_roc`, … and the `Rio` analogues, and
  `Rio.toList/toArray_eq_nil_iff`, without `…LE/LT`: both sides are (the first step of) the same
  iterator; `Rio.forIn'_eq_forIn'_rco` without `LawfulMonad`: both sides run the same iterator loop
  with the same body up to proofs (`loop_congr`).

Run with the lean4 repo's stage1 binary: `lean checks/RangeNdA2Hand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open Lean Meta Elab Term in
def RangeNdA2Drop.dropType (T : Ident) (i : Nat) (zero : Bool) : TermElabM Expr := do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← if zero then pure (ci.levelParams.map fun _ => levelZero)
    else ci.levelParams.mapM fun _ => mkFreshLevelMVar
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i]!
    unless ← isProp (← inferType x) do throwError "binder {i} of {n} is not a Prop"
    for j in [i+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i) body

/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => RangeNdA2Drop.dropType T i.getNat false
/-- `drop0% T i`: like `drop% T i` with all universes set to `0` (for refutations). -/
elab "drop0% " T:ident i:num : term => RangeNdA2Drop.dropType T i.getNat true

open Std Std.PRange

namespace RangeNdA2Hand

/-! ## Model table

Each model is its own type, so instance search fills the theorems' other instance arguments.
✓ = instance, ✗ = `¬` lemma, - = no instance (not needed).

| model    | carrier | `LUE` | `LE` | `LT` | `Least?` | `Inf` | `Lin` | `RxcF` | `RxoF` | `Rxc.LHS` | `Rxo.LHS` |
|----------|---------|-------|------|------|----------|-------|-------|--------|--------|-----------|-----------|
| `NLT2`   | Nat     | ✓     | ✓    | ✗    | ✓        | ✓     | ✓     | ✓      | ✓      | -         | ✓         |
| `NLE2`   | Nat     | ✓     | ✗    | ✓    | ✓        | ✓     | ✓     | ✓      | ✓      | -         | -         |
| `NLeast` | Nat     | ✓     | ✓    | ✓    | ✗        | ✓     | ✓     | ✓      | ✓      | -         | -         |
| `NMerge` | Nat     | ✓     | ✓    | ✓    | -        | ✓     | ✗     | ✓      | ✓      | -         | -         |
| `NBack`  | Nat     | ✗     | ✓    | ✓    | ✓        | ✓     | ✓     | ✓      | ✓      | -         | ✓         |
| `NSz`    | Nat     | ✓     | ✓    | ✓    | ✓        | ✓     | ✓     | ✓      | ✓      | ✗         | ✗         |
| `M0`     | 1 point | ✗     | ✓    | -    | -        | -     | -     | ✓      | -      | ✓         | -         |
| `U0`     | 1 point | ✓     | ✓    | ✓    | ✓        | -     | -     | ✓      | ✓      | -         | -         |
| `UF`     | 1 point | ✓     | ✗    | -    | -        | -     | -     | ✓      | -      | ✓         | -         |

(`LUE` = `LawfulUpwardEnumerable`, `LE`/`LT`/`Least?` = `LawfulUpwardEnumerableLE/LT/Least?`,
`Inf`/`Lin` = `Infinitely/LinearlyUpwardEnumerable`, `RxcF`/`RxoF` = `Rxc/Rxo.IsAlwaysFinite`,
`LHS` = `LawfulHasSize`.) The Nat models have explicit `UpwardEnumerable`/`Least?` instances (so
`simp` unfolds `succ?`), `DecidableEq`, and points `M.pt n`. `NMerge`'s ranges are evaluated with
`Roo.toList_eq_match` instead of `range_eval` (the `if` in its `succ?` blocks `simp`).
-/

/-! ## Models -/

/-- `NLT2`: Nat whose `<` misses the pairs `(1, 3)` and `(0, 5)`; everything else is Nat's. -/
def NLT2 := Nat
def NLT2.pt (n : Nat) : NLT2 := n
instance : DecidableEq NLT2 := inferInstanceAs (DecidableEq Nat)
abbrev NLT2.lt (a b : Nat) : Prop := a < b ∧ ¬(a = 1 ∧ b = 3) ∧ ¬(a = 0 ∧ b = 5)
instance : UpwardEnumerable NLT2 :=
  { succ? := fun (n : Nat) => some (n + 1), succMany? := fun k (n : Nat) => some (n + k) }
instance : LE NLT2 := inferInstanceAs (LE Nat)
instance : DecidableLE NLT2 := inferInstanceAs (DecidableLE Nat)
instance : LT NLT2 := ⟨fun (a b : Nat) => NLT2.lt a b⟩
instance : DecidableLT NLT2 := fun (a b : Nat) => inferInstanceAs (Decidable (NLT2.lt a b))
instance : Least? NLT2 := ⟨some (NLT2.pt 0)⟩
instance : LawfulUpwardEnumerable NLT2 := inferInstanceAs (LawfulUpwardEnumerable Nat)
instance : LawfulUpwardEnumerableLE NLT2 := inferInstanceAs (LawfulUpwardEnumerableLE Nat)
instance : LawfulUpwardEnumerableLeast? NLT2 := inferInstanceAs (LawfulUpwardEnumerableLeast? Nat)
instance : InfinitelyUpwardEnumerable NLT2 := inferInstanceAs (InfinitelyUpwardEnumerable Nat)
instance : LinearlyUpwardEnumerable NLT2 := inferInstanceAs (LinearlyUpwardEnumerable Nat)
instance : Rxc.IsAlwaysFinite NLT2 := inferInstanceAs (Rxc.IsAlwaysFinite Nat)
instance : Rxo.IsAlwaysFinite NLT2 :=
  ⟨fun (i hi : Nat) => ⟨hi, show ¬ NLT2.lt (i + hi) hi by unfold NLT2.lt; omega⟩⟩
def NLT2.sz (lo hi : Nat) : Nat := if h : NLT2.lt lo hi then NLT2.sz (lo + 1) hi + 1 else 0
termination_by hi + 1 - lo
decreasing_by omega
instance : Rxo.HasSize NLT2 := ⟨fun (a b : Nat) => NLT2.sz a b⟩
instance : Rxo.LawfulHasSize NLT2 where
  size_eq_zero_of_not_le lo hi h := by
    exact (NLT2.sz.eq_1 lo hi).trans (dif_neg h)
  size_eq_one_of_succ?_eq_none lo hi h h' := nomatch h'
  size_eq_succ_of_succ?_eq_some lo hi lo' h h' := by
    cases h'; exact (NLT2.sz.eq_1 lo hi).trans (dif_pos h)
theorem NLT2.not_LLT : ¬ LawfulUpwardEnumerableLT NLT2 := fun h => by
  have := (h.lt_iff (1 : Nat) (3 : Nat)).2 ⟨1, rfl⟩
  exact this.2.1 ⟨rfl, rfl⟩

/-- `NLE2`: Nat whose `≤` misses the pairs `(1, 3)` and `(0, 5)`; everything else is Nat's. -/
def NLE2 := Nat
def NLE2.pt (n : Nat) : NLE2 := n
instance : DecidableEq NLE2 := inferInstanceAs (DecidableEq Nat)
abbrev NLE2.le (a b : Nat) : Prop := a ≤ b ∧ ¬(a = 1 ∧ b = 3) ∧ ¬(a = 0 ∧ b = 5)
instance : UpwardEnumerable NLE2 :=
  { succ? := fun (n : Nat) => some (n + 1), succMany? := fun k (n : Nat) => some (n + k) }
instance : LE NLE2 := ⟨fun (a b : Nat) => NLE2.le a b⟩
instance : DecidableLE NLE2 := fun (a b : Nat) => inferInstanceAs (Decidable (NLE2.le a b))
instance : LT NLE2 := inferInstanceAs (LT Nat)
instance : DecidableLT NLE2 := inferInstanceAs (DecidableLT Nat)
instance : Least? NLE2 := ⟨some (NLE2.pt 0)⟩
instance : LawfulUpwardEnumerable NLE2 := inferInstanceAs (LawfulUpwardEnumerable Nat)
instance : LawfulUpwardEnumerableLT NLE2 := inferInstanceAs (LawfulUpwardEnumerableLT Nat)
instance : LawfulUpwardEnumerableLeast? NLE2 := inferInstanceAs (LawfulUpwardEnumerableLeast? Nat)
instance : InfinitelyUpwardEnumerable NLE2 := inferInstanceAs (InfinitelyUpwardEnumerable Nat)
instance : LinearlyUpwardEnumerable NLE2 := inferInstanceAs (LinearlyUpwardEnumerable Nat)
instance : Rxo.IsAlwaysFinite NLE2 := inferInstanceAs (Rxo.IsAlwaysFinite Nat)
instance : Rxc.IsAlwaysFinite NLE2 :=
  ⟨fun (i hi : Nat) => ⟨hi + 1, show ¬ NLE2.le (i + (hi + 1)) hi by unfold NLE2.le; omega⟩⟩
theorem NLE2.not_LLE : ¬ LawfulUpwardEnumerableLE NLE2 := fun h => by
  have := (h.le_iff (1 : Nat) (3 : Nat)).2 ⟨2, rfl⟩
  exact this.2.1 ⟨rfl, rfl⟩

/-- `NLeast`: Nat with `least? = some 1`; everything else is Nat's. -/
def NLeast := Nat
def NLeast.pt (n : Nat) : NLeast := n
instance : DecidableEq NLeast := inferInstanceAs (DecidableEq Nat)
instance : UpwardEnumerable NLeast :=
  { succ? := fun (n : Nat) => some (n + 1), succMany? := fun k (n : Nat) => some (n + k) }
instance : LE NLeast := inferInstanceAs (LE Nat)
instance : DecidableLE NLeast := inferInstanceAs (DecidableLE Nat)
instance : LT NLeast := inferInstanceAs (LT Nat)
instance : DecidableLT NLeast := inferInstanceAs (DecidableLT Nat)
instance : Least? NLeast := ⟨some (NLeast.pt 1)⟩
instance : LawfulUpwardEnumerable NLeast := inferInstanceAs (LawfulUpwardEnumerable Nat)
instance : LawfulUpwardEnumerableLE NLeast := inferInstanceAs (LawfulUpwardEnumerableLE Nat)
instance : LawfulUpwardEnumerableLT NLeast := inferInstanceAs (LawfulUpwardEnumerableLT Nat)
instance : InfinitelyUpwardEnumerable NLeast := inferInstanceAs (InfinitelyUpwardEnumerable Nat)
instance : LinearlyUpwardEnumerable NLeast := inferInstanceAs (LinearlyUpwardEnumerable Nat)
instance : Rxc.IsAlwaysFinite NLeast := inferInstanceAs (Rxc.IsAlwaysFinite Nat)
instance : Rxo.IsAlwaysFinite NLeast := inferInstanceAs (Rxo.IsAlwaysFinite Nat)
theorem NLeast.not_LLeast : ¬ LawfulUpwardEnumerableLeast? NLeast := fun h => by
  obtain ⟨_, h1, n, hn⟩ := h.least?_le (0 : Nat)
  cases h1; change some (1 + n) = some 0 at hn; simp at hn

/-- `NMerge`: Nat where `0` and `3` both have successor `4` (`0 → 4 → 5 → …`, `1 → 2 → 3 → 4 → …`);
`≤`/`<` are `UpwardEnumerable.LE/LT`. Lawful and finite, but not `LinearlyUpwardEnumerable`. -/
def NMerge := Nat
def NMerge.pt (n : Nat) : NMerge := n
instance : DecidableEq NMerge := inferInstanceAs (DecidableEq Nat)
abbrev NMerge.lt (a b : Nat) : Prop := if a = 0 then 4 ≤ b else a < b
abbrev NMerge.le (a b : Nat) : Prop := if a = 0 then b = 0 ∨ 4 ≤ b else a ≤ b
instance : UpwardEnumerable NMerge :=
  { succ? := fun (n : Nat) => some ((if n = 0 then 4 else n + 1 : Nat)),
    succMany? := fun k (n : Nat) => some ((if n = 0 ∧ k ≠ 0 then k + 3 else n + k : Nat)) }
instance : LE NMerge := ⟨fun (a b : Nat) => NMerge.le a b⟩
instance : DecidableLE NMerge := fun (a b : Nat) => inferInstanceAs (Decidable (NMerge.le a b))
instance : LT NMerge := ⟨fun (a b : Nat) => NMerge.lt a b⟩
instance : DecidableLT NMerge := fun (a b : Nat) => inferInstanceAs (Decidable (NMerge.lt a b))
instance : LawfulUpwardEnumerable NMerge where
  ne_of_lt (a b : Nat) := fun ⟨n, h⟩ => by
    show @Ne Nat a b
    change some (if a = 0 ∧ n + 1 ≠ 0 then n + 1 + 3 else a + (n + 1)) = some b at h
    simp only [Option.some.injEq] at h; split at h <;> omega
  succMany?_zero (a : Nat) := by change some (if a = 0 ∧ 0 ≠ 0 then 0 + 3 else a + 0) = some a; simp
  succMany?_add_one n (a : Nat) := by
    change some (if a = 0 ∧ n + 1 ≠ 0 then n + 1 + 3 else a + (n + 1)) =
      some (if (if a = 0 ∧ n ≠ 0 then n + 3 else a + n) = 0 then 4 else (if a = 0 ∧ n ≠ 0 then n + 3 else a + n) + 1)
    simp only [Option.some.injEq]; split <;> split <;> split <;> omega
instance : LawfulUpwardEnumerableLT NMerge where
  lt_iff (a b : Nat) := by
    change NMerge.lt a b ↔ ∃ n, some (if a = 0 ∧ n + 1 ≠ 0 then n + 1 + 3 else a + (n + 1)) = some b
    unfold NMerge.lt; simp only [Option.some.injEq]
    constructor
    · intro h; split at h
      · exact ⟨b - 4, by split <;> omega⟩
      · exact ⟨b - a - 1, by split <;> omega⟩
    · rintro ⟨n, hn⟩; split <;> split at hn <;> omega
instance : LawfulUpwardEnumerableLE NMerge where
  le_iff (a b : Nat) := by
    change NMerge.le a b ↔ ∃ n, some (if a = 0 ∧ n ≠ 0 then n + 3 else a + n) = some b
    unfold NMerge.le; simp only [Option.some.injEq]
    constructor
    · intro h; split at h
      · rcases h with h | h
        · exact ⟨0, by split <;> omega⟩
        · exact ⟨b - 3, by split <;> omega⟩
      · exact ⟨b - a, by split <;> omega⟩
    · rintro ⟨n, hn⟩; split <;> split at hn <;> omega
instance : InfinitelyUpwardEnumerable NMerge := ⟨fun _ => rfl⟩
instance : Rxo.IsAlwaysFinite NMerge :=
  ⟨fun (i hi : Nat) => ⟨hi + 5, show ¬ NMerge.lt (if i = 0 ∧ hi + 5 ≠ 0 then hi + 5 + 3 else i + (hi + 5)) hi by
    unfold NMerge.lt; split <;> split <;> omega⟩⟩
instance : Rxc.IsAlwaysFinite NMerge :=
  ⟨fun (i hi : Nat) => ⟨hi + 5, show ¬ NMerge.le (if i = 0 ∧ hi + 5 ≠ 0 then hi + 5 + 3 else i + (hi + 5)) hi by
    unfold NMerge.le; split <;> split <;> omega⟩⟩
theorem NMerge.not_Lin : ¬ LinearlyUpwardEnumerable NMerge := fun h =>
  absurd (show (0 : Nat) = 3 from h.eq_of_succ?_eq (0 : Nat) (3 : Nat) rfl) (by decide)

/-- `NBack`: Nat with `succ? n = n + 1`, but `succMany? 1 1 = some 0` (otherwise `n + k`);
`≤`/`<` are `UpwardEnumerable.LE/LT`, `least? = some 0`. Everything but `LawfulUpwardEnumerable`. -/
def NBack := Nat
def NBack.pt (n : Nat) : NBack := n
instance : DecidableEq NBack := inferInstanceAs (DecidableEq Nat)
abbrev NBack.lt (a b : Nat) : Prop := if a = 1 then b = 0 ∨ 3 ≤ b else a < b
abbrev NBack.le (a b : Nat) : Prop := if a = 1 then b = 0 ∨ b = 1 ∨ 3 ≤ b else a ≤ b
instance : UpwardEnumerable NBack :=
  { succ? := fun (n : Nat) => some (n + 1),
    succMany? := fun k (n : Nat) => some ((if n = 1 ∧ k = 1 then 0 else n + k : Nat)) }
instance : LE NBack := ⟨fun (a b : Nat) => NBack.le a b⟩
instance : DecidableLE NBack := fun (a b : Nat) => inferInstanceAs (Decidable (NBack.le a b))
instance : LT NBack := ⟨fun (a b : Nat) => NBack.lt a b⟩
instance : DecidableLT NBack := fun (a b : Nat) => inferInstanceAs (Decidable (NBack.lt a b))
instance : Least? NBack := ⟨some (NBack.pt 0)⟩
instance : LawfulUpwardEnumerableLT NBack where
  lt_iff (a b : Nat) := by
    change NBack.lt a b ↔ ∃ n, some (if a = 1 ∧ n + 1 = 1 then 0 else a + (n + 1)) = some b
    unfold NBack.lt; simp only [Option.some.injEq]
    constructor
    · intro h; split at h
      · rcases h with h | h
        · exact ⟨0, by split <;> omega⟩
        · exact ⟨b - 2, by split <;> omega⟩
      · exact ⟨b - a - 1, by split <;> omega⟩
    · rintro ⟨n, hn⟩; split <;> split at hn <;> omega
instance : LawfulUpwardEnumerableLE NBack where
  le_iff (a b : Nat) := by
    change NBack.le a b ↔ ∃ n, some (if a = 1 ∧ n = 1 then 0 else a + n) = some b
    unfold NBack.le; simp only [Option.some.injEq]
    constructor
    · intro h; split at h
      · rcases h with h | h | h
        · exact ⟨1, by split <;> omega⟩
        · exact ⟨0, by split <;> omega⟩
        · exact ⟨b - 1, by split <;> omega⟩
      · exact ⟨b - a, by split <;> omega⟩
    · rintro ⟨n, hn⟩; split <;> split at hn <;> omega
instance : LawfulUpwardEnumerableLeast? NBack :=
  ⟨fun (a : Nat) => ⟨(0 : Nat), rfl, a, show some (if 0 = 1 ∧ a = 1 then 0 else 0 + a) = some a by simp⟩⟩
instance : InfinitelyUpwardEnumerable NBack := ⟨fun _ => rfl⟩
instance : LinearlyUpwardEnumerable NBack :=
  ⟨fun (a b : Nat) (h : some (a + 1) = some (b + 1)) => Nat.succ.inj (Option.some.inj h)⟩
instance : Rxo.IsAlwaysFinite NBack :=
  ⟨fun (i hi : Nat) => ⟨hi + 3, show ¬ NBack.lt (if i = 1 ∧ hi + 3 = 1 then 0 else i + (hi + 3)) hi by
    unfold NBack.lt; split <;> split <;> omega⟩⟩
instance : Rxc.IsAlwaysFinite NBack :=
  ⟨fun (i hi : Nat) => ⟨hi + 3, show ¬ NBack.le (if i = 1 ∧ hi + 3 = 1 then 0 else i + (hi + 3)) hi by
    unfold NBack.le; split <;> split <;> omega⟩⟩
def NBack.sz (lo hi : Nat) : Nat := if h : NBack.lt lo hi then NBack.sz (lo + 1) hi + 1 else 0
termination_by hi + 3 - lo
decreasing_by split at h <;> omega
instance : Rxo.HasSize NBack := ⟨fun (a b : Nat) => NBack.sz a b⟩
instance : Rxo.LawfulHasSize NBack where
  size_eq_zero_of_not_le lo hi h := by
    exact (NBack.sz.eq_1 lo hi).trans (dif_neg h)
  size_eq_one_of_succ?_eq_none lo hi h h' := nomatch h'
  size_eq_succ_of_succ?_eq_some lo hi lo' h h' := by
    cases h'; exact (NBack.sz.eq_1 lo hi).trans (dif_pos h)
theorem NBack.not_LUE : ¬ LawfulUpwardEnumerable NBack := fun h => by
  have := h.succMany?_add_one 0 (1 : Nat)
  change some (0 : Nat) = some (2 : Nat) at this; simp at this

/-- `NSz`: Nat with `Rxc/Rxo.HasSize` constantly `0`; everything else is Nat's. -/
def NSz := Nat
def NSz.pt (n : Nat) : NSz := n
instance : DecidableEq NSz := inferInstanceAs (DecidableEq Nat)
instance : UpwardEnumerable NSz :=
  { succ? := fun (n : Nat) => some (n + 1), succMany? := fun k (n : Nat) => some (n + k) }
instance : LE NSz := inferInstanceAs (LE Nat)
instance : DecidableLE NSz := inferInstanceAs (DecidableLE Nat)
instance : LT NSz := inferInstanceAs (LT Nat)
instance : DecidableLT NSz := inferInstanceAs (DecidableLT Nat)
instance : Least? NSz := ⟨some (NSz.pt 0)⟩
instance : Rxc.HasSize NSz := ⟨fun _ _ => 0⟩
instance : Rxo.HasSize NSz := ⟨fun _ _ => 0⟩
instance : LawfulUpwardEnumerable NSz := inferInstanceAs (LawfulUpwardEnumerable Nat)
instance : LawfulUpwardEnumerableLE NSz := inferInstanceAs (LawfulUpwardEnumerableLE Nat)
instance : LawfulUpwardEnumerableLT NSz := inferInstanceAs (LawfulUpwardEnumerableLT Nat)
instance : LawfulUpwardEnumerableLeast? NSz := inferInstanceAs (LawfulUpwardEnumerableLeast? Nat)
instance : InfinitelyUpwardEnumerable NSz := inferInstanceAs (InfinitelyUpwardEnumerable Nat)
instance : LinearlyUpwardEnumerable NSz := inferInstanceAs (LinearlyUpwardEnumerable Nat)
instance : Rxc.IsAlwaysFinite NSz := inferInstanceAs (Rxc.IsAlwaysFinite Nat)
instance : Rxo.IsAlwaysFinite NSz := inferInstanceAs (Rxo.IsAlwaysFinite Nat)
theorem NSz.not_RxcLHS : ¬ Rxc.LawfulHasSize NSz := fun h =>
  absurd (h.size_eq_succ_of_succ?_eq_some (0 : Nat) (0 : Nat) (1 : Nat) (Nat.le_refl 0) rfl) (by decide)
theorem NSz.not_RxoLHS : ¬ Rxo.LawfulHasSize NSz := fun h =>
  absurd (h.size_eq_succ_of_succ?_eq_some (0 : Nat) (1 : Nat) (1 : Nat) (Nat.lt_succ_self 0) rfl) (by decide)

/-- `M0`: one point, `succMany?` constantly `none` (so `succMany? 0 a ≠ some a`); `≤`, `<` empty. -/
inductive M0 | pt deriving DecidableEq
instance : UpwardEnumerable M0 := { succ? := fun a => some a, succMany? := fun _ _ => none }
instance : LE M0 := ⟨fun _ _ => False⟩
instance : LT M0 := ⟨fun _ _ => False⟩
instance : DecidableLE M0 := fun _ _ => isFalse id
instance : DecidableLT M0 := fun _ _ => isFalse id
instance : Rxc.HasSize M0 := ⟨fun _ _ => 0⟩
instance : LawfulUpwardEnumerableLE M0 := ⟨fun _ _ => ⟨False.elim, fun ⟨_, h⟩ => nomatch h⟩⟩
instance : Rxc.IsAlwaysFinite M0 := ⟨fun _ _ => ⟨0, trivial⟩⟩
instance : Rxc.LawfulHasSize M0 := ⟨fun _ _ _ => rfl, fun _ _ h => h.elim, fun _ _ _ h => h.elim⟩
theorem M0.not_LUE : ¬ LawfulUpwardEnumerable M0 := fun h => nomatch h.succMany?_zero .pt

/-- `U0`: one point without successor; `≤` true, `<` empty, `least? = some pt`. -/
inductive U0 | pt deriving DecidableEq
instance : UpwardEnumerable U0 :=
  { succ? := fun _ => none, succMany? := fun n a => if n = 0 then some a else none }
instance : LE U0 := ⟨fun _ _ => True⟩
instance : LT U0 := ⟨fun _ _ => False⟩
instance : DecidableLE U0 := fun _ _ => isTrue trivial
instance : DecidableLT U0 := fun _ _ => isFalse id
instance : Least? U0 := ⟨some .pt⟩
instance : LawfulUpwardEnumerable U0 where
  ne_of_lt _ _ := fun ⟨_, h⟩ => nomatch h
  succMany?_zero _ := rfl
  succMany?_add_one n a := by cases n <;> rfl
instance : LawfulUpwardEnumerableLE U0 := ⟨fun .pt .pt => ⟨fun _ => ⟨0, rfl⟩, fun _ => trivial⟩⟩
instance : LawfulUpwardEnumerableLT U0 := ⟨fun _ _ => ⟨False.elim, fun ⟨_, h⟩ => nomatch h⟩⟩
instance : LawfulUpwardEnumerableLeast? U0 := ⟨fun .pt => ⟨.pt, rfl, 0, rfl⟩⟩
instance : Rxc.IsAlwaysFinite U0 := ⟨fun _ _ => ⟨1, trivial⟩⟩
instance : Rxo.IsAlwaysFinite U0 := ⟨fun _ _ => ⟨0, id⟩⟩

/-- `UF`: one point without successor and with `≤` empty: lawful except `LawfulUpwardEnumerableLE`. -/
inductive UF | pt deriving DecidableEq
instance : UpwardEnumerable UF :=
  { succ? := fun _ => none, succMany? := fun n a => if n = 0 then some a else none }
instance : LE UF := ⟨fun _ _ => False⟩
instance : Rxc.HasSize UF := ⟨fun _ _ => 0⟩
instance : LawfulUpwardEnumerable UF where
  ne_of_lt _ _ := fun ⟨_, h⟩ => nomatch h
  succMany?_zero _ := rfl
  succMany?_add_one n a := by cases n <;> rfl
instance : Rxc.IsAlwaysFinite UF := ⟨fun _ _ => ⟨0, id⟩⟩
instance : Rxc.LawfulHasSize UF := ⟨fun _ _ _ => rfl, fun _ _ h => h.elim, fun _ _ _ h => h.elim⟩
theorem UF.not_LLE : ¬ LawfulUpwardEnumerableLE UF := fun h => (h.le_iff .pt .pt).2 ⟨0, rfl⟩

macro "range_eval" : tactic => `(tactic| (
  repeat (rw [Iter.toList_eq_match_step]; simp +decide only [Rxc.Iterator.step_eq_step, Rxc.Iterator.step, Rxo.Iterator.step_eq_step, Rxo.Iterator.step, UpwardEnumerable.succ?, Least?.least?, ↓reduceIte])
  all_goals rfl))


/-- `CM`: a monad that only counts `bind`s and ignores continuations (not lawful). -/
def CM (_ : Type) : Type := Nat
instance : Monad CM where
  pure _ := (0 : Nat)
  bind x _ := Nat.succ (x : Nat)
theorem CM.not_lawful : ¬ LawfulMonad CM := fun h => by
  have := h.pure_bind (x := ()) (f := fun _ => (pure () : CM Unit))
  exact absurd (show (1 : Nat) = 0 from this) (by decide)

macro "cm_unfold" : tactic => `(tactic| (
  simp only [ForIn'.forIn', Iter.instForIn', IteratorLoop.finiteForIn', IteratorLoop.forIn,
    Rxc.Iterator.instIteratorLoop, Rxc.Iterator.instIteratorLoop.loop,
    Rxo.Iterator.instIteratorLoop, Rxo.Iterator.instIteratorLoop.loop,
    Roo.Internal.iter, Ric.Internal.iter, Rio.Internal.iter, Iter.toIterM, UpwardEnumerable.succ?,
    Least?.least?, Nat.reduceAdd]
  rw [WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ IteratorLoop.wellFounded_of_finite)]))

/-! ## Evaluated ranges (`range_eval` unfolds the iterator; needs only lawful + finite models) -/

theorem NLT2.roo03 : (Roo.mk (NLT2.pt 0) (NLT2.pt 3)).toList = [] := by
  simp only [Roo.toList, Roo.Internal.iter]; range_eval
theorem NLT2.roo04 : (Roo.mk (NLT2.pt 0) (NLT2.pt 4)).toList = [NLT2.pt 1, NLT2.pt 2, NLT2.pt 3] := by
  simp only [Roo.toList, Roo.Internal.iter]; range_eval
theorem NLT2.roo14 : (Roo.mk (NLT2.pt 1) (NLT2.pt 4)).toList = [NLT2.pt 2, NLT2.pt 3] := by
  simp only [Roo.toList, Roo.Internal.iter]; range_eval
theorem NLT2.rio2 : (Rio.mk (NLT2.pt 2)).toList = [NLT2.pt 0, NLT2.pt 1] := by
  simp only [Rio.toList, Rio.Internal.iter]; range_eval
theorem NLT2.rio3 : (Rio.mk (NLT2.pt 3)).toList = [NLT2.pt 0] := by
  simp only [Rio.toList, Rio.Internal.iter]; range_eval
theorem NLT2.ric4 : (Ric.mk (NLT2.pt 4)).toList = [NLT2.pt 0, NLT2.pt 1, NLT2.pt 2, NLT2.pt 3, NLT2.pt 4] := by
  simp only [Ric.toList, Ric.Internal.iter]; range_eval
theorem NLE2.ric2 : (Ric.mk (NLE2.pt 2)).toList = [NLE2.pt 0, NLE2.pt 1, NLE2.pt 2] := by
  simp only [Ric.toList, Ric.Internal.iter]; range_eval
theorem NLE2.ric3 : (Ric.mk (NLE2.pt 3)).toList = [NLE2.pt 0] := by
  simp only [Ric.toList, Ric.Internal.iter]; range_eval
theorem NLE2.ric4 : (Ric.mk (NLE2.pt 4)).toList = [NLE2.pt 0, NLE2.pt 1, NLE2.pt 2, NLE2.pt 3, NLE2.pt 4] := by
  simp only [Ric.toList, Ric.Internal.iter]; range_eval
theorem NLE2.ric5 : (Ric.mk (NLE2.pt 5)).toList = [] := by
  simp only [Ric.toList, Ric.Internal.iter]; range_eval
theorem NLE2.roo04 : (Roo.mk (NLE2.pt 0) (NLE2.pt 4)).toList = [NLE2.pt 1, NLE2.pt 2, NLE2.pt 3] := by
  simp only [Roo.toList, Roo.Internal.iter]; range_eval
theorem NLE2.rio4 : (Rio.mk (NLE2.pt 4)).toList = [NLE2.pt 0, NLE2.pt 1, NLE2.pt 2, NLE2.pt 3] := by
  simp only [Rio.toList, Rio.Internal.iter]; range_eval
theorem NLeast.ric0 : (Ric.mk (NLeast.pt 0)).toList = [] := by
  simp only [Ric.toList, Ric.Internal.iter]; range_eval
theorem NLeast.ric1 : (Ric.mk (NLeast.pt 1)).toList = [NLeast.pt 1] := by
  simp only [Ric.toList, Ric.Internal.iter]; range_eval
theorem NLeast.rio2 : (Rio.mk (NLeast.pt 2)).toList = [NLeast.pt 1] := by
  simp only [Rio.toList, Rio.Internal.iter]; range_eval
theorem NSz.ric0 : (Ric.mk (NSz.pt 0)).toList = [NSz.pt 0] := by
  simp only [Ric.toList, Ric.Internal.iter]; range_eval
theorem NSz.roo02 : (Roo.mk (NSz.pt 0) (NSz.pt 2)).toList = [NSz.pt 1] := by
  simp only [Roo.toList, Roo.Internal.iter]; range_eval
theorem NSz.rio1 : (Rio.mk (NSz.pt 1)).toList = [NSz.pt 0] := by
  simp only [Rio.toList, Rio.Internal.iter]; range_eval
theorem Nat.roo00 : (Roo.mk (0 : Nat) 0).toList = [] := by
  simp only [Roo.toList, Roo.Internal.iter]; range_eval
theorem Nat.roo02 : (Roo.mk (0 : Nat) 2).toList = [1] := by
  simp only [Roo.toList, Roo.Internal.iter]; range_eval
theorem Nat.ric0 : (Ric.mk (0 : Nat)).toList = [0] := by
  simp only [Ric.toList, Ric.Internal.iter]; range_eval
theorem Nat.rio1 : (Rio.mk (1 : Nat)).toList = [0] := by
  simp only [Rio.toList, Rio.Internal.iter]; range_eval
theorem NMerge.roo24 : (Roo.mk (NMerge.pt 2) (NMerge.pt 4)).toList = [NMerge.pt 3] := by
  rw [Roo.toList_eq_match, show UpwardEnumerable.succ? (NMerge.pt 2) = some (NMerge.pt 3) from rfl]
  dsimp only; rw [if_pos (by decide), Roo.toList_eq_match, show UpwardEnumerable.succ? (NMerge.pt 3) = some (NMerge.pt 4) from rfl]
  dsimp only; rw [if_neg (by decide)]
theorem NMerge.roo10 : (Roo.mk (NMerge.pt 1) (NMerge.pt 0)).toList = [] := by
  rw [Roo.toList_eq_match, show UpwardEnumerable.succ? (NMerge.pt 1) = some (NMerge.pt 2) from rfl]
  dsimp only; rw [if_neg (by decide)]


/-! ## Helper lemmas for the removable verdicts

The range iterators enumerate a chain of successors and stop at the first element that fails the
bound check. That they produce a `UpwardEnumerable.LT`-chain, that the `i`-th element is the `i`-th
successor of the first one, and that `LawfulHasSize` computes their length only needs
`LawfulUpwardEnumerable` and finiteness, not `LawfulUpwardEnumerableLE/LT/Least?`. -/

section Helpers
variable {α : Type u}

theorem rxc_toList_eq_match [LE α] [DecidableLE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] {it : Iter (α := Rxc.Iterator α) α} :
    it.toList = match it.internalState.next with
      | none => []
      | some a => if a ≤ it.internalState.upperBound then
          a :: (⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ : Iter (α := Rxc.Iterator α) α).toList
        else [] := by
  apply Eq.symm
  rw [Iter.toList_eq_match_step, Rxc.Iterator.step_eq_step]
  simp only [Rxc.Iterator.step]
  split <;> rename_i heq
  · simp [*]
  · split <;> rename_i heq' <;> simp [*]

theorem rxo_toList_eq_match [LT α] [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxo.IsAlwaysFinite α] {it : Iter (α := Rxo.Iterator α) α} :
    it.toList = match it.internalState.next with
      | none => []
      | some a => if a < it.internalState.upperBound then
          a :: (⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ : Iter (α := Rxo.Iterator α) α).toList
        else [] := by
  apply Eq.symm
  simp only [Iter.toList_eq_match_step (it := it), Rxo.Iterator.step_eq_step, Rxo.Iterator.step]
  split <;> rename_i heq
  · simp [*]
  · split <;> rename_i heq' <;> simp [*]

/-- Elements of a `Rxc` iterator's list: successors of its start, pairwise `UpwardEnumerable.LT`. -/
theorem rxc_chain [LE α] [DecidableLE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] (it : Iter (α := Rxc.Iterator α) α) :
    (∀ b ∈ it.toList, ∃ a, it.internalState.next = some a ∧ UpwardEnumerable.LE a b) ∧
      it.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [rxc_toList_eq_match]
  split
  · simp
  · rename_i a ha
    split
    · rename_i hle
      have ih := ihy (out := a) (it' := ⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩)
        (by simp_all [Rxc.Iterator.isPlausibleStep_iff, Rxc.Iterator.step])
      have key : ∀ b ∈ (⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ :
          Iter (α := Rxc.Iterator α) α).toList, UpwardEnumerable.LT a b := by
        intro b hb
        obtain ⟨a', ha', hle'⟩ := ih.1 b hb
        exact UpwardEnumerable.lt_of_lt_of_le (UpwardEnumerable.lt_succ? ha') hle'
      refine ⟨?_, List.Pairwise.cons key ih.2⟩
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨_, ha, UpwardEnumerable.le_refl _⟩
      · exact ⟨a, ha, UpwardEnumerable.le_of_lt (key b hb)⟩
    · simp

theorem rxo_chain [LT α] [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxo.IsAlwaysFinite α] (it : Iter (α := Rxo.Iterator α) α) :
    (∀ b ∈ it.toList, ∃ a, it.internalState.next = some a ∧ UpwardEnumerable.LE a b) ∧
      it.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [rxo_toList_eq_match]
  split
  · simp
  · rename_i a ha
    split
    · rename_i hle
      have ih := ihy (out := a) (it' := ⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩)
        (by simp_all [Rxo.Iterator.isPlausibleStep_iff, Rxo.Iterator.step])
      have key : ∀ b ∈ (⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ :
          Iter (α := Rxo.Iterator α) α).toList, UpwardEnumerable.LT a b := by
        intro b hb
        obtain ⟨a', ha', hle'⟩ := ih.1 b hb
        exact UpwardEnumerable.lt_of_lt_of_le (UpwardEnumerable.lt_succ? ha') hle'
      refine ⟨?_, List.Pairwise.cons key ih.2⟩
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨_, ha, UpwardEnumerable.le_refl _⟩
      · exact ⟨a, ha, UpwardEnumerable.le_of_lt (key b hb)⟩
    · simp

/-- The `i`-th element of a `Rxc` iterator's list exists only if the `i`-th successor does. -/
theorem rxc_isSome [LE α] [DecidableLE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] (it : Iter (α := Rxc.Iterator α) α) :
    ∀ i, i < it.toList.length → ∃ a, it.internalState.next = some a ∧
      (UpwardEnumerable.succMany? i a).isSome := by
  induction it using Iter.inductSteps with | step it ihy ihs
  intro i hi
  rw [rxc_toList_eq_match] at hi
  split at hi
  · simp at hi
  · rename_i a ha
    split at hi
    · refine ⟨a, ha, ?_⟩
      match i with
      | 0 => simp [UpwardEnumerable.succMany?_zero]
      | j + 1 =>
        have ih := ihy (out := a) (it' := ⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩)
          (by simp_all [Rxc.Iterator.isPlausibleStep_iff, Rxc.Iterator.step]) j (by simpa using hi)
        obtain ⟨a', ha', hs⟩ := ih
        simp only at ha'
        rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, ha', Option.bind_some]
        exact hs
    · simp at hi

theorem rxo_isSome [LT α] [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxo.IsAlwaysFinite α] (it : Iter (α := Rxo.Iterator α) α) :
    ∀ i, i < it.toList.length → ∃ a, it.internalState.next = some a ∧
      (UpwardEnumerable.succMany? i a).isSome := by
  induction it using Iter.inductSteps with | step it ihy ihs
  intro i hi
  rw [rxo_toList_eq_match] at hi
  split at hi
  · simp at hi
  · rename_i a ha
    split at hi
    · refine ⟨a, ha, ?_⟩
      match i with
      | 0 => simp [UpwardEnumerable.succMany?_zero]
      | j + 1 =>
        have ih := ihy (out := a) (it' := ⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩)
          (by simp_all [Rxo.Iterator.isPlausibleStep_iff, Rxo.Iterator.step]) j (by simpa using hi)
        obtain ⟨a', ha', hs⟩ := ih
        simp only at ha'
        rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, ha', Option.bind_some]
        exact hs
    · simp at hi

/-- `LawfulHasSize` computes the length of a `Rxc` iterator's list. -/
theorem rxc_length [LE α] [DecidableLE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] [Rxc.HasSize α] [Rxc.LawfulHasSize α] (it : Iter (α := Rxc.Iterator α) α) :
    it.toList.length = match it.internalState.next with
      | none => 0
      | some a => Rxc.HasSize.size a it.internalState.upperBound := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [rxc_toList_eq_match]
  split
  · rfl
  · rename_i a ha
    split
    · rename_i hle
      have ih := ihy (out := a) (it' := ⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩)
        (by simp_all [Rxc.Iterator.isPlausibleStep_iff, Rxc.Iterator.step])
      rw [List.length_cons, ih]
      simp only
      cases hs : UpwardEnumerable.succ? a with
      | none => rw [Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ hle hs]
      | some a' => rw [Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ hle hs]
    · rename_i hle
      rw [Rxc.LawfulHasSize.size_eq_zero_of_not_le _ _ hle]; rfl

theorem rxo_length [LT α] [DecidableLT α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxo.IsAlwaysFinite α] [Rxo.HasSize α] [Rxo.LawfulHasSize α] (it : Iter (α := Rxo.Iterator α) α) :
    it.toList.length = match it.internalState.next with
      | none => 0
      | some a => Rxo.HasSize.size a it.internalState.upperBound := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [rxo_toList_eq_match]
  split
  · rfl
  · rename_i a ha
    split
    · rename_i hle
      have ih := ihy (out := a) (it' := ⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩)
        (by simp_all [Rxo.Iterator.isPlausibleStep_iff, Rxo.Iterator.step])
      rw [List.length_cons, ih]
      simp only
      cases hs : UpwardEnumerable.succ? a with
      | none => rw [Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ hle hs]
      | some a' => rw [Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ hle hs]
    · rename_i hle
      rw [Rxo.LawfulHasSize.size_eq_zero_of_not_le _ _ hle]; rfl

/-- `LinearlyUpwardEnumerable` follows from `LawfulUpwardEnumerable`, `LawfulUpwardEnumerableLeast?`
and `InfinitelyUpwardEnumerable`: everything lies on the successor chain of `least`, which has no
repetitions. -/
theorem lin_of_least [UpwardEnumerable α] [LawfulUpwardEnumerable α] [Least? α]
    [LawfulUpwardEnumerableLeast? α] [InfinitelyUpwardEnumerable α] : LinearlyUpwardEnumerable α := by
  have key : ∀ (a b : α) (k : Nat), UpwardEnumerable.succMany? k a = some b →
      UpwardEnumerable.succ? a = UpwardEnumerable.succ? b → a = b := by
    intro a b k hk hs
    match k with
    | 0 => rw [UpwardEnumerable.succMany?_zero] at hk; exact Option.some.inj hk
    | j + 1 =>
      exfalso
      obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.1 (UpwardEnumerable.isSome_succ? (a := a))
      have h1 : UpwardEnumerable.succMany? (j + 1) s = some s := by
        have e1 : UpwardEnumerable.succMany? (j + 1 + 1) a = UpwardEnumerable.succ? b := by
          rw [UpwardEnumerable.succMany?_add_one, hk, Option.bind_some]
        rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs', Option.bind_some] at e1
        rw [e1, ← hs, hs']
      exact UpwardEnumerable.lt_irrefl ⟨j, h1⟩
  refine ⟨fun a b h => ?_⟩
  obtain ⟨i, hi, n, hn⟩ := UpwardEnumerable.least?_le (a := a)
  obtain ⟨i', hi', m, hm⟩ := UpwardEnumerable.least?_le (a := b)
  rw [hi] at hi'; cases hi'
  rcases Nat.le_total n m with hnm | hnm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [UpwardEnumerable.succMany?_add, hn, Option.bind_some] at hm
    exact key a b k hm h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [UpwardEnumerable.succMany?_add, hm, Option.bind_some] at hn
    exact (key b a k hn h.symm).symm

end Helpers

/-! ## Removable: unfolding lemmas of `Ric`/`Rio` that never use the order law -/

theorem loop_congr {α β : Type w} {n : Type x → Type x'} [Iterator α Id β] [IteratorLoop α Id n]
    {lift : (γ : Type w) → (δ : Type x) → (γ → n δ) → Id γ → n δ} {γ : Type x}
    {Pl : β → γ → ForInStep γ → Prop} {it it' : IterM (α := α) Id β} (e : it = it') {init : γ}
    {F : (b : β) → it.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))}
    {F' : (b : β) → it'.IsPlausibleIndirectOutput b → (c : γ) → n (Subtype (Pl b c))}
    (hF : ∀ b h h' c, F b h c = F' b h' c) :
    IteratorLoop.forIn lift γ Pl it init F = IteratorLoop.forIn lift γ Pl it' init F' := by
  subst e; congr 1; funext b h c; exact hF b h h c

theorem ric_toList_ite {α : Type u} [LE α] [DecidableLE α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] [Rxc.IsAlwaysFinite α] (r : Ric α) :
    r.toList = (let init : α := UpwardEnumerable.least (hn := ⟨r.upper⟩)
      if init ≤ r.upper then init :: (init<...=r.upper).toList else []) := by
  simp only [Ric.toList, Ric.Internal.iter, Roc.toList, Roc.Internal.iter,
    @UpwardEnumerable.least?_eq_some _ _ _ _ ⟨r.upper⟩]
  rw [rxc_toList_eq_match]

theorem rio_toList_ite {α : Type u} [LT α] [DecidableLT α] [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α] [Rxo.IsAlwaysFinite α] (r : Rio α) :
    r.toList = (let init : α := UpwardEnumerable.least (hn := ⟨r.upper⟩)
      if init < r.upper then init :: (init<...r.upper).toList else []) := by
  simp only [Rio.toList, Rio.Internal.iter, Roo.toList, Roo.Internal.iter,
    @UpwardEnumerable.least?_eq_some _ _ _ _ ⟨r.upper⟩]
  rw [rxo_toList_eq_match]

-- `Std.Ric.toList_eq_match_rcc` (hypothesis 7): removable, both sides are the toList of the same iterator from least? (LawfulUpwardEnumerableLE is not used).
theorem Ric.toList_eq_match_rcc.h7 : drop% Std.Ric.toList_eq_match_rcc 7 := by
  intro α r _ _ _ _ _ _
  simp only [Ric.toList, Ric.Internal.iter, Rcc.toList, Rcc.Internal.iter]
  cases h : (Least?.least? : Option α)
  · rw [rxc_toList_eq_match]
  · rfl

-- `Std.Ric.toList_eq_toList_rcc` (hypothesis 7): removable, both sides are the toList of the same iterator, since least? = some least.
theorem Ric.toList_eq_toList_rcc.h7 : drop% Std.Ric.toList_eq_toList_rcc 7 := by
  intro α r _ _ _ _ _ _ _
  simp only [Ric.toList, Ric.Internal.iter, Rcc.toList, Rcc.Internal.iter,
    @UpwardEnumerable.least?_eq_some _ _ _ _ ⟨r.upper⟩]

-- `Std.Ric.toArray_eq_toArray_rcc` (hypothesis 7): removable, both sides are the toArray of the same iterator, since least? = some least.
theorem Ric.toArray_eq_toArray_rcc.h7 : drop% Std.Ric.toArray_eq_toArray_rcc 7 := by
  intro α r _ _ _ _ _ _ _
  simp only [Ric.toArray, Ric.Internal.iter, Rcc.toArray, Rcc.Internal.iter,
    @UpwardEnumerable.least?_eq_some _ _ _ _ ⟨r.upper⟩]

-- `Std.Ric.toList_eq_ite_roc` (hypothesis 7): removable, it is the first step of the iterator from least (ric_toList_ite).
theorem Ric.toList_eq_ite_roc.h7 : drop% Std.Ric.toList_eq_ite_roc 7 := by
  intros; exact ric_toList_ite _

-- `Std.Ric.toList_eq_if_roc` (hypothesis 7): removable, it is the first step of the iterator from least (ric_toList_ite).
theorem Ric.toList_eq_if_roc.h7 : drop% Std.Ric.toList_eq_if_roc 7 := by
  intros; exact ric_toList_ite _

-- `Std.Ric.toArray_eq_ite_roc` (hypothesis 7): removable, it is the first step of the iterator from least (ric_toList_ite).
theorem Ric.toArray_eq_ite_roc.h7 : drop% Std.Ric.toArray_eq_ite_roc 7 := by
  intro α r _ _ _ _ _ _ _
  rw [← Ric.toArray_toList, ric_toList_ite]; dsimp only; split <;> simp [Roc.toArray_toList]

-- `Std.Ric.toArray_eq_if_roc` (hypothesis 7): removable, it is the first step of the iterator from least (ric_toList_ite).
theorem Ric.toArray_eq_if_roc.h7 : drop% Std.Ric.toArray_eq_if_roc 7 := by
  intro α r _ _ _ _ _ _ _
  rw [← Ric.toArray_toList, ric_toList_ite]; dsimp only; split <;> simp [Roc.toArray_toList]

-- `Std.Rio.toList_eq_match_rco` (hypothesis 7): removable, both sides are the toList of the same iterator from least? (LawfulUpwardEnumerableLT is not used).
theorem Rio.toList_eq_match_rco.h7 : drop% Std.Rio.toList_eq_match_rco 7 := by
  intro α r _ _ _ _ _ _
  simp only [Rio.toList, Rio.Internal.iter, Rco.toList, Rco.Internal.iter]
  cases h : (Least?.least? : Option α)
  · rw [rxo_toList_eq_match]
  · rfl

-- `Std.Rio.toArray_eq_match_rco` (hypothesis 7): removable, both sides are the toArray of the same iterator from least?.
theorem Rio.toArray_eq_match_rco.h7 : drop% Std.Rio.toArray_eq_match_rco 7 := by
  intro α r _ _ _ _ _ _
  simp only [Rio.toArray, Rio.Internal.iter, Rco.toArray, Rco.Internal.iter]
  cases h : (Least?.least? : Option α)
  · rw [← Iter.toArray_toList, rxo_toList_eq_match]
  · rfl

-- `Std.Rio.toList_eq_toList_rco` (hypothesis 7): removable, both sides are the toList of the same iterator, since least? = some least.
theorem Rio.toList_eq_toList_rco.h7 : drop% Std.Rio.toList_eq_toList_rco 7 := by
  intro α r _ _ _ _ _ _ _
  simp only [Rio.toList, Rio.Internal.iter, Rco.toList, Rco.Internal.iter,
    @UpwardEnumerable.least?_eq_some _ _ _ _ ⟨r.upper⟩]

-- `Std.Rio.toArray_eq_toArray_rco` (hypothesis 7): removable, both sides are the toArray of the same iterator, since least? = some least.
theorem Rio.toArray_eq_toArray_rco.h7 : drop% Std.Rio.toArray_eq_toArray_rco 7 := by
  intro α r _ _ _ _ _ _ _
  simp only [Rio.toArray, Rio.Internal.iter, Rco.toArray, Rco.Internal.iter,
    @UpwardEnumerable.least?_eq_some _ _ _ _ ⟨r.upper⟩]

-- `Std.Rio.toList_eq_ite_roo` (hypothesis 7): removable, it is the first step of the iterator from least (rio_toList_ite).
theorem Rio.toList_eq_ite_roo.h7 : drop% Std.Rio.toList_eq_ite_roo 7 := by
  intros; exact rio_toList_ite _

-- `Std.Rio.toList_eq_if_roo` (hypothesis 7): removable, it is the first step of the iterator from least (rio_toList_ite).
theorem Rio.toList_eq_if_roo.h7 : drop% Std.Rio.toList_eq_if_roo 7 := by
  intros; exact rio_toList_ite _

-- `Std.Rio.toArray_eq_ite_roo` (hypothesis 7): removable, it is the first step of the iterator from least (rio_toList_ite).
theorem Rio.toArray_eq_ite_roo.h7 : drop% Std.Rio.toArray_eq_ite_roo 7 := by
  intro α r _ _ _ _ _ _ _
  rw [← Rio.toArray_toList, rio_toList_ite]; dsimp only; split <;> simp [Roo.toArray_toList]

-- `Std.Rio.toArray_eq_if_roo` (hypothesis 7): removable, it is the first step of the iterator from least (rio_toList_ite).
theorem Rio.toArray_eq_if_roo.h7 : drop% Std.Rio.toArray_eq_if_roo 7 := by
  intro α r _ _ _ _ _ _ _
  rw [← Rio.toArray_toList, rio_toList_ite]; dsimp only; split <;> simp [Roo.toArray_toList]

-- `Std.Rio.toList_eq_nil_iff` (hypothesis 7): removable, the list starts with least iff least < upper (rio_toList_ite).
theorem Rio.toList_eq_nil_iff.h7 : drop% Std.Rio.toList_eq_nil_iff 7 := by
  intro α r _ _ _ _ _ _ _
  rw [rio_toList_ite]; dsimp only; split <;> simp_all

-- `Std.Rio.toArray_eq_nil_iff` (hypothesis 7): removable, the array starts with least iff least < upper (rio_toList_ite).
theorem Rio.toArray_eq_nil_iff.h7 : drop% Std.Rio.toArray_eq_nil_iff 7 := by
  intro α r _ _ _ _ _ _ _
  rw [← Rio.toArray_toList, rio_toList_ite]; dsimp only; split <;> simp_all

-- `Std.Rio.forIn'_eq_forIn'_rco` (hypothesis 14): removable, both sides run the same iterator loop (least? = some least) with the same body up to proofs (loop_congr), in any monad.
theorem Rio.forIn'_eq_forIn'_rco.h14 : drop% Std.Rio.forIn'_eq_forIn'_rco 14 := by
  intro α r _ _ _ _ _ _ _ _ _ _ m _ γ init f
  dsimp only [ForIn'.forIn']
  apply loop_congr
  · simp only [Rio.Internal.iter, Rco.Internal.iter, Iter.toIterM, @UpwardEnumerable.least?_eq_some _ _ _ _ ⟨r.upper⟩]
  · intros; rfl

/-! ## Removable: chain properties of the iterators (`rxc_chain`, `rxo_chain`) -/

-- `Std.Roo.pairwise_toList_upwardEnumerableLt` (hypothesis 6): removable, the list is a successor chain (rxo_chain), which needs only LawfulUpwardEnumerable and finiteness.
theorem Roo.pairwise_toList_upwardEnumerableLt.h6 : drop% Std.Roo.pairwise_toList_upwardEnumerableLt 6 := by
  intros; exact (rxo_chain _).2

-- `Std.Roo.nodup_toList` (hypothesis 6): removable, the list is pairwise UpwardEnumerable.LT (rxo_chain), hence pairwise distinct by ne_of_lt.
theorem Roo.nodup_toList.h6 : drop% Std.Roo.nodup_toList 6 := by
  intros; exact (rxo_chain _).2.imp UpwardEnumerable.ne_of_lt

-- `Std.Roo.pairwise_toList_ne` (hypothesis 6): removable, the list is pairwise UpwardEnumerable.LT (rxo_chain), hence pairwise distinct by ne_of_lt.
theorem Roo.pairwise_toList_ne.h6 : drop% Std.Roo.pairwise_toList_ne 6 := by
  intros; exact (rxo_chain _).2.imp UpwardEnumerable.ne_of_lt

-- `Std.Roo.pairwise_toList_le` (hypothesis 7): removable, the list is pairwise UpwardEnumerable.LT (rxo_chain), and LawfulUpwardEnumerableLE turns that into ≤.
theorem Roo.pairwise_toList_le.h7 : drop% Std.Roo.pairwise_toList_le 7 := by
  intros; exact (rxo_chain _).2.imp fun h => UpwardEnumerable.le_iff.2 (UpwardEnumerable.le_of_lt h)

-- `Std.Ric.pairwise_toList_upwardEnumerableLt` (hypothesis 7): removable, the list is a successor chain (rxc_chain), which needs only LawfulUpwardEnumerable and finiteness.
theorem Ric.pairwise_toList_upwardEnumerableLt.h7 : drop% Std.Ric.pairwise_toList_upwardEnumerableLt 7 := by
  intros; exact (rxc_chain _).2

-- `Std.Ric.pairwise_toList_upwardEnumerableLt` (hypothesis 8): removable, the list is a successor chain from least? (rxc_chain), whatever least? is.
theorem Ric.pairwise_toList_upwardEnumerableLt.h8 : drop% Std.Ric.pairwise_toList_upwardEnumerableLt 8 := by
  intros; exact (rxc_chain _).2

-- `Std.Ric.nodup_toList` (hypothesis 7): removable, the list is pairwise UpwardEnumerable.LT (rxc_chain), hence pairwise distinct.
theorem Ric.nodup_toList.h7 : drop% Std.Ric.nodup_toList 7 := by
  intros; exact (rxc_chain _).2.imp UpwardEnumerable.ne_of_lt

-- `Std.Ric.pairwise_toList_ne` (hypothesis 7): removable, the list is pairwise UpwardEnumerable.LT (rxc_chain), hence pairwise distinct.
theorem Ric.pairwise_toList_ne.h7 : drop% Std.Ric.pairwise_toList_ne 7 := by
  intros; exact (rxc_chain _).2.imp UpwardEnumerable.ne_of_lt

-- `Std.Ric.pairwise_toList_ne` (hypothesis 8): removable, the list is pairwise UpwardEnumerable.LT (rxc_chain), hence pairwise distinct.
theorem Ric.pairwise_toList_ne.h8 : drop% Std.Ric.pairwise_toList_ne 8 := by
  intros; exact (rxc_chain _).2.imp UpwardEnumerable.ne_of_lt

-- `Std.Ric.pairwise_toList_lt` (hypothesis 8): removable, the list is pairwise UpwardEnumerable.LT (rxc_chain), and LawfulUpwardEnumerableLT turns that into <.
theorem Ric.pairwise_toList_lt.h8 : drop% Std.Ric.pairwise_toList_lt 8 := by
  intros; exact (rxc_chain _).2.imp fun h => UpwardEnumerable.lt_iff.2 h

-- `Std.Ric.pairwise_toList_lt` (hypothesis 11): removable, the list is pairwise UpwardEnumerable.LT (rxc_chain), and LawfulUpwardEnumerableLT turns that into <.
theorem Ric.pairwise_toList_lt.h11 : drop% Std.Ric.pairwise_toList_lt 11 := by
  intros; exact (rxc_chain _).2.imp fun h => UpwardEnumerable.lt_iff.2 h

-- `Std.Ric.pairwise_toList_le` (hypothesis 9): removable, the list is pairwise UpwardEnumerable.LT (rxc_chain), and LawfulUpwardEnumerableLE turns that into ≤.
theorem Ric.pairwise_toList_le.h9 : drop% Std.Ric.pairwise_toList_le 9 := by
  intros; exact (rxc_chain _).2.imp fun h => UpwardEnumerable.le_iff.2 (UpwardEnumerable.le_of_lt h)

-- `Std.Rio.pairwise_toList_upwardEnumerableLt` (hypothesis 7): removable, the list is a successor chain (rxo_chain), which needs only LawfulUpwardEnumerable and finiteness.
theorem Rio.pairwise_toList_upwardEnumerableLt.h7 : drop% Std.Rio.pairwise_toList_upwardEnumerableLt 7 := by
  intros; exact (rxo_chain _).2

-- `Std.Rio.pairwise_toList_upwardEnumerableLt` (hypothesis 8): removable, the list is a successor chain from least? (rxo_chain), whatever least? is.
theorem Rio.pairwise_toList_upwardEnumerableLt.h8 : drop% Std.Rio.pairwise_toList_upwardEnumerableLt 8 := by
  intros; exact (rxo_chain _).2

-- `Std.Rio.nodup_toList` (hypothesis 7): removable, the list is pairwise UpwardEnumerable.LT (rxo_chain), hence pairwise distinct.
theorem Rio.nodup_toList.h7 : drop% Std.Rio.nodup_toList 7 := by
  intros; exact (rxo_chain _).2.imp UpwardEnumerable.ne_of_lt

-- `Std.Rio.pairwise_toList_ne` (hypothesis 7): removable, the list is pairwise UpwardEnumerable.LT (rxo_chain), hence pairwise distinct.
theorem Rio.pairwise_toList_ne.h7 : drop% Std.Rio.pairwise_toList_ne 7 := by
  intros; exact (rxo_chain _).2.imp UpwardEnumerable.ne_of_lt

-- `Std.Rio.pairwise_toList_ne` (hypothesis 8): removable, the list is pairwise UpwardEnumerable.LT (rxo_chain), hence pairwise distinct.
theorem Rio.pairwise_toList_ne.h8 : drop% Std.Rio.pairwise_toList_ne 8 := by
  intros; exact (rxo_chain _).2.imp UpwardEnumerable.ne_of_lt

-- `Std.Rio.pairwise_toList_lt` (hypothesis 10): removable, the list is pairwise UpwardEnumerable.LT (rxo_chain), and LawfulUpwardEnumerableLT turns that into <.
theorem Rio.pairwise_toList_lt.h10 : drop% Std.Rio.pairwise_toList_lt 10 := by
  intros; exact (rxo_chain _).2.imp fun h => UpwardEnumerable.lt_iff.2 h

-- `Std.Rio.pairwise_toList_le` (hypothesis 8): removable, the list is pairwise UpwardEnumerable.LT (rxo_chain), and LawfulUpwardEnumerableLE turns that into ≤.
theorem Rio.pairwise_toList_le.h8 : drop% Std.Rio.pairwise_toList_le 8 := by
  intros; exact (rxo_chain _).2.imp fun h => UpwardEnumerable.le_iff.2 (UpwardEnumerable.le_of_lt h)

-- `Std.Rio.pairwise_toList_le` (hypothesis 10): removable, the list is pairwise UpwardEnumerable.LT (rxo_chain), and LawfulUpwardEnumerableLE turns that into ≤.
theorem Rio.pairwise_toList_le.h10 : drop% Std.Rio.pairwise_toList_le 10 := by
  intros; exact (rxo_chain _).2.imp fun h => UpwardEnumerable.le_iff.2 (UpwardEnumerable.le_of_lt h)

/-! ## Removable: `isSome_succMany?` (`rxc_isSome`, `rxo_isSome`) -/

-- `Std.Roo.isSome_succMany?_of_lt_length_toList` (hypothesis 6): removable, the i-th list element is the i-th successor of succ? lower (rxo_isSome).
theorem Roo.isSome_succMany?_of_lt_length_toList.h6 : drop% Std.Roo.isSome_succMany?_of_lt_length_toList 6 := by
  intro α r _ _ _ _ _ i h
  obtain ⟨a, ha, hs⟩ := rxo_isSome (Roo.Internal.iter r) i h
  change UpwardEnumerable.succ? r.lower = some a at ha
  rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, ha, Option.bind_some]; exact hs

-- `Std.Roo.isSome_succMany?_of_lt_size_toArray` (hypothesis 6): removable, the i-th element is the i-th successor of succ? lower (rxo_isSome).
theorem Roo.isSome_succMany?_of_lt_size_toArray.h6 : drop% Std.Roo.isSome_succMany?_of_lt_size_toArray 6 := by
  intro α r _ _ _ _ _ i h
  rw [← Roo.toArray_toList, List.size_toArray] at h
  obtain ⟨a, ha, hs⟩ := rxo_isSome (Roo.Internal.iter r) i h
  change UpwardEnumerable.succ? r.lower = some a at ha
  rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, ha, Option.bind_some]; exact hs

-- `Std.Ric.isSome_succMany?_of_lt_length_toList` (hypothesis 7): removable, the i-th list element is the i-th successor of least (rxc_isSome).
theorem Ric.isSome_succMany?_of_lt_length_toList.h7 : drop% Std.Ric.isSome_succMany?_of_lt_length_toList 7 := by
  intro α r _ _ _ _ _ _ _ i h
  obtain ⟨a, ha, hs⟩ := rxc_isSome (Ric.Internal.iter r) i h
  change Least?.least? = some a at ha
  rw [Option.some.inj ((@UpwardEnumerable.least?_eq_some _ _ _ _ ⟨r.upper⟩).symm.trans ha)]; exact hs

-- `Std.Ric.isSome_succMany?_of_lt_size_toArray` (hypothesis 7): removable, the i-th element is the i-th successor of least (rxc_isSome).
theorem Ric.isSome_succMany?_of_lt_size_toArray.h7 : drop% Std.Ric.isSome_succMany?_of_lt_size_toArray 7 := by
  intro α r _ _ _ _ _ _ _ i h
  rw [← Ric.toArray_toList, List.size_toArray] at h
  obtain ⟨a, ha, hs⟩ := rxc_isSome (Ric.Internal.iter r) i h
  change Least?.least? = some a at ha
  rw [Option.some.inj ((@UpwardEnumerable.least?_eq_some _ _ _ _ ⟨r.upper⟩).symm.trans ha)]; exact hs

-- `Std.Rio.isSome_succMany?_of_lt_length_toList` (hypothesis 7): removable, the i-th list element is the i-th successor of least (rxo_isSome).
theorem Rio.isSome_succMany?_of_lt_length_toList.h7 : drop% Std.Rio.isSome_succMany?_of_lt_length_toList 7 := by
  intro α r _ _ _ _ _ _ _ i h
  obtain ⟨a, ha, hs⟩ := rxo_isSome (Rio.Internal.iter r) i h
  change Least?.least? = some a at ha
  rw [Option.some.inj ((@UpwardEnumerable.least?_eq_some _ _ _ _ ⟨r.upper⟩).symm.trans ha)]; exact hs

-- `Std.Rio.isSome_succMany?_of_lt_size_toArray` (hypothesis 7): removable, the i-th element is the i-th successor of least (rxo_isSome).
theorem Rio.isSome_succMany?_of_lt_size_toArray.h7 : drop% Std.Rio.isSome_succMany?_of_lt_size_toArray 7 := by
  intro α r _ _ _ _ _ _ _ i h
  rw [← Rio.toArray_toList, List.size_toArray] at h
  obtain ⟨a, ha, hs⟩ := rxo_isSome (Rio.Internal.iter r) i h
  change Least?.least? = some a at ha
  rw [Option.some.inj ((@UpwardEnumerable.least?_eq_some _ _ _ _ ⟨r.upper⟩).symm.trans ha)]; exact hs

/-! ## Removable: sizes (`rxc_length`, `rxo_length`) -/

-- `Std.Ric.length_toList` (hypothesis 8): removable, LawfulHasSize states the same recursion as the iterator (rxc_length).
theorem Ric.length_toList.h8 : drop% Std.Ric.length_toList 8 := by
  intro α r _ _ _ _ _ _ _ _; exact rxc_length (Ric.Internal.iter r)

-- `Std.Ric.size_toArray` (hypothesis 8): removable, LawfulHasSize states the same recursion as the iterator (rxc_length).
theorem Ric.size_toArray.h8 : drop% Std.Ric.size_toArray 8 := by
  intro α r _ _ _ _ _ _ _ _; rw [← Ric.toArray_toList, List.size_toArray]; exact rxc_length (Ric.Internal.iter r)

-- `Std.Rio.length_toList` (hypothesis 8): removable, LawfulHasSize states the same recursion as the iterator (rxo_length).
theorem Rio.length_toList.h8 : drop% Std.Rio.length_toList 8 := by
  intro α r _ _ _ _ _ _ _ _; exact rxo_length (Rio.Internal.iter r)

-- `Std.Rio.size_toArray` (hypothesis 8): removable, LawfulHasSize states the same recursion as the iterator (rxo_length).
theorem Rio.size_toArray.h8 : drop% Std.Rio.size_toArray 8 := by
  intro α r _ _ _ _ _ _ _ _; rw [← Rio.toArray_toList, List.size_toArray]; exact rxo_length (Rio.Internal.iter r)

/-! ## Removable: `LinearlyUpwardEnumerable` is derivable (`lin_of_least`) -/

-- `Std.Ric.toList_succ_eq_map` (hypothesis 5): removable, LinearlyUpwardEnumerable follows from LawfulUpwardEnumerable, LawfulUpwardEnumerableLeast? and InfinitelyUpwardEnumerable (lin_of_least).
theorem Ric.toList_succ_eq_map.h5 : drop% Std.Ric.toList_succ_eq_map 5 := by
  intros; haveI := lin_of_least (α := ‹_›); exact Ric.toList_succ_eq_map

-- `Std.Ric.toArray_succ_eq_map` (hypothesis 6): removable, LinearlyUpwardEnumerable is derivable (lin_of_least).
theorem Ric.toArray_succ_eq_map.h6 : drop% Std.Ric.toArray_succ_eq_map 6 := by
  intro α r; intros; haveI := lin_of_least (α := α); exact Ric.toArray_succ_eq_map (r := r)

-- `Std.Rio.toList_succ_eq_map` (hypothesis 5): removable, LinearlyUpwardEnumerable is derivable (lin_of_least).
theorem Rio.toList_succ_eq_map.h5 : drop% Std.Rio.toList_succ_eq_map 5 := by
  intros; haveI := lin_of_least (α := ‹_›); exact Rio.toList_succ_eq_map

-- `Std.Rio.toArray_succ_eq_map` (hypothesis 6): removable, LinearlyUpwardEnumerable is derivable (lin_of_least).
theorem Rio.toArray_succ_eq_map.h6 : drop% Std.Rio.toArray_succ_eq_map 6 := by
  intro α r; intros; haveI := lin_of_least (α := α); exact Rio.toArray_succ_eq_map (r := r)

/-! ## Necessary: `forIn'_congr` over Nat and `Id` -/

-- `Std.Roo.forIn'_congr` (hypothesis 17): necessary, over Nat and Id: r = r' = 0<...0 (empty), f = f' = yield, init = 0, init' = 1: forIn' gives 0 ≠ 1.
theorem Roo.forIn'_congr.h17 : ¬ drop0% Std.Roo.forIn'_congr 17 := fun h => by
  have := h (α := Nat) (m := Id) (r := ⟨0, 0⟩) (r' := ⟨0, 0⟩) (init := 0) (init' := 1)
    (f := fun _ _ b => pure (ForInStep.yield b)) (f' := fun _ _ b => pure (ForInStep.yield b)) rfl (fun _ _ _ => rfl)
  rw [Roo.forIn'_eq_forIn'_toList, Roo.forIn'_eq_forIn'_toList] at this; simp [Nat.roo00] at this

-- `Std.Roo.forIn'_congr` (hypothesis 18): necessary, over Nat and Id: r = r' = 0<...2 = [1], f returns done 0, f' returns done 1: forIn' gives 0 ≠ 1.
theorem Roo.forIn'_congr.h18 : ¬ drop0% Std.Roo.forIn'_congr 18 := fun h => by
  have := h (α := Nat) (m := Id) (r := ⟨0, 2⟩) (r' := ⟨0, 2⟩) (init := 0) (init' := 0)
    (f := fun _ _ _ => pure (ForInStep.done 0)) (f' := fun _ _ _ => pure (ForInStep.done 1)) rfl rfl
  rw [Roo.forIn'_eq_forIn'_toList, Roo.forIn'_eq_forIn'_toList] at this; simp [Nat.roo02] at this

-- `Std.Ric.forIn'_congr` (hypothesis 19): necessary, over Nat and Id: r = r' = *...=0, f = f' = yield, init = 0, init' = 1: forIn' gives 0 ≠ 1.
theorem Ric.forIn'_congr.h19 : ¬ drop0% Std.Ric.forIn'_congr 19 := fun h => by
  have := h (α := Nat) (m := Id) (r := ⟨0⟩) (r' := ⟨0⟩) (init := 0) (init' := 1)
    (f := fun _ _ b => pure (ForInStep.yield b)) (f' := fun _ _ b => pure (ForInStep.yield b)) rfl (fun _ _ _ => rfl)
  rw [Ric.forIn'_eq_forIn'_toList, Ric.forIn'_eq_forIn'_toList] at this; simp [Nat.ric0] at this

-- `Std.Ric.forIn'_congr` (hypothesis 20): necessary, over Nat and Id: r = r' = *...=0 = [0], f returns done 0, f' returns done 1: forIn' gives 0 ≠ 1.
theorem Ric.forIn'_congr.h20 : ¬ drop0% Std.Ric.forIn'_congr 20 := fun h => by
  have := h (α := Nat) (m := Id) (r := ⟨0⟩) (r' := ⟨0⟩) (init := 0) (init' := 0)
    (f := fun _ _ _ => pure (ForInStep.done 0)) (f' := fun _ _ _ => pure (ForInStep.done 1)) rfl rfl
  rw [Ric.forIn'_eq_forIn'_toList, Ric.forIn'_eq_forIn'_toList] at this; simp [Nat.ric0] at this

-- `Std.Rio.forIn'_congr` (hypothesis 19): necessary, over Nat and Id: r = r' = *...1, f = f' = yield, init = 0, init' = 1: forIn' gives 0 ≠ 1.
theorem Rio.forIn'_congr.h19 : ¬ drop0% Std.Rio.forIn'_congr 19 := fun h => by
  have := h (α := Nat) (m := Id) (r := ⟨1⟩) (r' := ⟨1⟩) (init := 0) (init' := 1)
    (f := fun _ _ b => pure (ForInStep.yield b)) (f' := fun _ _ b => pure (ForInStep.yield b)) rfl (fun _ _ _ => rfl)
  rw [Rio.forIn'_eq_forIn'_toList, Rio.forIn'_eq_forIn'_toList] at this; simp [Nat.rio1] at this

-- `Std.Rio.forIn'_congr` (hypothesis 20): necessary, over Nat and Id: r = r' = *...1 = [0], f returns done 0, f' returns done 1: forIn' gives 0 ≠ 1.
theorem Rio.forIn'_congr.h20 : ¬ drop0% Std.Rio.forIn'_congr 20 := fun h => by
  have := h (α := Nat) (m := Id) (r := ⟨1⟩) (r' := ⟨1⟩) (init := 0) (init' := 0)
    (f := fun _ _ _ => pure (ForInStep.done 0)) (f' := fun _ _ _ => pure (ForInStep.done 1)) rfl rfl
  rw [Rio.forIn'_eq_forIn'_toList, Rio.forIn'_eq_forIn'_toList] at this; simp [Nat.rio1] at this

/-! ## Necessary: membership and `toList` -/

-- `Std.Roo.mem_toList_iff_mem` (hypothesis 6): necessary, NLT2 (< misses (1,3), (0,5)): r = 0<...3 has toList [] (1 < 3 fails) but 2 ∈ r.
theorem Roo.mem_toList_iff_mem.h6 : ¬ drop0% Std.Roo.mem_toList_iff_mem 6 := fun h => by
  have := (h (α := NLT2) (r := ⟨NLT2.pt 0, NLT2.pt 3⟩) (a := NLT2.pt 2)).2 (Roo.mem_iff.2 ⟨by decide, by decide⟩)
  rw [NLT2.roo03] at this; simp at this

-- `Std.Roo.mem_toArray_iff_mem` (hypothesis 6): necessary, NLT2: r = 0<...3 has toArray #[] but 2 ∈ r.
theorem Roo.mem_toArray_iff_mem.h6 : ¬ drop0% Std.Roo.mem_toArray_iff_mem 6 := fun h => by
  have := (h (α := NLT2) (r := ⟨NLT2.pt 0, NLT2.pt 3⟩) (a := NLT2.pt 2)).2 (Roo.mem_iff.2 ⟨by decide, by decide⟩)
  rw [← Roo.toArray_toList, NLT2.roo03] at this; simp at this

-- `Std.Ric.mem_toList_iff_mem` (hypothesis 7): necessary, NLE2 (≤ misses (1,3), (0,5)): *...=3 has toList [0] but 2 ∈ *...=3.
theorem Ric.mem_toList_iff_mem.h7 : ¬ drop0% Std.Ric.mem_toList_iff_mem 7 := fun h => by
  have := (h (α := NLE2) (r := ⟨NLE2.pt 3⟩) (a := NLE2.pt 2)).2 (Ric.mem_iff.2 (by decide))
  rw [NLE2.ric3] at this; revert this; decide

-- `Std.Ric.mem_toArray_iff_mem` (hypothesis 7): necessary, NLE2: *...=3 has toArray #[0] but 2 ∈ *...=3.
theorem Ric.mem_toArray_iff_mem.h7 : ¬ drop0% Std.Ric.mem_toArray_iff_mem 7 := fun h => by
  have := (h (α := NLE2) (r := ⟨NLE2.pt 3⟩) (a := NLE2.pt 2)).2 (Ric.mem_iff.2 (by decide))
  rw [← Ric.toArray_toList, NLE2.ric3] at this; simp only [List.mem_toArray] at this; revert this; decide

-- `Std.Ric.mem_toList_iff_mem` (hypothesis 8): necessary, NLeast (least? = some 1): *...=1 has toList [1] but 0 ∈ *...=1.
theorem Ric.mem_toList_iff_mem.h8 : ¬ drop0% Std.Ric.mem_toList_iff_mem 8 := fun h => by
  have := (h (α := NLeast) (r := ⟨NLeast.pt 1⟩) (a := NLeast.pt 0)).2 (Ric.mem_iff.2 (by decide))
  rw [NLeast.ric1] at this; revert this; decide

-- `Std.Ric.mem_toArray_iff_mem` (hypothesis 8): necessary, NLeast: *...=1 has toArray #[1] but 0 ∈ *...=1.
theorem Ric.mem_toArray_iff_mem.h8 : ¬ drop0% Std.Ric.mem_toArray_iff_mem 8 := fun h => by
  have := (h (α := NLeast) (r := ⟨NLeast.pt 1⟩) (a := NLeast.pt 0)).2 (Ric.mem_iff.2 (by decide))
  rw [← Ric.toArray_toList, NLeast.ric1] at this; simp only [List.mem_toArray] at this; revert this; decide

-- `Std.Rio.mem_toList_iff_mem` (hypothesis 7): necessary, NLT2: *...3 has toList [0] (1 < 3 fails) but 2 ∈ *...3.
theorem Rio.mem_toList_iff_mem.h7 : ¬ drop0% Std.Rio.mem_toList_iff_mem 7 := fun h => by
  have := (h (α := NLT2) (r := ⟨NLT2.pt 3⟩) (a := NLT2.pt 2)).2 (Rio.mem_iff.2 (by decide))
  rw [NLT2.rio3] at this; revert this; decide

-- `Std.Rio.mem_toArray_iff_mem` (hypothesis 7): necessary, NLT2: *...3 has toArray #[0] but 2 ∈ *...3.
theorem Rio.mem_toArray_iff_mem.h7 : ¬ drop0% Std.Rio.mem_toArray_iff_mem 7 := fun h => by
  have := (h (α := NLT2) (r := ⟨NLT2.pt 3⟩) (a := NLT2.pt 2)).2 (Rio.mem_iff.2 (by decide))
  rw [← Rio.toArray_toList, NLT2.rio3] at this; simp only [List.mem_toArray] at this; revert this; decide

-- `Std.Rio.mem_toList_iff_mem` (hypothesis 8): necessary, NLeast: *...2 has toList [1] but 0 ∈ *...2.
theorem Rio.mem_toList_iff_mem.h8 : ¬ drop0% Std.Rio.mem_toList_iff_mem 8 := fun h => by
  have := (h (α := NLeast) (r := ⟨NLeast.pt 2⟩) (a := NLeast.pt 0)).2 (Rio.mem_iff.2 (by decide))
  rw [NLeast.rio2] at this; revert this; decide

-- `Std.Rio.mem_toArray_iff_mem` (hypothesis 8): necessary, NLeast: *...2 has toArray #[1] but 0 ∈ *...2.
theorem Rio.mem_toArray_iff_mem.h8 : ¬ drop0% Std.Rio.mem_toArray_iff_mem 8 := fun h => by
  have := (h (α := NLeast) (r := ⟨NLeast.pt 2⟩) (a := NLeast.pt 0)).2 (Rio.mem_iff.2 (by decide))
  rw [← Rio.toArray_toList, NLeast.rio2] at this; simp only [List.mem_toArray] at this; revert this; decide

-- `Std.Ric.mem_iff_mem_rcc` (hypothesis 6): necessary, NLE2: 5 ∈ *...=5, but 5 ∉ least...=5 = 0...=5 since ¬ 0 ≤ 5.
theorem Ric.mem_iff_mem_rcc.h6 : ¬ drop0% Std.Ric.mem_iff_mem_rcc 6 := fun h => by
  have := (h (α := NLE2) (r := ⟨NLE2.pt 5⟩) (a := NLE2.pt 5)).1 (Ric.mem_iff.2 (by decide))
  exact absurd (Rcc.mem_iff.1 this).1 (by decide)

-- `Std.Ric.toList_ne_nil` (hypothesis 7): necessary, NLE2: *...=5 has toList [] since ¬ 0 ≤ 5.
theorem Ric.toList_ne_nil.h7 : ¬ drop0% Std.Ric.toList_ne_nil 7 := fun h =>
  h (α := NLE2) (r := ⟨NLE2.pt 5⟩) NLE2.ric5

-- `Std.Ric.toArray_ne_empty` (hypothesis 7): necessary, NLE2: *...=5 has toArray #[] since ¬ 0 ≤ 5.
theorem Ric.toArray_ne_empty.h7 : ¬ drop0% Std.Ric.toArray_ne_empty 7 := fun h =>
  h (α := NLE2) (r := ⟨NLE2.pt 5⟩) (by rw [← Ric.toArray_toList, NLE2.ric5])

-- `Std.Ric.toList_ne_nil` (hypothesis 8): necessary, NLeast: *...=0 has toList [] since least = 1.
theorem Ric.toList_ne_nil.h8 : ¬ drop0% Std.Ric.toList_ne_nil 8 := fun h =>
  h (α := NLeast) (r := ⟨NLeast.pt 0⟩) NLeast.ric0

-- `Std.Ric.toArray_ne_empty` (hypothesis 8): necessary, NLeast: *...=0 has toArray #[] since least = 1.
theorem Ric.toArray_ne_empty.h8 : ¬ drop0% Std.Ric.toArray_ne_empty 8 := fun h =>
  h (α := NLeast) (r := ⟨NLeast.pt 0⟩) (by rw [← Ric.toArray_toList, NLeast.ric0])

/-! ## Necessary: `Pairwise` with the model's order -/

-- `Std.Roo.pairwise_toList_lt` (hypothesis 6): necessary, NLT2: 0<...4 has toList [1, 2, 3] but ¬ 1 < 3.
theorem Roo.pairwise_toList_lt.h6 : ¬ drop0% Std.Roo.pairwise_toList_lt 6 := fun h => by
  have := h (α := NLT2) (r := ⟨NLT2.pt 0, NLT2.pt 4⟩)
  rw [NLT2.roo04] at this; revert this; decide

-- `Std.Roo.pairwise_toList_le` (hypothesis 8): necessary, NLE2: 0<...4 has toList [1, 2, 3] but ¬ 1 ≤ 3.
theorem Roo.pairwise_toList_le.h8 : ¬ drop0% Std.Roo.pairwise_toList_le 8 := fun h => by
  have := h (α := NLE2) (r := ⟨NLE2.pt 0, NLE2.pt 4⟩)
  rw [NLE2.roo04] at this; revert this; decide

-- `Std.Ric.pairwise_toList_lt` (hypothesis 9): necessary, NLT2: *...=4 has toList [0, 1, 2, 3, 4] but ¬ 1 < 3.
theorem Ric.pairwise_toList_lt.h9 : ¬ drop0% Std.Ric.pairwise_toList_lt 9 := fun h => by
  have := h (α := NLT2) (r := ⟨NLT2.pt 4⟩)
  rw [NLT2.ric4] at this; revert this; decide

-- `Std.Ric.pairwise_toList_le` (hypothesis 8): necessary, NLE2: *...=4 has toList [0, 1, 2, 3, 4] but ¬ 1 ≤ 3.
theorem Ric.pairwise_toList_le.h8 : ¬ drop0% Std.Ric.pairwise_toList_le 8 := fun h => by
  have := h (α := NLE2) (r := ⟨NLE2.pt 4⟩)
  rw [NLE2.ric4] at this; revert this; decide

-- `Std.Rio.pairwise_toList_le` (hypothesis 9): necessary, NLE2: *...4 has toList [0, 1, 2, 3] but ¬ 1 ≤ 3.
theorem Rio.pairwise_toList_le.h9 : ¬ drop0% Std.Rio.pairwise_toList_le 9 := fun h => by
  have := h (α := NLE2) (r := ⟨NLE2.pt 4⟩)
  rw [NLE2.rio4] at this; revert this; decide

/-! ## Necessary: successor lemmas -/

-- `Std.Roo.mem_succ_succ_iff` (hypothesis 4): necessary, NMerge (succ 0 = succ 3 = 4, lawful otherwise): lo = 1, hi = 0, a = 3 ∈ 2<...4, but no a' ∈ 1<...0 (nothing is < 0).
theorem Roo.mem_succ_succ_iff.h4 : ¬ drop0% Std.Roo.mem_succ_succ_iff 4 := fun h => by
  obtain ⟨a', -, hm⟩ := (h (α := NMerge) (lo := NMerge.pt 1) (hi := NMerge.pt 0) (a := NMerge.pt 3)).1
    (Roo.mem_iff.2 ⟨by decide, by decide⟩)
  have := (Roo.mem_iff.1 hm).2
  change NMerge.lt a' 0 at this; unfold NMerge.lt at this; split at this <;> omega

-- `Std.Roo.mem_succ_succ_iff` (hypothesis 5): necessary, NLT2: lo = 0, hi = 3, a = 3 = succ 2 with 2 ∈ 0<...3, but 3 ∉ 1<...4 since ¬ 1 < 3.
theorem Roo.mem_succ_succ_iff.h5 : ¬ drop0% Std.Roo.mem_succ_succ_iff 5 := fun h => by
  have := (h (α := NLT2) (lo := NLT2.pt 0) (hi := NLT2.pt 3) (a := NLT2.pt 3)).2
    ⟨NLT2.pt 2, rfl, Roo.mem_iff.2 ⟨by decide, by decide⟩⟩
  exact absurd (Roo.mem_iff.1 this).1 (by decide)

-- `Std.Roo.mem_succ_succ_iff` (hypothesis 8): necessary, NBack (succMany? 1 1 = some 0 ≠ succ? 1; < and ≤ are UpwardEnumerable.LT/LE): lo = hi = a = 0: 0 ∈ 1<...1 (1 < 0 < 1), but 0 is no successor.
theorem Roo.mem_succ_succ_iff.h8 : ¬ drop0% Std.Roo.mem_succ_succ_iff 8 := fun h => by
  obtain ⟨a', ha', -⟩ := (h (α := NBack) (lo := NBack.pt 0) (hi := NBack.pt 0) (a := NBack.pt 0)).1
    (Roo.mem_iff.2 ⟨by decide, by decide⟩)
  have : (0 : Nat) = Nat.succ a' := ha'
  omega

-- `Std.Roo.succ_mem_succ_succ_iff` (hypothesis 4): necessary, NMerge: a = 0, lo = 1, hi = 4: succ 0 = 4 ∈ 2<...5, but 0 ∉ 1<...4.
theorem Roo.succ_mem_succ_succ_iff.h4 : ¬ drop0% Std.Roo.succ_mem_succ_succ_iff 4 := fun h => by
  have := (h (α := NMerge) (lo := NMerge.pt 1) (hi := NMerge.pt 4) (a := NMerge.pt 0)).1
    (Roo.mem_iff.2 ⟨by decide, by decide⟩)
  exact absurd (Roo.mem_iff.1 this).1 (by decide)

-- `Std.Roo.succ_mem_succ_succ_iff` (hypothesis 5): necessary, NLT2: a = 2, lo = 0, hi = 3: 2 ∈ 0<...3, but 3 ∉ 1<...4.
theorem Roo.succ_mem_succ_succ_iff.h5 : ¬ drop0% Std.Roo.succ_mem_succ_succ_iff 5 := fun h => by
  have := (h (α := NLT2) (lo := NLT2.pt 0) (hi := NLT2.pt 3) (a := NLT2.pt 2)).2
    (Roo.mem_iff.2 ⟨by decide, by decide⟩)
  exact absurd (Roo.mem_iff.1 this).1 (by decide)

-- `Std.Roo.succ_mem_succ_succ_iff` (hypothesis 8): necessary, NBack: a = 1, lo = 0, hi = 3: 1 ∈ 0<...3, but 2 ∉ 1<...4 since ¬ 1 < 2.
theorem Roo.succ_mem_succ_succ_iff.h8 : ¬ drop0% Std.Roo.succ_mem_succ_succ_iff 8 := fun h => by
  have := (h (α := NBack) (lo := NBack.pt 0) (hi := NBack.pt 3) (a := NBack.pt 1)).2
    (Roo.mem_iff.2 ⟨by decide, by decide⟩)
  exact absurd (Roo.mem_iff.1 this).1 (by decide)

-- `Std.Roo.toList_succ_succ_eq_map` (hypothesis 4): necessary, NMerge: lo = 1, hi = 0: (2<...4).toList = [3], (1<...0).toList = [].
theorem Roo.toList_succ_succ_eq_map.h4 : ¬ drop0% Std.Roo.toList_succ_succ_eq_map 4 := fun h => by
  have := h (α := NMerge) (lo := NMerge.pt 1) (hi := NMerge.pt 0)
  rw [show succ (NMerge.pt 1) = NMerge.pt 2 from rfl, show succ (NMerge.pt 0) = NMerge.pt 4 from rfl,
    NMerge.roo24, NMerge.roo10] at this
  simp at this

-- `Std.Roo.toArray_succ_succ_eq_map` (hypothesis 4): necessary, NMerge: lo = 1, hi = 0: (2<...4).toArray = #[3], (1<...0).toArray = #[].
theorem Roo.toArray_succ_succ_eq_map.h4 : ¬ drop0% Std.Roo.toArray_succ_succ_eq_map 4 := fun h => by
  have := h (α := NMerge) (lo := NMerge.pt 1) (hi := NMerge.pt 0)
  rw [show succ (NMerge.pt 1) = NMerge.pt 2 from rfl, show succ (NMerge.pt 0) = NMerge.pt 4 from rfl,
    ← Roo.toArray_toList, ← Roo.toArray_toList, NMerge.roo24, NMerge.roo10] at this
  simp at this

-- `Std.Roo.toList_succ_succ_eq_map` (hypothesis 5): necessary, NLT2: lo = 0, hi = 3: (1<...4).toList = [2, 3], (0<...3).toList = [].
theorem Roo.toList_succ_succ_eq_map.h5 : ¬ drop0% Std.Roo.toList_succ_succ_eq_map 5 := fun h => by
  have := h (α := NLT2) (lo := NLT2.pt 0) (hi := NLT2.pt 3)
  rw [show succ (NLT2.pt 0) = NLT2.pt 1 from rfl, show succ (NLT2.pt 3) = NLT2.pt 4 from rfl,
    NLT2.roo14, NLT2.roo03] at this
  simp at this

-- `Std.Roo.toArray_succ_succ_eq_map` (hypothesis 5): necessary, NLT2: lo = 0, hi = 3: (1<...4).toArray = #[2, 3], (0<...3).toArray = #[].
theorem Roo.toArray_succ_succ_eq_map.h5 : ¬ drop0% Std.Roo.toArray_succ_succ_eq_map 5 := fun h => by
  have := h (α := NLT2) (lo := NLT2.pt 0) (hi := NLT2.pt 3)
  rw [show succ (NLT2.pt 0) = NLT2.pt 1 from rfl, show succ (NLT2.pt 3) = NLT2.pt 4 from rfl,
    ← Roo.toArray_toList, ← Roo.toArray_toList, NLT2.roo14, NLT2.roo03] at this
  simp at this

-- `Std.Ric.mem_succ_iff` (hypothesis 4): necessary, NMerge: hi = 0, a = 3: 3 ≤ succ 0 = 4, but neither 3 ≤ 0 nor 3 = 4.
theorem Ric.mem_succ_iff.h4 : ¬ drop0% Std.Ric.mem_succ_iff 4 := fun h => by
  rcases (h (α := NMerge) (hi := NMerge.pt 0) (a := NMerge.pt 3)).1 (Ric.mem_iff.2 (by decide)) with h1 | h1
  · exact absurd (Ric.mem_iff.1 h1) (by decide)
  · exact absurd h1 (by decide)

-- `Std.Ric.mem_succ_iff` (hypothesis 5): necessary, NLE2: hi = 2, a = 1: 1 ≤ 2, but ¬ 1 ≤ succ 2 = 3.
theorem Ric.mem_succ_iff.h5 : ¬ drop0% Std.Ric.mem_succ_iff 5 := fun h => by
  have := (h (α := NLE2) (hi := NLE2.pt 2) (a := NLE2.pt 1)).2 (Or.inl (Ric.mem_iff.2 (by decide)))
  exact absurd (Ric.mem_iff.1 this) (by decide)

-- `Std.Ric.mem_succ_iff` (hypothesis 8): necessary, NBack: hi = 1, a = 1: 1 ≤ 1, but ¬ 1 ≤ succ 1 = 2.
theorem Ric.mem_succ_iff.h8 : ¬ drop0% Std.Ric.mem_succ_iff 8 := fun h => by
  have := (h (α := NBack) (hi := NBack.pt 1) (a := NBack.pt 1)).2 (Or.inl (Ric.mem_iff.2 (by decide)))
  exact absurd (Ric.mem_iff.1 this) (by decide)

-- `Std.Ric.succ_mem_succ_iff` (hypothesis 4): necessary, NMerge: a = 3, hi = 0: succ 3 = 4 ≤ succ 0 = 4, but ¬ 3 ≤ 0.
theorem Ric.succ_mem_succ_iff.h4 : ¬ drop0% Std.Ric.succ_mem_succ_iff 4 := fun h => by
  have := (h (α := NMerge) (hi := NMerge.pt 0) (a := NMerge.pt 3)).1 (Ric.mem_iff.2 (by decide))
  exact absurd (Ric.mem_iff.1 this) (by decide)

-- `Std.Ric.succ_mem_succ_iff` (hypothesis 5): necessary, NLE2: a = 0, hi = 2: 0 ≤ 2, but ¬ 1 ≤ 3.
theorem Ric.succ_mem_succ_iff.h5 : ¬ drop0% Std.Ric.succ_mem_succ_iff 5 := fun h => by
  have := (h (α := NLE2) (hi := NLE2.pt 2) (a := NLE2.pt 0)).2 (Ric.mem_iff.2 (by decide))
  exact absurd (Ric.mem_iff.1 this) (by decide)

-- `Std.Ric.succ_mem_succ_iff` (hypothesis 8): necessary, NBack: a = 1, hi = 2: 2 ≤ 3, but ¬ 1 ≤ 2.
theorem Ric.succ_mem_succ_iff.h8 : ¬ drop0% Std.Ric.succ_mem_succ_iff 8 := fun h => by
  have := (h (α := NBack) (hi := NBack.pt 2) (a := NBack.pt 1)).1 (Ric.mem_iff.2 (by decide))
  exact absurd (Ric.mem_iff.1 this) (by decide)

-- `Std.Ric.toList_succ_eq_map` (hypothesis 6): necessary, NLE2: hi = 2: (*...=3).toList = [0], but 0 :: (*...=2).toList.map succ = [0, 1, 2, 3].
theorem Ric.toList_succ_eq_map.h6 : ¬ drop0% Std.Ric.toList_succ_eq_map 6 := fun h => by
  have := h (α := NLE2) (hi := NLE2.pt 2)
  rw [show succ (NLE2.pt 2) = NLE2.pt 3 from rfl, NLE2.ric3, NLE2.ric2] at this
  revert this; decide

-- `Std.Ric.toArray_succ_eq_map` (hypothesis 7): necessary, NLE2: hi = 2: (*...=3).toArray = #[0], but #[0] ++ (*...=2).toArray.map succ = #[0, 1, 2, 3].
theorem Ric.toArray_succ_eq_map.h7 : ¬ drop0% Std.Ric.toArray_succ_eq_map 7 := fun h => by
  have := h (α := NLE2) (hi := NLE2.pt 2) (r := ⟨NLE2.pt 0⟩)
  rw [show succ (NLE2.pt 2) = NLE2.pt 3 from rfl, ← Ric.toArray_toList, ← Ric.toArray_toList,
    NLE2.ric3, NLE2.ric2] at this
  simp at this

-- `Std.Rio.mem_succ_iff` (hypothesis 4): necessary, NMerge: hi = 0, a = 3: 3 < succ 0 = 4, but neither 3 < 0 nor 3 = 0.
theorem Rio.mem_succ_iff.h4 : ¬ drop0% Std.Rio.mem_succ_iff 4 := fun h => by
  rcases (h (α := NMerge) (hi := NMerge.pt 0) (a := NMerge.pt 3)).1 (Rio.mem_iff.2 (by decide)) with h1 | h1
  · exact absurd (Rio.mem_iff.1 h1) (by decide)
  · exact absurd h1 (by decide)

-- `Std.Rio.mem_succ_iff` (hypothesis 5): necessary, NLT2: hi = 2, a = 1: 1 < 2, but ¬ 1 < succ 2 = 3.
theorem Rio.mem_succ_iff.h5 : ¬ drop0% Std.Rio.mem_succ_iff 5 := fun h => by
  have := (h (α := NLT2) (hi := NLT2.pt 2) (a := NLT2.pt 1)).2 (Or.inl (Rio.mem_iff.2 (by decide)))
  exact absurd (Rio.mem_iff.1 this) (by decide)

-- `Std.Rio.mem_succ_iff` (hypothesis 8): necessary, NBack: hi = a = 1: a = hi, but ¬ 1 < succ 1 = 2.
theorem Rio.mem_succ_iff.h8 : ¬ drop0% Std.Rio.mem_succ_iff 8 := fun h => by
  have := (h (α := NBack) (hi := NBack.pt 1) (a := NBack.pt 1)).2 (Or.inr rfl)
  exact absurd (Rio.mem_iff.1 this) (by decide)

-- `Std.Rio.succ_mem_succ_iff` (hypothesis 4): necessary, NMerge: a = 1, hi = 0: succ 1 = 2 < succ 0 = 4, but ¬ 1 < 0.
theorem Rio.succ_mem_succ_iff.h4 : ¬ drop0% Std.Rio.succ_mem_succ_iff 4 := fun h => by
  have := (h (α := NMerge) (hi := NMerge.pt 0) (a := NMerge.pt 1)).1 (Rio.mem_iff.2 (by decide))
  exact absurd (Rio.mem_iff.1 this) (by decide)

-- `Std.Rio.succ_mem_succ_iff` (hypothesis 5): necessary, NLT2: a = 0, hi = 2: 0 < 2, but ¬ 1 < 3.
theorem Rio.succ_mem_succ_iff.h5 : ¬ drop0% Std.Rio.succ_mem_succ_iff 5 := fun h => by
  have := (h (α := NLT2) (hi := NLT2.pt 2) (a := NLT2.pt 0)).2 (Rio.mem_iff.2 (by decide))
  exact absurd (Rio.mem_iff.1 this) (by decide)

-- `Std.Rio.succ_mem_succ_iff` (hypothesis 8): necessary, NBack: a = 1, hi = 2: 2 < 3, but ¬ 1 < 2.
theorem Rio.succ_mem_succ_iff.h8 : ¬ drop0% Std.Rio.succ_mem_succ_iff 8 := fun h => by
  have := (h (α := NBack) (hi := NBack.pt 2) (a := NBack.pt 1)).1 (Rio.mem_iff.2 (by decide))
  exact absurd (Rio.mem_iff.1 this) (by decide)

-- `Std.Rio.toList_succ_eq_map` (hypothesis 6): necessary, NLT2: hi = 2: (*...3).toList = [0], but 0 :: (*...2).toList.map succ = [0, 1, 2].
theorem Rio.toList_succ_eq_map.h6 : ¬ drop0% Std.Rio.toList_succ_eq_map 6 := fun h => by
  have := h (α := NLT2) (hi := NLT2.pt 2)
  rw [show succ (NLT2.pt 2) = NLT2.pt 3 from rfl, NLT2.rio3, NLT2.rio2] at this
  revert this; decide

-- `Std.Rio.toArray_succ_eq_map` (hypothesis 7): necessary, NLT2: hi = 2: (*...3).toArray = #[0], but #[0] ++ (*...2).toArray.map succ = #[0, 1, 2].
theorem Rio.toArray_succ_eq_map.h7 : ¬ drop0% Std.Rio.toArray_succ_eq_map 7 := fun h => by
  have := h (α := NLT2) (hi := NLT2.pt 2) (r := ⟨NLT2.pt 0⟩)
  rw [show succ (NLT2.pt 2) = NLT2.pt 3 from rfl, ← Rio.toArray_toList, ← Rio.toArray_toList,
    NLT2.rio3, NLT2.rio2] at this
  simp at this

/-! ## Necessary: `mem_of_mem_of_le`, `isEmpty` -/

-- `Std.Roo.mem_of_mem_of_le` (hypothesis 4): necessary, NLT2: r = 1<...4, b = 2, a = 3 ∈ 2<...4, but ¬ 1 < 3.
theorem Roo.mem_of_mem_of_le.h4 : ¬ drop0% Std.Roo.mem_of_mem_of_le 4 := fun h => by
  have := h (α := NLT2) (r := ⟨NLT2.pt 1, NLT2.pt 4⟩) (b := NLT2.pt 2) (a := NLT2.pt 3) ⟨1, rfl⟩
    (Roo.mem_iff.2 ⟨by decide, by decide⟩)
  exact absurd (Roo.mem_iff.1 this).1 (by decide)

-- `Std.Roo.mem_of_mem_of_le` (hypothesis 6): necessary, NBack: r = 0<...1, b = 1 (UpwardEnumerable.LE 0 1), a = 0 ∈ 1<...1, but ¬ 0 < 0.
theorem Roo.mem_of_mem_of_le.h6 : ¬ drop0% Std.Roo.mem_of_mem_of_le 6 := fun h => by
  have := h (α := NBack) (r := ⟨NBack.pt 0, NBack.pt 1⟩) (b := NBack.pt 1) (a := NBack.pt 0) ⟨1, rfl⟩
    (Roo.mem_iff.2 ⟨by decide, by decide⟩)
  exact absurd (Roo.mem_iff.1 this).1 (by decide)

-- `Std.Roo.mem_of_mem_of_le` (hypothesis 10): necessary, over Nat: r = 0<...1, a = b = 0: 0 ∉ r.
theorem Roo.mem_of_mem_of_le.h10 : ¬ drop0% Std.Roo.mem_of_mem_of_le 10 := fun h => by
  have := h (α := Nat) (r := ⟨0, 1⟩) (b := 0) (a := 0) ⟨0, rfl⟩
  exact absurd (Roo.mem_iff.1 this).1 (by decide)

-- `Std.Roo.isEmpty_iff_forall_not_mem` (hypothesis 7): necessary, NLT2 (with its lawful Rxo.HasSize): 0<...3 is empty by isEmpty (¬ 1 < 3), but 2 ∈ 0<...3.
theorem Roo.isEmpty_iff_forall_not_mem.h7 : ¬ drop0% Std.Roo.isEmpty_iff_forall_not_mem 7 := fun h => by
  have := (h (α := NLT2) (r := ⟨NLT2.pt 0, NLT2.pt 3⟩)).1 (by decide) (NLT2.pt 2)
  exact this (Roo.mem_iff.2 ⟨by decide, by decide⟩)

-- `Std.Roo.isEmpty_iff_forall_not_mem` (hypothesis 9): necessary, NBack (with its lawful Rxo.HasSize): 1<...2 is empty by isEmpty (¬ 2 < 2), but 0 ∈ 1<...2.
theorem Roo.isEmpty_iff_forall_not_mem.h9 : ¬ drop0% Std.Roo.isEmpty_iff_forall_not_mem 9 := fun h => by
  have := (h (α := NBack) (r := ⟨NBack.pt 1, NBack.pt 2⟩)).1 (by decide) (NBack.pt 0)
  exact this (Roo.mem_iff.2 ⟨by decide, by decide⟩)

-- `Std.Ric.isEmpty_iff_forall_not_mem` (hypothesis 6): necessary, UF (one point, no successor, ≤ empty): isEmpty is false, but nothing is ≤ pt.
theorem Ric.isEmpty_iff_forall_not_mem.h6 : ¬ drop0% Std.Ric.isEmpty_iff_forall_not_mem 6 := fun h => by
  have := (h (α := UF) (r := ⟨.pt⟩)).2 (fun a ha => (Ric.mem_iff.1 ha : False))
  exact absurd this (by decide)

-- `Std.Ric.isEmpty_iff_forall_not_mem` (hypothesis 8): necessary, M0 (one point, succMany? constantly none, ≤ empty): isEmpty is false, but nothing is ≤ pt.
theorem Ric.isEmpty_iff_forall_not_mem.h8 : ¬ drop0% Std.Ric.isEmpty_iff_forall_not_mem 8 := fun h => by
  have := (h (α := M0) (r := ⟨.pt⟩)).2 (fun a ha => (Ric.mem_iff.1 ha : False))
  exact absurd this (by decide)

-- `Std.Rio.isEmpty_iff_forall_not_mem` (hypothesis 6): necessary, NLT2: *...5 is empty by isEmpty (¬ 0 < 5), but 1 ∈ *...5.
theorem Rio.isEmpty_iff_forall_not_mem.h6 : ¬ drop0% Std.Rio.isEmpty_iff_forall_not_mem 6 := fun h => by
  have := (h (α := NLT2) (r := ⟨NLT2.pt 5⟩)).1 (by decide) (NLT2.pt 1)
  exact this (Rio.mem_iff.2 (by decide))

-- `Std.Rio.isEmpty_iff_forall_not_mem` (hypothesis 7): necessary, NLeast: *...1 is empty by isEmpty (least = 1), but 0 ∈ *...1.
theorem Rio.isEmpty_iff_forall_not_mem.h7 : ¬ drop0% Std.Rio.isEmpty_iff_forall_not_mem 7 := fun h => by
  have := (h (α := NLeast) (r := ⟨NLeast.pt 1⟩)).1 (by decide) (NLeast.pt 0)
  exact this (Rio.mem_iff.2 (by decide))

-- `Std.Rio.isEmpty_iff_forall_not_mem` (hypothesis 8): necessary, NBack: *...0 is empty by isEmpty (least = 0), but 1 ∈ *...0 (1 < 0).
theorem Rio.isEmpty_iff_forall_not_mem.h8 : ¬ drop0% Std.Rio.isEmpty_iff_forall_not_mem 8 := fun h => by
  have := (h (α := NBack) (r := ⟨NBack.pt 0⟩)).1 (by decide) (NBack.pt 1)
  exact this (Rio.mem_iff.2 (by decide))

/-! ## Necessary: sizes and indices -/

-- `Std.Ric.size_eq_match_roc` (hypothesis 10): necessary, NSz (HasSize constantly 0): (*...=0).size = 0, but the right-hand side is (0<...=0).size + 1 = 1.
theorem Ric.size_eq_match_roc.h10 : ¬ drop0% Std.Ric.size_eq_match_roc 10 := fun h => by
  have := h (α := NSz) (r := ⟨NSz.pt 0⟩)
  revert this; decide

-- `Std.Roo.size_eq_match_roc` (hypothesis 9): necessary, NSz: (0<...2).size = 0, but the right-hand side is 1.
theorem Roo.size_eq_match_roc.h9 : ¬ drop0% Std.Roo.size_eq_match_roc 9 := fun h => by
  have := h (α := NSz) (r := ⟨NSz.pt 0, NSz.pt 2⟩)
  revert this; decide

-- `Std.Rio.size_eq_match_roc` (hypothesis 10): necessary, NSz: (*...1).size = 0, but the right-hand side is 1.
theorem Rio.size_eq_match_roc.h10 : ¬ drop0% Std.Rio.size_eq_match_roc 10 := fun h => by
  have := h (α := NSz) (r := ⟨NSz.pt 1⟩)
  revert this; decide

-- `Std.Ric.length_toList` (hypothesis 10): necessary, NSz: (*...=0).toList = [0] has length 1, size 0.
theorem Ric.length_toList.h10 : ¬ drop0% Std.Ric.length_toList 10 := fun h => by
  have := h (α := NSz) (r := ⟨NSz.pt 0⟩)
  rw [NSz.ric0] at this; revert this; decide

-- `Std.Ric.size_toArray` (hypothesis 10): necessary, NSz: (*...=0).toArray = #[0] has size 1, size 0.
theorem Ric.size_toArray.h10 : ¬ drop0% Std.Ric.size_toArray 10 := fun h => by
  have := h (α := NSz) (r := ⟨NSz.pt 0⟩)
  rw [← Ric.toArray_toList, NSz.ric0] at this; revert this; decide

-- `Std.Roo.length_toList` (hypothesis 9): necessary, NSz: (0<...2).toList = [1] has length 1, size 0.
theorem Roo.length_toList.h9 : ¬ drop0% Std.Roo.length_toList 9 := fun h => by
  have := h (α := NSz) (r := ⟨NSz.pt 0, NSz.pt 2⟩)
  rw [NSz.roo02] at this; revert this; decide

-- `Std.Roo.size_toArray` (hypothesis 9): necessary, NSz: (0<...2).toArray = #[1] has size 1, size 0.
theorem Roo.size_toArray.h9 : ¬ drop0% Std.Roo.size_toArray 9 := fun h => by
  have := h (α := NSz) (r := ⟨NSz.pt 0, NSz.pt 2⟩)
  rw [← Roo.toArray_toList, NSz.roo02] at this; revert this; decide

-- `Std.Rio.length_toList` (hypothesis 10): necessary, NSz: (*...1).toList = [0] has length 1, size 0.
theorem Rio.length_toList.h10 : ¬ drop0% Std.Rio.length_toList 10 := fun h => by
  have := h (α := NSz) (r := ⟨NSz.pt 1⟩)
  rw [NSz.rio1] at this; revert this; decide

-- `Std.Rio.size_toArray` (hypothesis 10): necessary, NSz: (*...1).toArray = #[0] has size 1, size 0.
theorem Rio.size_toArray.h10 : ¬ drop0% Std.Rio.size_toArray 10 := fun h => by
  have := h (α := NSz) (r := ⟨NSz.pt 1⟩)
  rw [← Rio.toArray_toList, NSz.rio1] at this; revert this; decide

-- `Std.Ric.getElem?_toList_eq` (hypothesis 7): necessary, NLE2: (*...=3).toList = [0] has no index 2, but succMany? 2 0 = some 2 and 2 ≤ 3.
theorem Ric.getElem?_toList_eq.h7 : ¬ drop0% Std.Ric.getElem?_toList_eq 7 := fun h => by
  have := h (α := NLE2) (r := ⟨NLE2.pt 3⟩) (i := 2)
  rw [NLE2.ric3] at this; revert this; decide

-- `Std.Ric.getElem?_toArray_eq` (hypothesis 7): necessary, NLE2: (*...=3).toArray = #[0] has no index 2, but succMany? 2 0 = some 2 and 2 ≤ 3.
theorem Ric.getElem?_toArray_eq.h7 : ¬ drop0% Std.Ric.getElem?_toArray_eq 7 := fun h => by
  have := h (α := NLE2) (r := ⟨NLE2.pt 3⟩) (i := 2)
  rw [← Ric.toArray_toList, NLE2.ric3] at this; revert this; decide

-- `Std.Roo.getElem?_toList_eq` (hypothesis 6): necessary, NLT2: (0<...3).toList = [], but succMany? 2 0 = some 2 and 2 < 3.
theorem Roo.getElem?_toList_eq.h6 : ¬ drop0% Std.Roo.getElem?_toList_eq 6 := fun h => by
  have := h (α := NLT2) (r := ⟨NLT2.pt 0, NLT2.pt 3⟩) (i := 1)
  rw [NLT2.roo03] at this; revert this; decide

-- `Std.Roo.getElem?_toArray_eq` (hypothesis 6): necessary, NLT2: (0<...3).toArray = #[], but succMany? 2 0 = some 2 and 2 < 3.
theorem Roo.getElem?_toArray_eq.h6 : ¬ drop0% Std.Roo.getElem?_toArray_eq 6 := fun h => by
  have := h (α := NLT2) (r := ⟨NLT2.pt 0, NLT2.pt 3⟩) (i := 1)
  rw [← Roo.toArray_toList, NLT2.roo03] at this; revert this; decide

-- `Std.Rio.getElem?_toList_eq` (hypothesis 7): necessary, NLT2: (*...3).toList = [0] has no index 2, but succMany? 2 0 = some 2 and 2 < 3.
theorem Rio.getElem?_toList_eq.h7 : ¬ drop0% Std.Rio.getElem?_toList_eq 7 := fun h => by
  have := h (α := NLT2) (r := ⟨NLT2.pt 3⟩) (i := 2)
  rw [NLT2.rio3] at this; revert this; decide

-- `Std.Rio.getElem?_toArray_eq` (hypothesis 7): necessary, NLT2: (*...3).toArray = #[0] has no index 2, but succMany? 2 0 = some 2 and 2 < 3.
theorem Rio.getElem?_toArray_eq.h7 : ¬ drop0% Std.Rio.getElem?_toArray_eq 7 := fun h => by
  have := h (α := NLT2) (r := ⟨NLT2.pt 3⟩) (i := 2)
  rw [← Rio.toArray_toList, NLT2.rio3] at this; revert this; decide

-- `Std.Ric.isSome_succMany?_of_lt_length_toList` (hypothesis 11): necessary, U0 (one point without successor): succMany? 1 pt = none.
theorem Ric.isSome_succMany?_of_lt_length_toList.h11 : ¬ drop0% Std.Ric.isSome_succMany?_of_lt_length_toList 11 := fun h => by
  have := h (α := U0) (r := ⟨.pt⟩) (i := 1)
  revert this; decide

-- `Std.Ric.isSome_succMany?_of_lt_size_toArray` (hypothesis 11): necessary, U0: succMany? 1 pt = none.
theorem Ric.isSome_succMany?_of_lt_size_toArray.h11 : ¬ drop0% Std.Ric.isSome_succMany?_of_lt_size_toArray 11 := fun h => by
  have := h (α := U0) (r := ⟨.pt⟩) (i := 1)
  revert this; decide

-- `Std.Roo.isSome_succMany?_of_lt_length_toList` (hypothesis 9): necessary, U0: succMany? 1 pt = none.
theorem Roo.isSome_succMany?_of_lt_length_toList.h9 : ¬ drop0% Std.Roo.isSome_succMany?_of_lt_length_toList 9 := fun h => by
  have := h (α := U0) (r := ⟨.pt, .pt⟩) (i := 0)
  revert this; decide

-- `Std.Roo.isSome_succMany?_of_lt_size_toArray` (hypothesis 9): necessary, U0: succMany? 1 pt = none.
theorem Roo.isSome_succMany?_of_lt_size_toArray.h9 : ¬ drop0% Std.Roo.isSome_succMany?_of_lt_size_toArray 9 := fun h => by
  have := h (α := U0) (r := ⟨.pt, .pt⟩) (i := 0)
  revert this; decide

-- `Std.Rio.isSome_succMany?_of_lt_length_toList` (hypothesis 11): necessary, U0: succMany? 1 pt = none.
theorem Rio.isSome_succMany?_of_lt_length_toList.h11 : ¬ drop0% Std.Rio.isSome_succMany?_of_lt_length_toList 11 := fun h => by
  have := h (α := U0) (r := ⟨.pt⟩) (i := 1)
  revert this; decide

-- `Std.Rio.isSome_succMany?_of_lt_size_toArray` (hypothesis 11): necessary, U0: succMany? 1 pt = none.
theorem Rio.isSome_succMany?_of_lt_size_toArray.h11 : ¬ drop0% Std.Rio.isSome_succMany?_of_lt_size_toArray 11 := fun h => by
  have := h (α := U0) (r := ⟨.pt⟩) (i := 1)
  revert this; decide

/-! ## Necessary: `LawfulMonad` (monad `CM`) -/

-- `Std.Roo.forIn'_eq_forIn'_toList` (hypothesis 12): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = 0<...2 = [1], f := pure (.done c): the range loop binds twice (the iterator loop wraps f in a bind), the list loop once (2 vs 1).
theorem Roo.forIn'_eq_forIn'_toList.h12 : ¬ drop0% Std.Roo.forIn'_eq_forIn'_toList 12 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨0, 2⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  simp only [Nat.roo02] at e
  revert e; cm_unfold
  exact fun e => absurd (show (2 : Nat) = 1 from e) (by decide)

-- `Std.Roo.forIn'_eq_forIn'_toArray` (hypothesis 12): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = 0<...2 = [1], f := pure (.done c): the range loop binds twice (the iterator loop wraps f in a bind), the array loop once (2 vs 1).
theorem Roo.forIn'_eq_forIn'_toArray.h12 : ¬ drop0% Std.Roo.forIn'_eq_forIn'_toArray 12 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨0, 2⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  simp only [show (Roo.mk (0 : Nat) 2).toArray = #[1] by rw [← Roo.toArray_toList, Nat.roo02]] at e
  revert e; cm_unfold
  exact fun e => absurd (show (2 : Nat) = 1 from e) (by decide)

-- `Std.Roo.forIn'_toList_eq_forIn'` (hypothesis 12): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = 0<...2 = [1], f := pure (.done c): the range loop binds twice (the iterator loop wraps f in a bind), the list loop once (1 vs 2).
theorem Roo.forIn'_toList_eq_forIn'.h12 : ¬ drop0% Std.Roo.forIn'_toList_eq_forIn' 12 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨0, 2⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  simp only [Nat.roo02] at e
  revert e; cm_unfold
  exact fun e => absurd (show (1 : Nat) = 2 from e) (by decide)

-- `Std.Roo.forIn'_toArray_eq_forIn'` (hypothesis 12): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = 0<...2 = [1], f := pure (.done c): the range loop binds twice (the iterator loop wraps f in a bind), the array loop once (1 vs 2).
theorem Roo.forIn'_toArray_eq_forIn'.h12 : ¬ drop0% Std.Roo.forIn'_toArray_eq_forIn' 12 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨0, 2⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  simp only [show (Roo.mk (0 : Nat) 2).toArray = #[1] by rw [← Roo.toArray_toList, Nat.roo02]] at e
  revert e; cm_unfold
  exact fun e => absurd (show (1 : Nat) = 2 from e) (by decide)

-- `Std.Ric.forIn'_eq_forIn'_toList` (hypothesis 14): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = *...=0 = [0], f := pure (.done c): the range loop binds twice (the iterator loop wraps f in a bind), the list loop once (2 vs 1).
theorem Ric.forIn'_eq_forIn'_toList.h14 : ¬ drop0% Std.Ric.forIn'_eq_forIn'_toList 14 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨0⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  simp only [Nat.ric0] at e
  revert e; cm_unfold
  exact fun e => absurd (show (2 : Nat) = 1 from e) (by decide)

-- `Std.Ric.forIn'_eq_forIn'_toArray` (hypothesis 14): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = *...=0 = [0], f := pure (.done c): the range loop binds twice (the iterator loop wraps f in a bind), the array loop once (2 vs 1).
theorem Ric.forIn'_eq_forIn'_toArray.h14 : ¬ drop0% Std.Ric.forIn'_eq_forIn'_toArray 14 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨0⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  simp only [show (Ric.mk (0 : Nat)).toArray = #[0] by rw [← Ric.toArray_toList, Nat.ric0]] at e
  revert e; cm_unfold
  exact fun e => absurd (show (2 : Nat) = 1 from e) (by decide)

-- `Std.Ric.forIn'_toList_eq_forIn'` (hypothesis 14): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = *...=0 = [0], f := pure (.done c): the range loop binds twice (the iterator loop wraps f in a bind), the list loop once (1 vs 2).
theorem Ric.forIn'_toList_eq_forIn'.h14 : ¬ drop0% Std.Ric.forIn'_toList_eq_forIn' 14 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨0⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  simp only [Nat.ric0] at e
  revert e; cm_unfold
  exact fun e => absurd (show (1 : Nat) = 2 from e) (by decide)

-- `Std.Ric.forIn'_toArray_eq_forIn'` (hypothesis 14): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = *...=0 = [0], f := pure (.done c): the range loop binds twice (the iterator loop wraps f in a bind), the array loop once (1 vs 2).
theorem Ric.forIn'_toArray_eq_forIn'.h14 : ¬ drop0% Std.Ric.forIn'_toArray_eq_forIn' 14 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨0⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  simp only [show (Ric.mk (0 : Nat)).toArray = #[0] by rw [← Ric.toArray_toList, Nat.ric0]] at e
  revert e; cm_unfold
  exact fun e => absurd (show (1 : Nat) = 2 from e) (by decide)

-- `Std.Rio.forIn'_eq_forIn'_toList` (hypothesis 14): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = *...1 = [0], f := pure (.done c): the range loop binds twice (the iterator loop wraps f in a bind), the list loop once (2 vs 1).
theorem Rio.forIn'_eq_forIn'_toList.h14 : ¬ drop0% Std.Rio.forIn'_eq_forIn'_toList 14 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨1⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  simp only [Nat.rio1] at e
  revert e; cm_unfold
  exact fun e => absurd (show (2 : Nat) = 1 from e) (by decide)

-- `Std.Rio.forIn'_eq_forIn'_toArray` (hypothesis 14): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = *...1 = [0], f := pure (.done c): the range loop binds twice (the iterator loop wraps f in a bind), the array loop once (2 vs 1).
theorem Rio.forIn'_eq_forIn'_toArray.h14 : ¬ drop0% Std.Rio.forIn'_eq_forIn'_toArray 14 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨1⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  simp only [show (Rio.mk (1 : Nat)).toArray = #[0] by rw [← Rio.toArray_toList, Nat.rio1]] at e
  revert e; cm_unfold
  exact fun e => absurd (show (2 : Nat) = 1 from e) (by decide)

-- `Std.Rio.forIn'_toList_eq_forIn'` (hypothesis 14): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = *...1 = [0], f := pure (.done c): the range loop binds twice (the iterator loop wraps f in a bind), the list loop once (1 vs 2).
theorem Rio.forIn'_toList_eq_forIn'.h14 : ¬ drop0% Std.Rio.forIn'_toList_eq_forIn' 14 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨1⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  simp only [Nat.rio1] at e
  revert e; cm_unfold
  exact fun e => absurd (show (1 : Nat) = 2 from e) (by decide)

-- `Std.Rio.forIn'_toArray_eq_forIn'` (hypothesis 14): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = *...1 = [0], f := pure (.done c): the range loop binds twice (the iterator loop wraps f in a bind), the array loop once (1 vs 2).
theorem Rio.forIn'_toArray_eq_forIn'.h14 : ¬ drop0% Std.Rio.forIn'_toArray_eq_forIn' 14 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨1⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  simp only [show (Rio.mk (1 : Nat)).toArray = #[0] by rw [← Rio.toArray_toList, Nat.rio1]] at e
  revert e; cm_unfold
  exact fun e => absurd (show (1 : Nat) = 2 from e) (by decide)

-- `Std.Roo.forIn'_eq_match` (hypothesis 10): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = 0<...2 = [1], f := pure (.done c): the range loop binds twice, the unfolded right-hand side once (2 vs 1).
theorem Roo.forIn'_eq_match.h10 : ¬ drop0% Std.Roo.forIn'_eq_match 10 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨0, 2⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  revert e; cm_unfold
  exact fun e => absurd (show (2 : Nat) = 1 from e) (by decide)

-- `Std.Ric.forIn'_eq_ite_roc` (hypothesis 14): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = *...=0 = [0], f := pure (.done c): the range loop binds twice, the unfolded right-hand side once (2 vs 1).
theorem Ric.forIn'_eq_ite_roc.h14 : ¬ drop0% Std.Ric.forIn'_eq_ite_roc 14 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨0⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  revert e; cm_unfold
  exact fun e => absurd (show (2 : Nat) = 1 from e) (by decide)

-- `Std.Ric.forIn'_eq_if_roc` (hypothesis 14): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = *...=0 = [0], f := pure (.done c): the range loop binds twice, the unfolded right-hand side once (2 vs 1).
theorem Ric.forIn'_eq_if_roc.h14 : ¬ drop0% Std.Ric.forIn'_eq_if_roc 14 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨0⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  revert e; cm_unfold
  exact fun e => absurd (show (2 : Nat) = 1 from e) (by decide)

-- `Std.Rio.forIn'_eq_ite_roo` (hypothesis 12): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = *...1 = [0], f := pure (.done c): the range loop binds twice, the unfolded right-hand side once (2 vs 1).
theorem Rio.forIn'_eq_ite_roo.h12 : ¬ drop0% Std.Rio.forIn'_eq_ite_roo 12 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨1⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  revert e; cm_unfold
  exact fun e => absurd (show (2 : Nat) = 1 from e) (by decide)

-- `Std.Rio.forIn'_eq_if_roo` (hypothesis 12): necessary, CM (counts binds, ignores continuations; not lawful): over Nat, r = *...1 = [0], f := pure (.done c): the range loop binds twice, the unfolded right-hand side once (2 vs 1).
theorem Rio.forIn'_eq_if_roo.h12 : ¬ drop0% Std.Rio.forIn'_eq_if_roo 12 := fun h => by
  have e := h (α := Nat) (m := CM) (γ := Nat) (r := ⟨1⟩) (init := 0) (f := fun _ _ c => pure (ForInStep.done c))
  revert e; cm_unfold
  exact fun e => absurd (show (2 : Nat) = 1 from e) (by decide)

end RangeNdA2Hand
