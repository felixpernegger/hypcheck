import Lean

/-!
Hand pass `RangeNdB` (hand8): 123 non-dependent hypotheses of Range theorems: the unbounded ranges
`Std.Rci/Roi/Rii.*` of `Init.Data.Range.Polymorphic.Lemmas` (88), the iterator lemmas of
`Polymorphic/Iterators.lean` (24) and the class projections of `Polymorphic/PRange.lean` (11).
For hypothesis `hᵢ` of theorem `T` each declaration proves `¬T'` (necessary, `¬ drop0% T i`, universes
set to `0`) or `T'` (removable, `drop% T i`, universe-polymorphic).

104 necessary. Each refutation instantiates `T'` at one of the models below (or `Fin n` with the
library instances and one broken `≤`, `<`, `least?` or `Rxi.HasSize` passed in place of the
library one) and evaluates: range `toList` by unfolding the iterator steps (`rxi_eval`, as in
`runs/explore3/Eval.lean`), iterator outputs by constructing or excluding derivations of
`IsPlausibleIndirectOutput` (`out_direct`, `out_next`, `noOut_done`, `noOut_yield`), and range
`forIn'` in a non-lawful monad by unfolding the loop once (`loop_unfold`: `extrinsicFix₃_eq_fix` with
`IteratorLoop.wellFounded_of_finite`, then `WellFounded.fix_eq`).

19 removable:
* 16 `LinearlyUpwardEnumerable`/`LawfulUpwardEnumerableLE`/`…LT` hypotheses of
  `Rci/Roi.mem_succ_iff`, `succ_mem_succ_succ_iff`, `toList/toArray_succ_succ_eq_map`: the remaining
  `InfinitelyUpwardEnumerable` + `Rxi.IsAlwaysFinite` + `LawfulUpwardEnumerable` hold only on empty
  types (`false_of_inf_rxi_lue`), so these statements are vacuous;
* `Rxc/Rxo.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput` without
  `LawfulUpwardEnumerableLE/LT`: induction on the output relation, using only `LawfulUpwardEnumerable`;
* `Rii.forIn'_eq_match_rci` without `LawfulMonad`: both sides are definitionally the same loop.

Run with the lean4 repo's stage1 binary: `lean checks/RangeNdBHand.lean`.
-/

set_option linter.unusedVariables false
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
/-- `drop0% T i`: like `drop% T i`, with all universes of `T` set to `0` (for `¬` verdicts). -/
elab "drop0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => levelZero
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i.getNat]!
    unless ← isProp (← inferType x) do throwError "binder {i.getNat} of {n} is not a Prop"
    for j in [i.getNat+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i.getNat} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i.getNat) body

namespace RangeNdBHand
open Std Std.PRange

/-! ## Generic helpers (no verdicts) -/

-- Infinitely + Rxi-finite + lawful upward enumerable types are empty.
theorem false_of_inf_rxi_lue {α : Type u} [UpwardEnumerable α] [InfinitelyUpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] (a : α) : False := by
  obtain ⟨n, hn⟩ := Rxi.IsAlwaysFinite.finite a
  have : ∀ k, (succMany? k a).isSome := by
    intro k
    induction k with
    | zero => simp [succMany?_zero]
    | succ k ih =>
      rw [succMany?_add_one]
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ih
      rw [hx, Option.bind_some]
      exact InfinitelyUpwardEnumerable.isSome_succ? x
  have := this n; rw [hn] at this; cases this

-- An iterator whose only plausible step is `done` has no indirect outputs.
theorem noOut_done {α β : Type w} [Iterator α Id β] {it : Iter (α := α) β} {out : β}
    (h : ∀ s, it.IsPlausibleStep s → s = .done) : ¬ it.IsPlausibleIndirectOutput out := by
  intro ho
  cases ho with
  | direct hd =>
    obtain ⟨it', hs⟩ := Iter.isPlausibleOutput_iff_exists.1 hd
    cases h _ hs
  | indirect hs _ =>
    obtain ⟨s, hs1, hs2⟩ := Iter.isPlausibleSuccessorOf_iff_exists.1 hs
    cases h _ hs2; cases hs1

-- An iterator whose only plausible step yields `o ≠ out` and continues with an iterator `it'`
-- that never outputs `out` never outputs `out`.
theorem noOut_yield {α β : Type w} [Iterator α Id β] {it it' : Iter (α := α) β} {o out : β}
    (h : ∀ s, it.IsPlausibleStep s → s = .yield it' o) (ho : o ≠ out)
    (h' : ¬ it'.IsPlausibleIndirectOutput out) : ¬ it.IsPlausibleIndirectOutput out := by
  intro hi
  cases hi with
  | direct hd =>
    obtain ⟨it'', hs⟩ := Iter.isPlausibleOutput_iff_exists.1 hd
    cases h _ hs; exact ho rfl
  | indirect hs hi' =>
    obtain ⟨s, hs1, hs2⟩ := Iter.isPlausibleSuccessorOf_iff_exists.1 hs
    cases h _ hs2; cases hs1; exact h' hi'

theorem out_direct {α β : Type w} [Iterator α Id β] {it it' : Iter (α := α) β} {out : β}
    (h : it.IsPlausibleStep (.yield it' out)) : it.IsPlausibleIndirectOutput out :=
  .direct (Iter.isPlausibleOutput_iff_exists.2 ⟨it', h⟩)

theorem out_next {α β : Type w} [Iterator α Id β] {it it' : Iter (α := α) β} {o out : β}
    (h : it.IsPlausibleStep (.yield it' o)) (h' : it'.IsPlausibleIndirectOutput out) :
    it.IsPlausibleIndirectOutput out :=
  .indirect h.isPlausibleSuccessor_of_yield h'

/-! ## Models

* `Fin n` with the library instances (lawful, finite, `least? = some 0`); a broken `≤`, `<`,
  `least?` or `Rxi.HasSize` is passed explicitly in place of the library one.
* `S3`: `succ? 0 = some 1` (else `none`), but `succMany? 1` sends `0` and `1` to `2`; `≤`/`<` follow
  `succMany?` (`LawfulUpwardEnumerableLE/LT`), lawful `Rxi.HasSize`, `Rxi`-finite; not
  `LawfulUpwardEnumerable`. The iterators (which use `succ?`) visit `0, 1`, but `¬ 0 ≤ 1`.
* `Jump`: two elements, `succ? = none`, `succMany? (k+1) _ = some true`; `≤` always true,
  `a < b ↔ b = true`, `least? = some false` (`LawfulUpwardEnumerableLE/LT/Least?`); not lawful.
  The iterators from `false` stop after `false`, but `true` is a member.
* `Skip`: `succ? n = some (n+1)`, `succMany? 1 n = some (n+1)` only for `n ≤ 1`; `≤`/`<` follow
  `succMany?`; `Infinitely`/`LinearlyUpwardEnumerable`, `Rxi`-finite; not lawful. `≤` is not
  transitive: `0 ≤ 1 ≤ 2`, `¬ 0 ≤ 2`, and not preserved by `succ`: `1 ≤ 2`, `¬ 2 ≤ 3`.
* `UNone`: one element, `succ? = none`, `succMany? = none`; `≤` always false
  (`LawfulUpwardEnumerableLE`), lawful size `1`, `Rxi`-finite; not lawful (`succMany? 0 a = none`).
* `Loop1`: one element, `succ? = succMany? = some`, `≤`/`<` always true (no finiteness).
-/

structure S3 where
  n : Nat
deriving DecidableEq

instance : UpwardEnumerable S3 where
  succ? a := if a.n = 0 then some ⟨1⟩ else none
  succMany? k a := if k = 0 then some a else if k = 1 ∧ a.n ≤ 1 then some ⟨2⟩ else none

instance : LE S3 := ⟨fun a b => b = a ∨ (a.n ≤ 1 ∧ b.n = 2)⟩
instance : LT S3 := ⟨fun a b => a.n ≤ 1 ∧ b.n = 2⟩
instance : DecidableLE S3 := fun a b => inferInstanceAs (Decidable (b = a ∨ (a.n ≤ 1 ∧ b.n = 2)))
instance : DecidableLT S3 := fun a b => inferInstanceAs (Decidable (a.n ≤ 1 ∧ b.n = 2))

instance : LawfulUpwardEnumerableLE S3 where
  le_iff a b := by
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact ⟨0, by subst h; rfl⟩
      · exact ⟨1, by
          show (if 1 = 0 then some a else if 1 = 1 ∧ a.n ≤ 1 then some ⟨2⟩ else none) = some b
          cases b; simp_all⟩
    · rintro ⟨k, hk⟩
      change (if k = 0 then some a else if k = 1 ∧ a.n ≤ 1 then some ⟨2⟩ else none) = some b at hk
      split at hk
      · exact Or.inl (Option.some.inj hk).symm
      · split at hk
        · cases hk; exact Or.inr ⟨by omega, rfl⟩
        · cases hk

instance : LawfulUpwardEnumerableLT S3 where
  lt_iff a b := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨0, by
        show (if 0 + 1 = 0 then some a else if 0 + 1 = 1 ∧ a.n ≤ 1 then some ⟨2⟩ else none) = some b
        cases b; simp_all⟩
    · rintro ⟨k, hk⟩
      change (if k + 1 = 0 then some a else if k + 1 = 1 ∧ a.n ≤ 1 then some ⟨2⟩ else none) = some b at hk
      split at hk
      · omega
      · split at hk
        · cases hk; exact ⟨by omega, rfl⟩
        · cases hk

instance : Rxi.IsAlwaysFinite S3 := ⟨fun a => ⟨2, rfl⟩⟩
instance : Rxi.HasSize S3 := ⟨fun a => if a.n = 0 then 2 else 1⟩
instance : Rxi.LawfulHasSize S3 where
  size_eq_one_of_succ?_eq_none lo h := by
    change (if lo.n = 0 then some _ else none) = none at h
    show (if lo.n = 0 then 2 else 1) = 1
    split at h <;> simp_all
  size_eq_succ_of_succ?_eq_some lo lo' h := by
    change (if lo.n = 0 then some ⟨1⟩ else none) = some lo' at h
    show (if lo.n = 0 then 2 else 1) = (if lo'.n = 0 then 2 else 1) + 1
    split at h
    · cases h; simp_all
    · cases h

theorem S3.not_lue : ¬ LawfulUpwardEnumerable S3 := fun h => by
  have := h.succMany?_add_one 0 ⟨0⟩; cases this

structure Jump where
  b : Bool
deriving DecidableEq

instance : UpwardEnumerable Jump where
  succ? _ := none
  succMany? k _ := some ⟨k != 0⟩

instance : LE Jump := ⟨fun _ _ => True⟩
instance : LT Jump := ⟨fun _ b => b.b = true⟩
instance : DecidableLE Jump := fun _ _ => instDecidableTrue
instance : DecidableLT Jump := fun _ b => inferInstanceAs (Decidable (b.b = true))
instance : Least? Jump := ⟨some ⟨false⟩⟩

theorem Jump.ueLE (a b : Jump) : UpwardEnumerable.LE a b := by
  obtain ⟨_ | _⟩ := b
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

instance : LawfulUpwardEnumerableLE Jump := ⟨fun a b => ⟨fun _ => Jump.ueLE a b, fun _ => trivial⟩⟩
instance : LawfulUpwardEnumerableLT Jump where
  lt_iff a b := by
    constructor
    · intro h; obtain ⟨_ | _⟩ := b
      · cases h
      · exact ⟨0, rfl⟩
    · rintro ⟨k, hk⟩
      change some (⟨k + 1 != 0⟩ : Jump) = some b at hk
      cases hk; show (k + 1 != 0) = true; simp
instance : LawfulUpwardEnumerableLeast? Jump := ⟨fun a => ⟨⟨false⟩, rfl, Jump.ueLE _ a⟩⟩

theorem Jump.not_lue : ¬ LawfulUpwardEnumerable Jump := fun h => by
  have := h.succMany?_add_one 0 ⟨false⟩; cases this

structure Skip where
  n : Nat
deriving DecidableEq

instance : UpwardEnumerable Skip where
  succ? a := some ⟨a.n + 1⟩
  succMany? k a := if k = 0 then some a else if k = 1 ∧ a.n ≤ 1 then some ⟨a.n + 1⟩ else none

instance : LE Skip := ⟨fun a b => b = a ∨ (a.n ≤ 1 ∧ b.n = a.n + 1)⟩
instance : LT Skip := ⟨fun a b => a.n ≤ 1 ∧ b.n = a.n + 1⟩
instance : DecidableLE Skip := fun a b => inferInstanceAs (Decidable (b = a ∨ (a.n ≤ 1 ∧ b.n = a.n + 1)))
instance : DecidableLT Skip := fun a b => inferInstanceAs (Decidable (a.n ≤ 1 ∧ b.n = a.n + 1))

instance : LawfulUpwardEnumerableLE Skip where
  le_iff a b := by
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact ⟨0, by subst h; rfl⟩
      · exact ⟨1, by
          show (if 1 = 0 then some a else if 1 = 1 ∧ a.n ≤ 1 then some ⟨a.n + 1⟩ else none) = some b
          cases b; simp_all⟩
    · rintro ⟨k, hk⟩
      change (if k = 0 then some a else if k = 1 ∧ a.n ≤ 1 then some ⟨a.n + 1⟩ else none) = some b at hk
      split at hk
      · exact Or.inl (Option.some.inj hk).symm
      · split at hk
        · cases hk; exact Or.inr ⟨by omega, rfl⟩
        · cases hk

instance : LawfulUpwardEnumerableLT Skip where
  lt_iff a b := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨0, by
        show (if 0 + 1 = 0 then some a else if 0 + 1 = 1 ∧ a.n ≤ 1 then some ⟨a.n + 1⟩ else none) = some b
        cases b; simp_all⟩
    · rintro ⟨k, hk⟩
      change (if k + 1 = 0 then some a else if k + 1 = 1 ∧ a.n ≤ 1 then some ⟨a.n + 1⟩ else none) = some b at hk
      split at hk
      · omega
      · split at hk
        · cases hk; exact ⟨by omega, rfl⟩
        · cases hk

instance : InfinitelyUpwardEnumerable Skip := ⟨fun _ => rfl⟩
instance : LinearlyUpwardEnumerable Skip where
  eq_of_succ?_eq a b h := by
    cases a; cases b
    simp only [succ?, Option.some.injEq, Skip.mk.injEq] at h ⊢; omega
instance : Rxi.IsAlwaysFinite Skip := ⟨fun a => ⟨2, rfl⟩⟩

theorem Skip.not_lue : ¬ LawfulUpwardEnumerable Skip := fun h => by
  have := h.succMany?_add_one 1 ⟨0⟩; cases this

structure UNone where
deriving DecidableEq

instance : UpwardEnumerable UNone := ⟨fun _ => none, fun _ _ => none⟩
instance : LE UNone := ⟨fun _ _ => False⟩
instance : DecidableLE UNone := fun _ _ => instDecidableFalse
instance : LawfulUpwardEnumerableLE UNone := ⟨fun _ _ => ⟨False.elim, fun ⟨_, h⟩ => by cases h⟩⟩
instance : Rxi.IsAlwaysFinite UNone := ⟨fun _ => ⟨0, rfl⟩⟩
instance : Rxi.HasSize UNone := ⟨fun _ => 1⟩
instance : Rxi.LawfulHasSize UNone where
  size_eq_one_of_succ?_eq_none _ _ := rfl
  size_eq_succ_of_succ?_eq_some _ _ h := by cases h

theorem UNone.not_lue : ¬ LawfulUpwardEnumerable UNone := fun h => by
  have := h.succMany?_zero ⟨⟩; cases this

structure Loop1 where
deriving DecidableEq

instance : UpwardEnumerable Loop1 := ⟨fun _ => some ⟨⟩, fun _ _ => some ⟨⟩⟩
instance : LE Loop1 := ⟨fun _ _ => True⟩
instance : LT Loop1 := ⟨fun _ _ => True⟩

/-! ### Evaluation tactics -/

-- `toList` of an `Rxi` iterator over `Fin n` (as in `runs/explore3/Eval.lean`).
macro "rxi_eval" : tactic => `(tactic| (repeat (rw [Iter.toList_eq_match_step]; simp +decide only
  [Rxi.Iterator.step_eq_step, Rxi.Iterator.step, UpwardEnumerable.succ?, Fin.addNat?, Fin.val_zero,
   Fin.val_one, Fin.val_two, Nat.reduceAdd, ↓reduceDIte, Nat.reduceLT, Fin.isValue, Fin.mk_one,
   Fin.zero_eta])))

theorem tl_rci02 : (Rci.mk (0 : Fin 2)).toList = [0, 1] := by
  simp only [Rci.toList, Rci.Internal.iter]; rxi_eval
theorem tl_roi02 : (Roi.mk (0 : Fin 2)).toList = [1] := by
  simp only [Roi.toList, Roi.Internal.iter]; rxi_eval
theorem tl_roi03 : (Roi.mk (0 : Fin 3)).toList = [1, 2] := by
  simp only [Roi.toList, Roi.Internal.iter]; rxi_eval
theorem tl_rii2 : (Rii.mk : Rii (Fin 2)).toList = [0, 1] := by
  simp only [Rii.toList, Rii.Internal.iter, Least?.least?]; rxi_eval

end RangeNdBHand

namespace RangeNdBHand
open Std Std.PRange

/-! ## Verdicts: `Internal.isPlausibleIndirectOutput_iter_iff`, `upwardEnumerableLe_of_isPlausibleIndirectOutput` -/

-- `Std.Rcc.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 4: `Std.PRange.LawfulUpwardEnumerable α`): S3, r = 0...2: the iterator outputs 1 (succ? 0 = some 1), but ¬ 0 ≤ 1.
theorem it0 : ¬ drop0% Std.Rcc.Internal.isPlausibleIndirectOutput_iter_iff 4 := fun h => by
  have := (@h S3 _ _ _ _ ⟨⟨0⟩, ⟨2⟩⟩ ⟨1⟩).1 (out_next (Rxc.Iterator.isPlausibleStep_iff.2 rfl)
    (out_direct (Rxc.Iterator.isPlausibleStep_iff.2 rfl)))
  revert this; decide

-- `Std.Rcc.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerableLE α`): Fin 2 with a ≤ b :↔ b = 1, r = 0...1: the iterator outputs 0, but ¬ 0 ≤ 0.
theorem it1 : ¬ drop0% Std.Rcc.Internal.isPlausibleIndirectOutput_iter_iff 5 := fun h => by
  letI : LE (Fin 2) := ⟨fun _ b => b = 1⟩
  letI : DecidableLE (Fin 2) := fun _ b => inferInstanceAs (Decidable (b = 1))
  have := (@h (Fin 2) _ _ _ _ ⟨0, 1⟩ 0).1 (out_direct (Rxc.Iterator.isPlausibleStep_iff.2 rfl))
  exact absurd this.1 (by decide)

-- `Std.Rxc.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput` (hypothesis 4: `Std.PRange.LawfulUpwardEnumerable α`): S3, iterator from 0 with bound 2 outputs 1, but not UpwardEnumerable.LE 0 1.
theorem it2 : ¬ drop0% Std.Rxc.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput 4 := fun h => by
  obtain ⟨a, ha, hle⟩ := @h S3 _ _ _ _ (⟨⟨some ⟨0⟩, ⟨2⟩⟩⟩ : Iter (α := Rxc.Iterator S3) S3) ⟨1⟩
    (out_next (Rxc.Iterator.isPlausibleStep_iff.2 rfl) (out_direct (Rxc.Iterator.isPlausibleStep_iff.2 rfl)))
  cases ha
  exact absurd ((LawfulUpwardEnumerableLE.le_iff _ _).2 hle) (by decide)

-- `Std.Rco.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerable α`): S3, r = 0...<2: the iterator outputs 1, but ¬ 0 ≤ 1.
theorem it3 : ¬ drop0% Std.Rco.Internal.isPlausibleIndirectOutput_iter_iff 5 := fun h => by
  have := (@h S3 _ _ _ _ _ _ ⟨⟨0⟩, ⟨2⟩⟩ ⟨1⟩).1 (out_next (Rxo.Iterator.isPlausibleStep_iff.2 rfl)
    (out_direct (Rxo.Iterator.isPlausibleStep_iff.2 rfl)))
  revert this; decide

-- `Std.Rco.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 6: `Std.PRange.LawfulUpwardEnumerableLT α`): Fin 2 with a < b :↔ a = 1, r = 0...<0: 1 is a member, but the iterator stops at once (¬ 0 < 0).
theorem it4 : ¬ drop0% Std.Rco.Internal.isPlausibleIndirectOutput_iter_iff 6 := fun h => by
  letI : LT (Fin 2) := ⟨fun a _ => a = 1⟩
  letI : DecidableLT (Fin 2) := fun a _ => inferInstanceAs (Decidable (a = 1))
  exact noOut_done (fun s hs => (Rxo.Iterator.isPlausibleStep_iff.1 hs).trans rfl)
    ((@h (Fin 2) _ _ _ _ _ _ ⟨0, 0⟩ 1).2 (by decide))

-- `Std.Rxo.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput` (hypothesis 4: `Std.PRange.LawfulUpwardEnumerable α`): S3, iterator from 0 with bound 2 outputs 1, but not UpwardEnumerable.LE 0 1.
theorem it5 : ¬ drop0% Std.Rxo.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput 4 := fun h => by
  obtain ⟨a, ha, hle⟩ := @h S3 _ _ _ _ (⟨⟨some ⟨0⟩, ⟨2⟩⟩⟩ : Iter (α := Rxo.Iterator S3) S3) ⟨1⟩
    (out_next (Rxo.Iterator.isPlausibleStep_iff.2 rfl) (out_direct (Rxo.Iterator.isPlausibleStep_iff.2 rfl)))
  cases ha
  exact absurd ((LawfulUpwardEnumerableLE.le_iff _ _).2 hle) (by decide)

-- `Std.Rci.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 3: `Std.PRange.LawfulUpwardEnumerable α`): S3, r = 0...*: the iterator outputs 1, but ¬ 0 ≤ 1.
theorem it6 : ¬ drop0% Std.Rci.Internal.isPlausibleIndirectOutput_iter_iff 3 := fun h => by
  have := (@h S3 _ _ _ ⟨⟨0⟩⟩ ⟨1⟩).1 (out_next (Rxi.Iterator.isPlausibleStep_iff.2 rfl)
    (out_direct (Rxi.Iterator.isPlausibleStep_iff.2 rfl)))
  revert this; decide

-- `Std.Rci.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 4: `Std.PRange.LawfulUpwardEnumerableLE α`): Fin 2 with a ≤ b :↔ b = 1, r = 0...*: the iterator outputs 0, but ¬ 0 ≤ 0.
theorem it7 : ¬ drop0% Std.Rci.Internal.isPlausibleIndirectOutput_iter_iff 4 := fun h => by
  letI : LE (Fin 2) := ⟨fun _ b => b = 1⟩
  have := (@h (Fin 2) _ _ _ ⟨0⟩ 0).1 (out_direct (Rxi.Iterator.isPlausibleStep_iff.2 rfl))
  exact absurd (show (0 : Fin 2) = 1 from this) (by decide)

-- `Std.Rxi.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput` (hypothesis 2: `Std.PRange.LawfulUpwardEnumerable α`): S3, iterator from 0 outputs 1, but not UpwardEnumerable.LE 0 1.
theorem it8 : ¬ drop0% Std.Rxi.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput 2 := fun h => by
  obtain ⟨a, ha, hle⟩ := @h S3 _ (⟨⟨some ⟨0⟩⟩⟩ : Iter (α := Rxi.Iterator S3) S3) ⟨1⟩
    (out_next (Rxi.Iterator.isPlausibleStep_iff.2 rfl) (out_direct (Rxi.Iterator.isPlausibleStep_iff.2 rfl)))
  cases ha
  exact absurd ((LawfulUpwardEnumerableLE.le_iff _ _).2 hle) (by decide)

-- `Std.Roc.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerable α`): S3, r = 0<...2: the iterator outputs 1 (succ? 0), but ¬ 0 < 1.
theorem it9 : ¬ drop0% Std.Roc.Internal.isPlausibleIndirectOutput_iter_iff 5 := fun h => by
  have := (@h S3 _ _ _ _ _ _ ⟨⟨0⟩, ⟨2⟩⟩ ⟨1⟩).1 (out_direct (Rxc.Iterator.isPlausibleStep_iff.2 rfl))
  revert this; decide

-- `Std.Roc.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 6: `Std.PRange.LawfulUpwardEnumerableLE α`): Fin 3 with a ≤ b :↔ a ≠ 1, r = 0<...0: 2 is a member, but the iterator stops at 1 (¬ 1 ≤ 0).
theorem it10 : ¬ drop0% Std.Roc.Internal.isPlausibleIndirectOutput_iter_iff 6 := fun h => by
  letI : LE (Fin 3) := ⟨fun a _ => a ≠ 1⟩
  letI : DecidableLE (Fin 3) := fun a _ => inferInstanceAs (Decidable (a ≠ 1))
  exact noOut_done (fun s hs => (Rxc.Iterator.isPlausibleStep_iff.1 hs).trans rfl)
    ((@h (Fin 3) _ _ _ _ _ _ ⟨0, 0⟩ 2).2 (by decide))

-- `Std.Roo.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 6: `Std.PRange.LawfulUpwardEnumerable α`): S3, r = 0<...<2: the iterator outputs 1, but ¬ 0 < 1.
theorem it11 : ¬ drop0% Std.Roo.Internal.isPlausibleIndirectOutput_iter_iff 6 := fun h => by
  have := (@h S3 _ _ _ _ _ _ _ ⟨⟨0⟩, ⟨2⟩⟩ ⟨1⟩).1 (out_direct (Rxo.Iterator.isPlausibleStep_iff.2 rfl))
  revert this; decide

-- `Std.Roi.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 3: `Std.PRange.LawfulUpwardEnumerable α`): S3, r = 0<...*: the iterator outputs 1, but ¬ 0 < 1.
theorem it12 : ¬ drop0% Std.Roi.Internal.isPlausibleIndirectOutput_iter_iff 3 := fun h => by
  have := (@h S3 _ _ _ ⟨⟨0⟩⟩ ⟨1⟩).1 (out_direct (Rxi.Iterator.isPlausibleStep_iff.2 rfl))
  revert this; decide

-- `Std.Roi.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 4: `Std.PRange.LawfulUpwardEnumerableLT α`): Fin 2 with < always false, r = 0<...*: the iterator outputs 1, but ¬ 0 < 1.
theorem it13 : ¬ drop0% Std.Roi.Internal.isPlausibleIndirectOutput_iter_iff 4 := fun h => by
  letI : LT (Fin 2) := ⟨fun _ _ => False⟩
  exact (@h (Fin 2) _ _ _ ⟨0⟩ 1).1 (out_direct (Rxi.Iterator.isPlausibleStep_iff.2 rfl))

-- `Std.Ric.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerable α`): Jump, r = *...true: true is a member, but the iterator outputs only false (succ? false = none).
theorem it14 : ¬ drop0% Std.Ric.Internal.isPlausibleIndirectOutput_iter_iff 5 := fun h =>
  noOut_yield (fun s hs => (Rxc.Iterator.isPlausibleStep_iff.1 hs).trans rfl) (by decide)
    (noOut_done (fun s hs => (Rxc.Iterator.isPlausibleStep_iff.1 hs).trans rfl))
    ((@h Jump _ _ _ _ _ _ ⟨⟨true⟩⟩ ⟨true⟩).2 trivial)

-- `Std.Ric.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 6: `Std.PRange.LawfulUpwardEnumerableLE α`): Fin 2 with a ≤ b :↔ a = 1, r = *...0: 1 is a member, but the iterator stops at once (¬ 0 ≤ 0).
theorem it15 : ¬ drop0% Std.Ric.Internal.isPlausibleIndirectOutput_iter_iff 6 := fun h => by
  letI : LE (Fin 2) := ⟨fun a _ => a = 1⟩
  letI : DecidableLE (Fin 2) := fun a _ => inferInstanceAs (Decidable (a = 1))
  exact noOut_done (fun s hs => (Rxc.Iterator.isPlausibleStep_iff.1 hs).trans rfl)
    ((@h (Fin 2) _ _ _ _ _ _ ⟨0⟩ 1).2 (by decide))

-- `Std.Ric.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 7: `Std.PRange.LawfulUpwardEnumerableLeast? α`): Fin 2 with least? = none, r = *...1: 0 is a member, but the iterator is empty.
theorem it16 : ¬ drop0% Std.Ric.Internal.isPlausibleIndirectOutput_iter_iff 7 := fun h => by
  letI : Least? (Fin 2) := ⟨none⟩
  exact noOut_done (fun s hs => (Rxc.Iterator.isPlausibleStep_iff.1 hs).trans rfl)
    ((@h (Fin 2) _ _ _ _ _ _ ⟨1⟩ 0).2 (by decide))

-- `Std.Rio.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerable α`): Jump, r = *...<true: true is a member, but the iterator outputs only false.
theorem it17 : ¬ drop0% Std.Rio.Internal.isPlausibleIndirectOutput_iter_iff 5 := fun h =>
  noOut_yield (fun s hs => (Rxo.Iterator.isPlausibleStep_iff.1 hs).trans rfl) (by decide)
    (noOut_done (fun s hs => (Rxo.Iterator.isPlausibleStep_iff.1 hs).trans rfl))
    ((@h Jump _ _ _ _ _ _ ⟨⟨true⟩⟩ ⟨true⟩).2 rfl)

-- `Std.Rio.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 6: `Std.PRange.LawfulUpwardEnumerableLT α`): Fin 2 with a < b :↔ a = 1, r = *...<0: 1 is a member, but the iterator stops at once (¬ 0 < 0).
theorem it18 : ¬ drop0% Std.Rio.Internal.isPlausibleIndirectOutput_iter_iff 6 := fun h => by
  letI : LT (Fin 2) := ⟨fun a _ => a = 1⟩
  letI : DecidableLT (Fin 2) := fun a _ => inferInstanceAs (Decidable (a = 1))
  exact noOut_done (fun s hs => (Rxo.Iterator.isPlausibleStep_iff.1 hs).trans rfl)
    ((@h (Fin 2) _ _ _ _ _ _ ⟨0⟩ 1).2 (by decide))

-- `Std.Rio.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 7: `Std.PRange.LawfulUpwardEnumerableLeast? α`): Fin 2 with least? = none, r = *...<1: 0 is a member, but the iterator is empty.
theorem it19 : ¬ drop0% Std.Rio.Internal.isPlausibleIndirectOutput_iter_iff 7 := fun h => by
  letI : Least? (Fin 2) := ⟨none⟩
  exact noOut_done (fun s hs => (Rxo.Iterator.isPlausibleStep_iff.1 hs).trans rfl)
    ((@h (Fin 2) _ _ _ _ _ _ ⟨1⟩ 0).2 (by decide))

-- `Std.Rii.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 3: `Std.PRange.LawfulUpwardEnumerable α`): Jump: true is a member of *...*, but the iterator outputs only false.
theorem it20 : ¬ drop0% Std.Rii.Internal.isPlausibleIndirectOutput_iter_iff 3 := fun h =>
  noOut_yield (fun s hs => (Rxi.Iterator.isPlausibleStep_iff.1 hs).trans rfl) (by decide)
    (noOut_done (fun s hs => (Rxi.Iterator.isPlausibleStep_iff.1 hs).trans rfl))
    ((@h Jump _ _ _ ⟨⟩ ⟨true⟩).2 trivial)

-- `Std.Rii.Internal.isPlausibleIndirectOutput_iter_iff` (hypothesis 4: `Std.PRange.LawfulUpwardEnumerableLeast? α`): Fin 2 with least? = none: 0 is a member of *...*, but the iterator is empty.
theorem it21 : ¬ drop0% Std.Rii.Internal.isPlausibleIndirectOutput_iter_iff 4 := fun h => by
  letI : Least? (Fin 2) := ⟨none⟩
  exact noOut_done (fun s hs => (Rxi.Iterator.isPlausibleStep_iff.1 hs).trans rfl)
    ((@h (Fin 2) _ _ _ ⟨⟩ 0).2 trivial)

end RangeNdBHand

namespace RangeNdBHand
open Std Std.PRange

-- `Std.Rxc.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerableLE α`): removable; every output is reached from the first state by succ? steps, which UpwardEnumerable.LE follows by LawfulUpwardEnumerable alone (induction on the output relation).
theorem it22 : drop% Std.Rxc.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput 5 := by
  intro α _ _ _ _ it out hout
  induction hout with
  | direct h =>
    obtain ⟨it', hs⟩ := Iter.isPlausibleOutput_iff_exists.1 h
    rw [Rxc.Iterator.isPlausibleStep_iff, Rxc.Iterator.step] at hs
    split at hs
    · cases hs
    · split at hs
      · cases hs; exact ⟨_, ‹_›, UpwardEnumerable.le_refl _⟩
      · cases hs
  | indirect h _ ih =>
    obtain ⟨s, hs1, hs2⟩ := Iter.isPlausibleSuccessorOf_iff_exists.1 h
    rw [Rxc.Iterator.isPlausibleStep_iff, Rxc.Iterator.step] at hs2
    obtain ⟨a', ha', hle⟩ := ih
    split at hs2
    · subst hs2; cases hs1
    · rename_i x hx
      split at hs2
      · subst hs2; cases hs1
        exact ⟨x, hx, UpwardEnumerable.le_trans (UpwardEnumerable.le_of_succ?_eq ha') hle⟩
      · subst hs2; cases hs1

-- `Std.Rxo.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerableLT α`): removable; every output is reached from the first state by succ? steps, which UpwardEnumerable.LE follows by LawfulUpwardEnumerable alone (induction on the output relation).
theorem it23 : drop% Std.Rxo.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput 5 := by
  intro α _ _ _ _ it out hout
  induction hout with
  | direct h =>
    obtain ⟨it', hs⟩ := Iter.isPlausibleOutput_iff_exists.1 h
    rw [Rxo.Iterator.isPlausibleStep_iff, Rxo.Iterator.step] at hs
    split at hs
    · cases hs
    · split at hs
      · cases hs; exact ⟨_, ‹_›, UpwardEnumerable.le_refl _⟩
      · cases hs
  | indirect h _ ih =>
    obtain ⟨s, hs1, hs2⟩ := Iter.isPlausibleSuccessorOf_iff_exists.1 h
    rw [Rxo.Iterator.isPlausibleStep_iff, Rxo.Iterator.step] at hs2
    obtain ⟨a', ha', hle⟩ := ih
    split at hs2
    · subst hs2; cases hs1
    · rename_i x hx
      split at hs2
      · subst hs2; cases hs1
        exact ⟨x, hx, UpwardEnumerable.le_trans (UpwardEnumerable.le_of_succ?_eq ha') hle⟩
      · subst hs2; cases hs1

end RangeNdBHand

namespace RangeNdBHand
open Std Std.PRange

@[instance_reducible] def leastNone : Least? (Fin 2) := ⟨none⟩
@[instance_reducible] def least1 : Least? (Fin 2) := ⟨some 1⟩

theorem tl_rii_none : @Rii.toList (Fin 2) _ leastNone ⟨⟩ _ _ = [] := by
  simp only [Rii.toList, Rii.Internal.iter]; rxi_eval
theorem tl_rii_1 : @Rii.toList (Fin 2) _ least1 ⟨⟩ _ _ = [1] := by
  simp only [Rii.toList, Rii.Internal.iter, show @Least?.least? (Fin 2) least1 = some 1 from rfl]; rxi_eval

-- `Std.Rii.toList_eq_nil_iff` (hypothesis 8: `Std.PRange.LawfulUpwardEnumerableLeast? α`): Fin 2 with least? = none: toList = [], but Fin 2 is nonempty.
theorem t0 : ¬ drop0% Std.Rii.toList_eq_nil_iff 8 := fun h =>
  (@h (Fin 2) ⟨⟩ _ _ leastNone _ _ _ _).1 tl_rii_none ⟨0⟩

-- `Std.Rii.toArray_eq_empty_iff` (hypothesis 8: `Std.PRange.LawfulUpwardEnumerableLeast? α`): Fin 2 with least? = none: toArray = #[], but Fin 2 is nonempty.
theorem t1 : ¬ drop0% Std.Rii.toArray_eq_empty_iff 8 := fun h =>
  (@h (Fin 2) ⟨⟩ _ _ leastNone _ _ _ _).1 (by rw [← @Rii.toArray_toList (Fin 2) ⟨⟩ leastNone, tl_rii_none]) ⟨0⟩

-- `Std.Rii.mem_toList` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerableLeast? α`): Fin 2 with least? = some 1: toList = [1] misses 0.
theorem t2 : ¬ drop0% Std.Rii.mem_toList 5 := fun h => by
  have := @h (Fin 2) ⟨⟩ least1 _ _ _ 0
  rw [tl_rii_1] at this; simp at this

-- `Std.Rii.mem_toArray` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerableLeast? α`): Fin 2 with least? = some 1: toArray = #[1] misses 0.
theorem t3 : ¬ drop0% Std.Rii.mem_toArray 5 := fun h => by
  have := @h (Fin 2) ⟨⟩ least1 _ _ _ 0
  rw [← @Rii.toArray_toList (Fin 2) ⟨⟩ least1, tl_rii_1] at this; simp at this

-- `Std.Rii.isEmpty_iff` (hypothesis 4: `Std.PRange.LawfulUpwardEnumerableLeast? α`): Fin 2 with least? = none: isEmpty, but Fin 2 is nonempty.
theorem t4 : ¬ drop0% Std.Rii.isEmpty_iff 4 := fun h =>
  (@h (Fin 2) ⟨⟩ leastNone _).1 rfl ⟨0⟩

-- `Std.Rii.isEmpty_iff_forall_not_mem` (hypothesis 7: `Std.PRange.LawfulUpwardEnumerableLeast? α`): Fin 2 with least? = none: isEmpty, but 0 ∈ *...*.
theorem t5 : ¬ drop0% Std.Rii.isEmpty_iff_forall_not_mem 7 := fun h =>
  (@h (Fin 2) ⟨⟩ _ _ leastNone _ _ _).1 rfl 0 trivial

-- `Std.Rii.mem_iff_mem_rci` (hypothesis 6: `Std.PRange.LawfulUpwardEnumerableLE α`): Fin 2 with ≤ always false: 0 ∈ *...*, but ¬ least ≤ 0.
theorem t6 : ¬ drop0% Std.Rii.mem_iff_mem_rci 6 := fun h => by
  letI : LE (Fin 2) := ⟨fun _ _ => False⟩
  exact (@h (Fin 2) ⟨⟩ _ _ _ _ _ _ 0).1 trivial

-- `Std.Rii.pairwise_toList_lt` (hypothesis 6: `Std.PRange.LawfulUpwardEnumerableLT α`): Fin 2 with < always false: toList = [0, 1].
theorem t7 : ¬ drop0% Std.Rii.pairwise_toList_lt 6 := fun h => by
  letI : LT (Fin 2) := ⟨fun _ _ => False⟩
  have := @h (Fin 2) ⟨⟩ _ _ _ _ _ _
  rw [tl_rii2] at this; exact List.rel_of_pairwise_cons this (List.mem_singleton_self 1)

-- `Std.Rii.pairwise_toList_le` (hypothesis 6: `Std.PRange.LawfulUpwardEnumerableLE α`): Fin 2 with ≤ always false: toList = [0, 1].
theorem t8 : ¬ drop0% Std.Rii.pairwise_toList_le 6 := fun h => by
  letI : LE (Fin 2) := ⟨fun _ _ => False⟩
  have := @h (Fin 2) ⟨⟩ _ _ _ _ _ _
  rw [tl_rii2] at this; exact List.rel_of_pairwise_cons this (List.mem_singleton_self 1)

-- `Std.Rci.mem_toList_iff_mem` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerableLE α`): Fin 2 with ≤ always false: 0 ∈ (0...*).toList = [0, 1], but 0 ∉ 0...*.
theorem t9 : ¬ drop0% Std.Rci.mem_toList_iff_mem 5 := fun h => by
  letI : LE (Fin 2) := ⟨fun _ _ => False⟩
  have := @h (Fin 2) ⟨0⟩ _ _ _ _ 0
  rw [tl_rci02] at this; exact this.1 (by simp)

-- `Std.Rci.mem_toArray_iff_mem` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerableLE α`): Fin 2 with ≤ always false: 0 ∈ (0...*).toArray = #[0, 1], but 0 ∉ 0...*.
theorem t10 : ¬ drop0% Std.Rci.mem_toArray_iff_mem 5 := fun h => by
  letI : LE (Fin 2) := ⟨fun _ _ => False⟩
  have := @h (Fin 2) ⟨0⟩ _ _ _ _ 0
  rw [← Rci.toArray_toList, tl_rci02] at this; exact this.1 (by simp)

-- `Std.Rci.pairwise_toList_lt` (hypothesis 6: `Std.PRange.LawfulUpwardEnumerableLT α`): Fin 2 with < always false: (0...*).toList = [0, 1].
theorem t11 : ¬ drop0% Std.Rci.pairwise_toList_lt 6 := fun h => by
  letI : LT (Fin 2) := ⟨fun _ _ => False⟩
  have := @h (Fin 2) ⟨0⟩ _ _ _ _ _
  rw [tl_rci02] at this; exact List.rel_of_pairwise_cons this (List.mem_singleton_self 1)

-- `Std.Rci.pairwise_toList_le` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerableLE α`): Fin 2 with ≤ always false: (0...*).toList = [0, 1].
theorem t12 : ¬ drop0% Std.Rci.pairwise_toList_le 5 := fun h => by
  letI : LE (Fin 2) := ⟨fun _ _ => False⟩
  have := @h (Fin 2) ⟨0⟩ _ _ _ _
  rw [tl_rci02] at this; exact List.rel_of_pairwise_cons this (List.mem_singleton_self 1)

-- `Std.Roi.mem_toList_iff_mem` (hypothesis 6: `Std.PRange.LawfulUpwardEnumerableLT α`): Fin 2 with < always false: 1 ∈ (0<...*).toList = [1], but 1 ∉ 0<...*.
theorem t13 : ¬ drop0% Std.Roi.mem_toList_iff_mem 6 := fun h => by
  letI : LT (Fin 2) := ⟨fun _ _ => False⟩
  have := @h (Fin 2) ⟨0⟩ _ _ _ _ 1
  rw [tl_roi02] at this; exact this.1 (by simp)

-- `Std.Roi.mem_toArray_iff_mem` (hypothesis 6: `Std.PRange.LawfulUpwardEnumerableLT α`): Fin 2 with < always false: 1 ∈ (0<...*).toArray = #[1], but 1 ∉ 0<...*.
theorem t14 : ¬ drop0% Std.Roi.mem_toArray_iff_mem 6 := fun h => by
  letI : LT (Fin 2) := ⟨fun _ _ => False⟩
  have := @h (Fin 2) ⟨0⟩ _ _ _ _ 1
  rw [← Roi.toArray_toList, tl_roi02] at this; exact this.1 (by simp)

-- `Std.Roi.pairwise_toList_lt` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerableLT α`): Fin 3 with < always false: (0<...*).toList = [1, 2].
theorem t15 : ¬ drop0% Std.Roi.pairwise_toList_lt 5 := fun h => by
  letI : LT (Fin 3) := ⟨fun _ _ => False⟩
  have := @h (Fin 3) ⟨0⟩ _ _ _ _
  rw [tl_roi03] at this; exact List.rel_of_pairwise_cons this (List.mem_singleton_self 2)

-- `Std.Roi.pairwise_toList_le` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerableLE α`): Fin 3 with ≤ always false: (0<...*).toList = [1, 2].
theorem t16 : ¬ drop0% Std.Roi.pairwise_toList_le 5 := fun h => by
  letI : LE (Fin 3) := ⟨fun _ _ => False⟩
  have := @h (Fin 3) ⟨0⟩ _ _ _ _
  rw [tl_roi03] at this; exact List.rel_of_pairwise_cons this (List.mem_singleton_self 2)

-- `Std.Rci.isEmpty_iff_forall_not_mem` (hypothesis 6: `Std.PRange.LawfulUpwardEnumerableLE α`): Fin 2 with ≤ always false: 0...* has no members, but isEmpty = false.
theorem t17 : ¬ drop0% Std.Rci.isEmpty_iff_forall_not_mem 6 := fun h => by
  letI : LE (Fin 2) := ⟨fun _ _ => False⟩
  exact absurd ((@h (Fin 2) ⟨0⟩ _ _ _ _ _ _).2 (fun _ h => h)) (by decide)

-- `Std.Rci.isEmpty_iff_forall_not_mem` (hypothesis 8: `Std.PRange.LawfulUpwardEnumerable α`): UNone (one element, succMany? = none, ≤ always false, lawful size 1): no members, but isEmpty = false.
theorem t18 : ¬ drop0% Std.Rci.isEmpty_iff_forall_not_mem 8 := fun h =>
  absurd ((@h UNone ⟨⟨⟩⟩ _ _ _ _ _ _).2 (fun _ h => h)) (by decide)

-- `Std.Roi.isEmpty_iff_forall_not_mem` (hypothesis 7: `Std.PRange.LawfulUpwardEnumerableLT α`): Fin 2 with < always false: 0<...* has no members, but succ? 0 = some 1, so isEmpty = false.
theorem t19 : ¬ drop0% Std.Roi.isEmpty_iff_forall_not_mem 7 := fun h => by
  letI : LT (Fin 2) := ⟨fun _ _ => False⟩
  letI : DecidableLT (Fin 2) := fun _ _ => instDecidableFalse
  exact absurd ((@h (Fin 2) ⟨0⟩ _ _ _ _ _ _ _).2 (fun _ h => h)) (by decide)

-- `Std.Roi.isEmpty_iff_forall_not_mem` (hypothesis 9: `Std.PRange.LawfulUpwardEnumerable α`): S3, r = 1<...*: succ? 1 = none, so isEmpty, but 1 < 2.
theorem t20 : ¬ drop0% Std.Roi.isEmpty_iff_forall_not_mem 9 := fun h =>
  (@h S3 ⟨⟨1⟩⟩ _ _ _ _ _ _ _).1 rfl ⟨2⟩ (by decide)

end RangeNdBHand

namespace RangeNdBHand
open Std Std.PRange

/-! ### `LawfulMonad` dropped: the bind-counting monad `CM`

`CM α := Nat × α`, `pure a = (0, a)`, `bind` adds `1` to the counts (not lawful: `pure a >>= f ≠ f a`).
A range loop runs `f a h c >>= fun s => pure ⟨s, trivial⟩` and then matches on the result (two
binds), while `List.forIn'`, `Array.forIn'` and the `match` forms bind `f`'s result once. With
`f = fun _ _ c => pure (.done c)` the counts differ (2 vs 1). The range loop is unfolded once by
`loop_unfold`. -/

def CM (α : Type) := Nat × α
instance : Monad CM where
  pure a := (0, a)
  bind x f := ((f x.2).1 + x.1 + 1, (f x.2).2)

theorem succ?_fin0 : succ? (0 : Fin 2) = some 1 := rfl

-- Unfold a range `forIn'` over `Fin 2` once (its loop is `WellFounded.extrinsicFix₃`, which is
-- `WellFounded.fix` for the finite range iterator), for any monad.
macro "loop_unfold" : tactic => `(tactic| focus
  simp only [ForIn'.forIn', IteratorLoop.forIn, Rci.Internal.iter, Roi.Internal.iter,
    Rii.Internal.iter, Iter.toIterM, succ?_fin0, Fin.least?_eq, Rxi.Iterator.instIteratorLoop.loop]
  rw [WellFounded.extrinsicFix₃_eq_fix (InvImage.wf _ IteratorLoop.wellFounded_of_finite),
    WellFounded.fix_eq])

-- `Std.Rci.forIn'_eq_forIn'_toList` (hypothesis 11: `LawfulMonad m`): CM (bind-counting monad), Fin 2, f returns .done at once: the range loop counts 2 binds, List.forIn' over (0...*).toList = [0, 1] counts 1.
theorem lm0 : ¬ drop0% Std.Rci.forIn'_eq_forIn'_toList 11 := fun h => by
  have := @h (Fin 2) ⟨0⟩ _ _ _ _ _ Nat 0 CM _ (fun _ _ c => pure (.done c))
  revert this; rw [tl_rci02]; loop_unfold
  intro e; exact absurd (congrArg (α := Nat × Nat) Prod.fst e) (by decide)

-- `Std.Rci.forIn'_eq_forIn'_toArray` (hypothesis 11: `LawfulMonad m`): CM (bind-counting monad), Fin 2, f returns .done at once: the range loop counts 2 binds, Array.forIn' over #[0, 1] counts 1.
theorem lm1 : ¬ drop0% Std.Rci.forIn'_eq_forIn'_toArray 11 := fun h => by
  have := @h (Fin 2) ⟨0⟩ _ _ _ _ _ Nat 0 CM _ (fun _ _ c => pure (.done c))
  revert this; rw [← Rci.toArray_toList, tl_rci02]; loop_unfold
  intro e; exact absurd (congrArg (α := Nat × Nat) Prod.fst e) (by decide)

-- `Std.Rci.forIn'_toList_eq_forIn'` (hypothesis 11: `LawfulMonad m`): CM (bind-counting monad), Fin 2, f returns .done at once: the range loop counts 2 binds, List.forIn' over (0...*).toList = [0, 1] counts 1.
theorem lm2 : ¬ drop0% Std.Rci.forIn'_toList_eq_forIn' 11 := fun h => by
  have := @h (Fin 2) ⟨0⟩ _ _ _ _ _ Nat 0 CM _ (fun _ _ c => pure (.done c))
  revert this; rw [tl_rci02]; loop_unfold
  intro e; exact absurd (congrArg (α := Nat × Nat) Prod.fst e) (by decide)

-- `Std.Rci.forIn'_toArray_eq_forIn'` (hypothesis 11: `LawfulMonad m`): CM (bind-counting monad), Fin 2, f returns .done at once: the range loop counts 2 binds, Array.forIn' over #[0, 1] counts 1.
theorem lm3 : ¬ drop0% Std.Rci.forIn'_toArray_eq_forIn' 11 := fun h => by
  have := @h (Fin 2) ⟨0⟩ _ _ _ _ _ Nat 0 CM _ (fun _ _ c => pure (.done c))
  revert this; rw [← Rci.toArray_toList, tl_rci02]; loop_unfold
  intro e; exact absurd (congrArg (α := Nat × Nat) Prod.fst e) (by decide)

-- `Std.Rci.forIn'_eq_match` (hypothesis 13: `LawfulMonad m`): CM (bind-counting monad), Fin 2, f returns .done at once: the range loop counts 2 binds, the unfolded right side (f 0 bound once) counts 1.
theorem lm4 : ¬ drop0% Std.Rci.forIn'_eq_match 13 := fun h => by
  have := @h (Fin 2) ⟨0⟩ _ _ _ _ _ _ _ _ _ CM _ Nat 0 (fun _ _ c => pure (.done c))
  revert this; loop_unfold
  intro e; exact absurd (congrArg (α := Nat × Nat) Prod.fst e) (by decide)

-- `Std.Roi.forIn'_eq_forIn'_toList` (hypothesis 11: `LawfulMonad m`): CM (bind-counting monad), Fin 2, f returns .done at once: the range loop counts 2 binds, List.forIn' over (0<...*).toList = [1] counts 1.
theorem lm5 : ¬ drop0% Std.Roi.forIn'_eq_forIn'_toList 11 := fun h => by
  have := @h (Fin 2) ⟨0⟩ _ _ _ _ _ Nat 0 CM _ (fun _ _ c => pure (.done c))
  revert this; rw [tl_roi02]; loop_unfold
  intro e; exact absurd (congrArg (α := Nat × Nat) Prod.fst e) (by decide)

-- `Std.Roi.forIn'_eq_forIn'_toArray` (hypothesis 11: `LawfulMonad m`): CM (bind-counting monad), Fin 2, f returns .done at once: the range loop counts 2 binds, Array.forIn' over #[1] counts 1.
theorem lm6 : ¬ drop0% Std.Roi.forIn'_eq_forIn'_toArray 11 := fun h => by
  have := @h (Fin 2) ⟨0⟩ _ _ _ _ _ Nat 0 CM _ (fun _ _ c => pure (.done c))
  revert this; rw [← Roi.toArray_toList, tl_roi02]; loop_unfold
  intro e; exact absurd (congrArg (α := Nat × Nat) Prod.fst e) (by decide)

-- `Std.Roi.forIn'_toList_eq_forIn'` (hypothesis 12: `LawfulMonad m`): CM (bind-counting monad), Fin 2, f returns .done at once: the range loop counts 2 binds, List.forIn' over (0<...*).toList = [1] counts 1.
theorem lm7 : ¬ drop0% Std.Roi.forIn'_toList_eq_forIn' 12 := fun h => by
  have := @h (Fin 2) ⟨0⟩ _ _ _ _ _ _ Nat 0 CM _ (fun _ _ c => pure (.done c))
  revert this; rw [tl_roi02]; loop_unfold
  intro e; exact absurd (congrArg (α := Nat × Nat) Prod.fst e) (by decide)

-- `Std.Roi.forIn'_toArray_eq_forIn'` (hypothesis 12: `LawfulMonad m`): CM (bind-counting monad), Fin 2, f returns .done at once: the range loop counts 2 binds, Array.forIn' over #[1] counts 1.
theorem lm8 : ¬ drop0% Std.Roi.forIn'_toArray_eq_forIn' 12 := fun h => by
  have := @h (Fin 2) ⟨0⟩ _ _ _ _ _ _ Nat 0 CM _ (fun _ _ c => pure (.done c))
  revert this; rw [← Roi.toArray_toList, tl_roi02]; loop_unfold
  intro e; exact absurd (congrArg (α := Nat × Nat) Prod.fst e) (by decide)

-- `Std.Roi.forIn'_eq_match` (hypothesis 10: `LawfulMonad m`): CM (bind-counting monad), Fin 2, f returns .done at once: the range loop counts 2 binds, the unfolded right side (f 1 bound once) counts 1.
theorem lm9 : ¬ drop0% Std.Roi.forIn'_eq_match 10 := fun h => by
  have := @h (Fin 2) ⟨0⟩ _ _ _ _ _ _ CM _ Nat 0 (fun _ _ c => pure (.done c))
  revert this; loop_unfold
  intro e; exact absurd (congrArg (α := Nat × Nat) Prod.fst e) (by decide)

-- `Std.Rii.forIn'_eq_forIn'_toList` (hypothesis 11: `LawfulMonad m`): CM (bind-counting monad), Fin 2, f returns .done at once: the range loop counts 2 binds, List.forIn' over (*...*).toList = [0, 1] counts 1.
theorem lm10 : ¬ drop0% Std.Rii.forIn'_eq_forIn'_toList 11 := fun h => by
  have := @h (Fin 2) ⟨⟩ _ _ _ _ _ Nat 0 CM _ (fun _ _ c => pure (.done c))
  revert this; rw [tl_rii2]; loop_unfold
  intro e; exact absurd (congrArg (α := Nat × Nat) Prod.fst e) (by decide)

-- `Std.Rii.forIn'_eq_forIn'_toArray` (hypothesis 11: `LawfulMonad m`): CM (bind-counting monad), Fin 2, f returns .done at once: the range loop counts 2 binds, Array.forIn' over #[0, 1] counts 1.
theorem lm11 : ¬ drop0% Std.Rii.forIn'_eq_forIn'_toArray 11 := fun h => by
  have := @h (Fin 2) ⟨⟩ _ _ _ _ _ Nat 0 CM _ (fun _ _ c => pure (.done c))
  revert this; rw [← Rii.toArray_toList, tl_rii2]; loop_unfold
  intro e; exact absurd (congrArg (α := Nat × Nat) Prod.fst e) (by decide)

-- `Std.Rii.forIn'_toList_eq_forIn'` (hypothesis 13: `LawfulMonad m`): CM (bind-counting monad), Fin 2, f returns .done at once: the range loop counts 2 binds, List.forIn' over (*...*).toList = [0, 1] counts 1.
theorem lm12 : ¬ drop0% Std.Rii.forIn'_toList_eq_forIn' 13 := fun h => by
  have := @h (Fin 2) ⟨⟩ _ _ _ _ _ _ _ Nat 0 CM _ (fun _ _ c => pure (.done c))
  revert this; rw [tl_rii2]; loop_unfold
  intro e; exact absurd (congrArg (α := Nat × Nat) Prod.fst e) (by decide)

-- `Std.Rii.forIn'_toArray_eq_forIn'` (hypothesis 13: `LawfulMonad m`): CM (bind-counting monad), Fin 2, f returns .done at once: the range loop counts 2 binds, Array.forIn' over #[0, 1] counts 1.
theorem lm13 : ¬ drop0% Std.Rii.forIn'_toArray_eq_forIn' 13 := fun h => by
  have := @h (Fin 2) ⟨⟩ _ _ _ _ _ _ _ Nat 0 CM _ (fun _ _ c => pure (.done c))
  revert this; rw [← Rii.toArray_toList, tl_rii2]; loop_unfold
  intro e; exact absurd (congrArg (α := Nat × Nat) Prod.fst e) (by decide)

-- `Std.Rii.forIn'_eq_match_roi` (hypothesis 12: `LawfulMonad m`): CM (bind-counting monad), Fin 2, f returns .done at once: the range loop counts 2 binds, the unfolded right side (f 0 bound once) counts 1.
theorem lm14 : ¬ drop0% Std.Rii.forIn'_eq_match_roi 12 := fun h => by
  have := @h (Fin 2) ⟨⟩ trivial _ _ _ _ _ _ _ CM _ Nat 0 (fun _ _ c => pure (.done c))
  revert this; loop_unfold
  intro e; exact absurd (congrArg (α := Nat × Nat) Prod.fst e) (by decide)

-- `Std.Rii.forIn'_eq_match_rci` (hypothesis 11: `LawfulMonad m`): removable; for least? = none both sides are pure init, and for least? = some a both sides are the same Rxi iterator loop from a, so they agree definitionally for every monad.
theorem lmr : drop% Std.Rii.forIn'_eq_match_rci 11 := by
  intro α r _ hl _ _ _ _ _ m _ γ init f
  rcases hl with ⟨_ | next⟩ <;> rfl

/-! ### `forIn'_congr` without `init = init'` or without the pointwise equation (`Id`, `Fin 2`) -/
-- `Std.Rci.forIn'_congr` (hypothesis 16: `init = init'`): Id, Fin 2, f = f' returning .done at once: the loops return init = 0 and init' = 1.
theorem cg0 : ¬ drop0% Std.Rci.forIn'_congr 16 := fun h => by
  have := @h (Fin 2) _ _ _ _ _ Id _ Nat 0 1 ⟨0⟩ ⟨0⟩ (fun _ _ c => pure (.done c))
    (fun _ _ c => pure (.done c)) rfl (fun _ _ _ => rfl)
  rw [Rci.forIn'_eq_forIn'_toList, Rci.forIn'_eq_forIn'_toList, tl_rci02] at this
  exact absurd (show (0 : Nat) = 1 from this) (by decide)

-- `Std.Rci.forIn'_congr` (hypothesis 17: `∀ (a : α) (m_1 : a ∈ r') (b : γ), f a ⋯ b = f' a m_1 b`): Id, Fin 2, init = init' = 0, f returns .done 0 and f' returns .done 1 at once.
theorem cg1 : ¬ drop0% Std.Rci.forIn'_congr 17 := fun h => by
  have := @h (Fin 2) _ _ _ _ _ Id _ Nat 0 0 ⟨0⟩ ⟨0⟩ (fun _ _ _ => pure (.done 0))
    (fun _ _ _ => pure (.done 1)) rfl rfl
  rw [Rci.forIn'_eq_forIn'_toList, Rci.forIn'_eq_forIn'_toList, tl_rci02] at this
  exact absurd (show (0 : Nat) = 1 from this) (by decide)

-- `Std.Roi.forIn'_congr` (hypothesis 16: `init = init'`): Id, Fin 2, f = f' returning .done at once: the loops return init = 0 and init' = 1.
theorem cg2 : ¬ drop0% Std.Roi.forIn'_congr 16 := fun h => by
  have := @h (Fin 2) _ _ _ _ _ Id _ Nat 0 1 ⟨0⟩ ⟨0⟩ (fun _ _ c => pure (.done c))
    (fun _ _ c => pure (.done c)) rfl (fun _ _ _ => rfl)
  rw [Roi.forIn'_eq_forIn'_toList, Roi.forIn'_eq_forIn'_toList, tl_roi02] at this
  exact absurd (show (0 : Nat) = 1 from this) (by decide)

-- `Std.Roi.forIn'_congr` (hypothesis 17: `∀ (a : α) (m_1 : a ∈ r') (b : γ), f a ⋯ b = f' a m_1 b`): Id, Fin 2, init = init' = 0, f returns .done 0 and f' returns .done 1 at once.
theorem cg3 : ¬ drop0% Std.Roi.forIn'_congr 17 := fun h => by
  have := @h (Fin 2) _ _ _ _ _ Id _ Nat 0 0 ⟨0⟩ ⟨0⟩ (fun _ _ _ => pure (.done 0))
    (fun _ _ _ => pure (.done 1)) rfl rfl
  rw [Roi.forIn'_eq_forIn'_toList, Roi.forIn'_eq_forIn'_toList, tl_roi02] at this
  exact absurd (show (0 : Nat) = 1 from this) (by decide)

-- `Std.Rii.forIn'_congr` (hypothesis 16: `init = init'`): Id, Fin 2, f = f' returning .done at once: the loops return init = 0 and init' = 1.
theorem cg4 : ¬ drop0% Std.Rii.forIn'_congr 16 := fun h => by
  have := @h (Fin 2) _ _ _ _ _ Id _ Nat 0 1 ⟨⟩ ⟨⟩ (fun _ _ c => pure (.done c))
    (fun _ _ c => pure (.done c)) rfl (fun _ _ _ => rfl)
  rw [Rii.forIn'_eq_forIn'_toList, Rii.forIn'_eq_forIn'_toList, tl_rii2] at this
  exact absurd (show (0 : Nat) = 1 from this) (by decide)

-- `Std.Rii.forIn'_congr` (hypothesis 17: `∀ (a : α) (m_1 : a ∈ r') (b : γ), f a ⋯ b = f' a m_1 b`): Id, Fin 2, init = init' = 0, f returns .done 0 and f' returns .done 1 at once.
theorem cg5 : ¬ drop0% Std.Rii.forIn'_congr 17 := fun h => by
  have := @h (Fin 2) _ _ _ _ _ Id _ Nat 0 0 ⟨⟩ ⟨⟩ (fun _ _ _ => pure (.done 0))
    (fun _ _ _ => pure (.done 1)) rfl rfl
  rw [Rii.forIn'_eq_forIn'_toList, Rii.forIn'_eq_forIn'_toList, tl_rii2] at this
  exact absurd (show (0 : Nat) = 1 from this) (by decide)

end RangeNdBHand

namespace RangeNdBHand
open Std Std.PRange

/-! ### `Infinitely` + `Rxi`-finite + lawful: vacuous -/

-- `Std.Rci.mem_succ_iff` (hypothesis 3: `Std.PRange.LinearlyUpwardEnumerable α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v0 : drop% Std.Rci.mem_succ_iff 3 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

-- `Std.Rci.mem_succ_iff` (hypothesis 4: `Std.PRange.LawfulUpwardEnumerableLE α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v1 : drop% Std.Rci.mem_succ_iff 4 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

-- `Std.Rci.succ_mem_succ_succ_iff` (hypothesis 3: `Std.PRange.LinearlyUpwardEnumerable α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v2 : drop% Std.Rci.succ_mem_succ_succ_iff 3 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

-- `Std.Rci.succ_mem_succ_succ_iff` (hypothesis 4: `Std.PRange.LawfulUpwardEnumerableLE α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v3 : drop% Std.Rci.succ_mem_succ_succ_iff 4 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

-- `Std.Rci.toList_succ_succ_eq_map` (hypothesis 4: `Std.PRange.LinearlyUpwardEnumerable α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v4 : drop% Std.Rci.toList_succ_succ_eq_map 4 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

-- `Std.Rci.toList_succ_succ_eq_map` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerableLE α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v5 : drop% Std.Rci.toList_succ_succ_eq_map 5 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

-- `Std.Rci.toArray_succ_succ_eq_map` (hypothesis 4: `Std.PRange.LinearlyUpwardEnumerable α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v6 : drop% Std.Rci.toArray_succ_succ_eq_map 4 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

-- `Std.Rci.toArray_succ_succ_eq_map` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerableLE α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v7 : drop% Std.Rci.toArray_succ_succ_eq_map 5 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

-- `Std.Roi.mem_succ_iff` (hypothesis 3: `Std.PRange.LinearlyUpwardEnumerable α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v8 : drop% Std.Roi.mem_succ_iff 3 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

-- `Std.Roi.mem_succ_iff` (hypothesis 4: `Std.PRange.LawfulUpwardEnumerableLT α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v9 : drop% Std.Roi.mem_succ_iff 4 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

-- `Std.Roi.succ_mem_succ_succ_iff` (hypothesis 3: `Std.PRange.LinearlyUpwardEnumerable α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v10 : drop% Std.Roi.succ_mem_succ_succ_iff 3 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

-- `Std.Roi.succ_mem_succ_succ_iff` (hypothesis 4: `Std.PRange.LawfulUpwardEnumerableLT α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v11 : drop% Std.Roi.succ_mem_succ_succ_iff 4 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

-- `Std.Roi.toList_succ_succ_eq_map` (hypothesis 4: `Std.PRange.LinearlyUpwardEnumerable α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v12 : drop% Std.Roi.toList_succ_succ_eq_map 4 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

-- `Std.Roi.toList_succ_succ_eq_map` (hypothesis 8: `Std.PRange.LawfulUpwardEnumerableLT α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v13 : drop% Std.Roi.toList_succ_succ_eq_map 8 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

-- `Std.Roi.toArray_succ_succ_eq_map` (hypothesis 4: `Std.PRange.LinearlyUpwardEnumerable α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v14 : drop% Std.Roi.toArray_succ_succ_eq_map 4 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

-- `Std.Roi.toArray_succ_succ_eq_map` (hypothesis 8: `Std.PRange.LawfulUpwardEnumerableLT α`): removable; the remaining InfinitelyUpwardEnumerable + Rxi.IsAlwaysFinite + LawfulUpwardEnumerable force α to be empty (false_of_inf_rxi_lue), so the statement is vacuous.
theorem v15 : drop% Std.Roi.toArray_succ_succ_eq_map 8 := by
  intro α; intros; exact (false_of_inf_rxi_lue (α := α) ‹α›).elim

/-! ### `Skip` (non-transitive `≤`, not preserved by `succ`) -/

-- `Std.Rci.mem_succ_iff` (hypothesis 7: `Std.PRange.LawfulUpwardEnumerable α`): Skip, lo = 1, a = 3: ¬ 2 ≤ 3, but 3 = succ 2 and 1 ≤ 2.
theorem s0 : ¬ drop0% Std.Rci.mem_succ_iff 7 := fun h => by
  have := (@h Skip _ _ _ _ _ _ ⟨1⟩ ⟨3⟩).2 ⟨⟨2⟩, rfl, by decide⟩
  revert this; decide

-- `Std.Rci.succ_mem_succ_succ_iff` (hypothesis 7: `Std.PRange.LawfulUpwardEnumerable α`): Skip, lo = 1, a = 2: 1 ≤ 2, but ¬ succ 1 ≤ succ 2.
theorem s1 : ¬ drop0% Std.Rci.succ_mem_succ_succ_iff 7 := fun h => by
  have := (@h Skip _ _ _ _ _ _ ⟨1⟩ ⟨2⟩).2 (by decide)
  revert this; decide

-- `Std.Roi.mem_succ_iff` (hypothesis 7: `Std.PRange.LawfulUpwardEnumerable α`): Skip, lo = 1, a = 3: ¬ 2 < 3, but 3 = succ 2 and 1 < 2.
theorem s2 : ¬ drop0% Std.Roi.mem_succ_iff 7 := fun h => by
  have := (@h Skip _ _ _ _ _ _ ⟨1⟩ ⟨3⟩).2 ⟨⟨2⟩, rfl, by decide⟩
  revert this; decide

-- `Std.Roi.succ_mem_succ_succ_iff` (hypothesis 7: `Std.PRange.LawfulUpwardEnumerable α`): Skip, lo = 1, a = 2: 1 < 2, but ¬ succ 1 < succ 2.
theorem s3 : ¬ drop0% Std.Roi.succ_mem_succ_succ_iff 7 := fun h => by
  have := (@h Skip _ _ _ _ _ _ ⟨1⟩ ⟨2⟩).2 (by decide)
  revert this; decide

-- `Std.Rci.mem_of_mem_roi` (hypothesis 8: `Std.PRange.LawfulUpwardEnumerable α`): Skip, r = 0...*, b = 1, a = 2: 0 ≤ 1 and 1 < 2, but ¬ 0 ≤ 2.
theorem s4 : ¬ drop0% Std.Rci.mem_of_mem_roi 8 := fun h => by
  have := @h Skip ⟨⟨0⟩⟩ _ _ _ _ _ _ ⟨2⟩ ⟨1⟩ (by decide) (by decide)
  revert this; decide

-- `Std.Roi.mem_of_mem_of_le` (hypothesis 6: `Std.PRange.LawfulUpwardEnumerable α`): Skip, r = 0<...*, b = 1, a = 2: UpwardEnumerable.LE 0 1 and 1 < 2, but ¬ 0 < 2.
theorem s5 : ¬ drop0% Std.Roi.mem_of_mem_of_le 6 := fun h => by
  have := @h Skip ⟨⟨0⟩⟩ _ _ _ _ ⟨2⟩ ⟨1⟩ ⟨1, rfl⟩ (by decide)
  revert this; decide

/-! ### `mem_of_mem_roi`, `mem_of_mem_of_le` with `Fin n` -/

-- `Std.Rci.mem_of_mem_roi` (hypothesis 5: `Std.PRange.LawfulUpwardEnumerableLE α`): Fin 2 with a ≤ b :↔ b = 0, r = 0...*, b = 0, a = 1: 0 ≤ 0 and 0 < 1, but ¬ 0 ≤ 1.
theorem m0 : ¬ drop0% Std.Rci.mem_of_mem_roi 5 := fun h => by
  letI : LE (Fin 2) := ⟨fun _ b => b = 0⟩
  exact absurd (show (1 : Fin 2) = 0 from @h (Fin 2) ⟨0⟩ _ _ _ _ _ _ 1 0 rfl (by decide)) (by decide)

-- `Std.Rci.mem_of_mem_roi` (hypothesis 6: `Std.PRange.LawfulUpwardEnumerableLT α`): Fin 2 with < always true, r = 1...*, b = 1, a = 0: 1 ≤ 1 and 1 < 0, but ¬ 1 ≤ 0.
theorem m1 : ¬ drop0% Std.Rci.mem_of_mem_roi 6 := fun h => by
  letI : LT (Fin 2) := ⟨fun _ _ => True⟩
  exact absurd (show (1 : Fin 2) ≤ 0 from @h (Fin 2) ⟨1⟩ _ _ _ _ _ _ 0 1 (by decide) trivial) (by decide)

-- `Std.Rci.mem_of_mem_roi` (hypothesis 11: `r.lower ≤ b`): Fin 3, r = 2...*, b = 0, a = 1: 0 < 1, but ¬ 2 ≤ 1.
theorem m2 : ¬ drop0% Std.Rci.mem_of_mem_roi 11 := fun h =>
  absurd (show (2 : Fin 3) ≤ 1 from @h (Fin 3) ⟨2⟩ _ _ _ _ _ _ _ 1 0 (by decide)) (by decide)

-- `Std.Rci.mem_of_mem_roi` (hypothesis 12: `a ∈ b<...*`): Fin 2, r = 1...*, b = 1, a = 0: 1 ≤ 1, but ¬ 1 ≤ 0.
theorem m3 : ¬ drop0% Std.Rci.mem_of_mem_roi 12 := fun h =>
  absurd (show (1 : Fin 2) ≤ 0 from @h (Fin 2) ⟨1⟩ _ _ _ _ _ _ _ 0 1 (by decide)) (by decide)

-- `Std.Roi.mem_of_mem_of_le` (hypothesis 4: `Std.PRange.LawfulUpwardEnumerableLT α`): Fin 2 with a < b :↔ a = 1, r = 0<...*, b = 1, a = 0: UpwardEnumerable.LE 0 1 and 1 < 0, but ¬ 0 < 0.
theorem m4 : ¬ drop0% Std.Roi.mem_of_mem_of_le 4 := fun h => by
  letI : LT (Fin 2) := ⟨fun a _ => a = 1⟩
  exact absurd (show (0 : Fin 2) = 1 from @h (Fin 2) ⟨0⟩ _ _ _ _ 0 1 ⟨1, rfl⟩ rfl) (by decide)

-- `Std.Roi.mem_of_mem_of_le` (hypothesis 9: `Std.PRange.UpwardEnumerable.LE r.lower b`): Fin 2, r = 1<...*, b = 0, a = 1: 0 < 1, but ¬ 1 < 1.
theorem m5 : ¬ drop0% Std.Roi.mem_of_mem_of_le 9 := fun h =>
  absurd (show (1 : Fin 2) < 1 from @h (Fin 2) ⟨1⟩ _ _ _ _ _ 1 0 (by decide)) (by decide)

-- `Std.Roi.mem_of_mem_of_le` (hypothesis 10: `a ∈ b<...*`): Fin 2, r = 0<...*, b = 0, a = 0: UpwardEnumerable.LE 0 0, but ¬ 0 < 0.
theorem m6 : ¬ drop0% Std.Roi.mem_of_mem_of_le 10 := fun h =>
  absurd (show (0 : Fin 2) < 0 from @h (Fin 2) ⟨0⟩ _ _ _ _ _ 0 0 ⟨0, rfl⟩) (by decide)

/-! ### `Rxi.LawfulHasSize` dropped: `Fin 2` with the constant size `5` -/

-- `Std.Rci.size_eq_size_roi` (hypothesis 6: `Std.Rxi.LawfulHasSize α`): Fin 2 with size = 5: 5 ≠ 5 + 1.
theorem z0 : ¬ drop0% Std.Rci.size_eq_size_roi 6 := fun h => by
  letI : Rxi.HasSize (Fin 2) := ⟨fun _ => 5⟩
  exact absurd (@h (Fin 2) ⟨0⟩ _ _ _ _) (by decide)

-- `Std.Rci.size_eq_match_rci` (hypothesis 6: `Std.Rxi.LawfulHasSize α`): Fin 2 with size = 5, r = 1...*: 5 ≠ 1 (succ? 1 = none).
theorem z1 : ¬ drop0% Std.Rci.size_eq_match_rci 6 := fun h => by
  letI : Rxi.HasSize (Fin 2) := ⟨fun _ => 5⟩
  exact absurd (@h (Fin 2) ⟨1⟩ _ _ _ _) (by decide)

-- `Std.Rci.length_toList` (hypothesis 6: `Std.Rxi.LawfulHasSize α`): Fin 2 with size = 5: (0...*).toList = [0, 1] has length 2.
theorem z2 : ¬ drop0% Std.Rci.length_toList 6 := fun h => by
  letI : Rxi.HasSize (Fin 2) := ⟨fun _ => 5⟩
  have := @h (Fin 2) ⟨0⟩ _ _ _ _
  rw [tl_rci02] at this; exact absurd this (by decide)

-- `Std.Rci.size_toArray` (hypothesis 6: `Std.Rxi.LawfulHasSize α`): Fin 2 with size = 5: (0...*).toArray = #[0, 1] has size 2.
theorem z3 : ¬ drop0% Std.Rci.size_toArray 6 := fun h => by
  letI : Rxi.HasSize (Fin 2) := ⟨fun _ => 5⟩
  have := @h (Fin 2) ⟨0⟩ _ _ _ _
  rw [← Rci.toArray_toList, tl_rci02] at this; exact absurd this (by decide)

-- `Std.Roi.size_eq_match_roi` (hypothesis 6: `Std.Rxi.LawfulHasSize α`): Fin 2 with size = 5, r = 0<...*: 5 ≠ (1<...*).size + 1 = 1.
theorem z4 : ¬ drop0% Std.Roi.size_eq_match_roi 6 := fun h => by
  letI : Rxi.HasSize (Fin 2) := ⟨fun _ => 5⟩
  exact absurd (@h (Fin 2) ⟨0⟩ _ _ _ _) (by decide)

-- `Std.Roi.length_toList` (hypothesis 6: `Std.Rxi.LawfulHasSize α`): Fin 2 with size = 5: (0<...*).toList = [1] has length 1.
theorem z5 : ¬ drop0% Std.Roi.length_toList 6 := fun h => by
  letI : Rxi.HasSize (Fin 2) := ⟨fun _ => 5⟩
  have := @h (Fin 2) ⟨0⟩ _ _ _ _
  rw [tl_roi02] at this; exact absurd this (by decide)

-- `Std.Roi.size_toArray` (hypothesis 6: `Std.Rxi.LawfulHasSize α`): Fin 2 with size = 5: (0<...*).toArray = #[1] has size 1.
theorem z6 : ¬ drop0% Std.Roi.size_toArray 6 := fun h => by
  letI : Rxi.HasSize (Fin 2) := ⟨fun _ => 5⟩
  have := @h (Fin 2) ⟨0⟩ _ _ _ _
  rw [← Roi.toArray_toList, tl_roi02] at this; exact absurd this (by decide)

-- `Std.Rii.size_eq_match_roi` (hypothesis 7: `Std.Rxi.LawfulHasSize α`): Fin 2 with size = 5: 5 ≠ (0<...*).size + 1 = 6.
theorem z7 : ¬ drop0% Std.Rii.size_eq_match_roi 7 := fun h => by
  letI : Rxi.HasSize (Fin 2) := ⟨fun _ => 5⟩
  exact absurd (@h (Fin 2) ⟨⟩ _ _ _ _ _) (by decide)

-- `Std.Rii.length_toList` (hypothesis 7: `Std.Rxi.LawfulHasSize α`): Fin 2 with size = 5: (*...*).toList = [0, 1] has length 2.
theorem z8 : ¬ drop0% Std.Rii.length_toList 7 := fun h => by
  letI : Rxi.HasSize (Fin 2) := ⟨fun _ => 5⟩
  have := @h (Fin 2) ⟨⟩ _ _ _ _ _
  rw [tl_rii2] at this; exact absurd this (by decide)

-- `Std.Rii.size_toArray` (hypothesis 7: `Std.Rxi.LawfulHasSize α`): Fin 2 with size = 5: (*...*).toArray = #[0, 1] has size 2.
theorem z9 : ¬ drop0% Std.Rii.size_toArray 7 := fun h => by
  letI : Rxi.HasSize (Fin 2) := ⟨fun _ => 5⟩
  have := @h (Fin 2) ⟨⟩ _ _ _ _ _
  rw [← Rii.toArray_toList, tl_rii2] at this; exact absurd this (by decide)

/-! ### `isSome_succMany?_of_lt_*` without the bound -/

-- `Std.Rci.isSome_succMany?_of_lt_length_toList` (hypothesis 9: `i < r.toList.length`): Fin 2, r = 0...*, i = 5: succMany? 5 0 = none.
theorem q0 : ¬ drop0% Std.Rci.isSome_succMany?_of_lt_length_toList 9 := fun h =>
  absurd (@h (Fin 2) ⟨0⟩ _ _ _ _ _ _ 5) (by decide)

-- `Std.Rci.isSome_succMany?_of_lt_size_toArray` (hypothesis 9: `i < r.toArray.size`): Fin 2, r = 0...*, i = 5: succMany? 5 0 = none.
theorem q1 : ¬ drop0% Std.Rci.isSome_succMany?_of_lt_size_toArray 9 := fun h =>
  absurd (@h (Fin 2) ⟨0⟩ _ _ _ _ _ _ 5) (by decide)

-- `Std.Roi.isSome_succMany?_of_lt_length_toList` (hypothesis 9: `i < r.toList.length`): Fin 2, r = 0<...*, i = 5: succMany? 6 0 = none.
theorem q2 : ¬ drop0% Std.Roi.isSome_succMany?_of_lt_length_toList 9 := fun h =>
  absurd (@h (Fin 2) ⟨0⟩ _ _ _ _ _ _ 5) (by decide)

-- `Std.Roi.isSome_succMany?_of_lt_size_toArray` (hypothesis 9: `i < r.toArray.size`): Fin 2, r = 0<...*, i = 5: succMany? 6 0 = none.
theorem q3 : ¬ drop0% Std.Roi.isSome_succMany?_of_lt_size_toArray 9 := fun h =>
  absurd (@h (Fin 2) ⟨0⟩ _ _ _ _ _ _ 5) (by decide)

-- `Std.Rii.isSome_succMany?_of_lt_length_toList` (hypothesis 8: `i < r.toList.length`): Fin 2, i = 5: succMany? 5 0 = none.
theorem q4 : ¬ drop0% Std.Rii.isSome_succMany?_of_lt_length_toList 8 := fun h =>
  absurd (@h (Fin 2) ⟨⟩ _ _ _ _ _ 5) (by decide)

-- `Std.Rii.isSome_succMany?_of_lt_size_toArray` (hypothesis 8: `i < r.toArray.size`): Fin 2, i = 5: succMany? 5 0 = none.
theorem q5 : ¬ drop0% Std.Rii.isSome_succMany?_of_lt_size_toArray 8 := fun h =>
  absurd (@h (Fin 2) ⟨⟩ _ _ _ _ _ 5) (by decide)

/-! ### `Polymorphic/PRange.lean`: class projections without the class -/

-- `Std.Rxc.IsAlwaysFinite.finite` (hypothesis 3: `Std.Rxc.IsAlwaysFinite α`): Loop1 (one element, succMany? = some, ≤ always true): no successor is ever beyond the bound.
theorem p0 : ¬ drop0% Std.Rxc.IsAlwaysFinite.finite 3 := fun h => by
  obtain ⟨n, hn⟩ := @h Loop1 inferInstance inferInstance ⟨⟩ ⟨⟩; exact (show ¬ ((⟨⟩ : Loop1) ≤ ⟨⟩) from hn) trivial

-- `Std.Rxo.IsAlwaysFinite.finite` (hypothesis 3: `Std.Rxo.IsAlwaysFinite α`): Loop1 (one element, succMany? = some, < always true): no successor is ever beyond the bound.
theorem p1 : ¬ drop0% Std.Rxo.IsAlwaysFinite.finite 3 := fun h => by
  obtain ⟨n, hn⟩ := @h Loop1 inferInstance inferInstance ⟨⟩ ⟨⟩; exact (show ¬ ((⟨⟩ : Loop1) < ⟨⟩) from hn) trivial

-- `Std.Rxi.IsAlwaysFinite.finite` (hypothesis 2: `Std.Rxi.IsAlwaysFinite α`): Loop1 (one element, succMany? = some): succMany? is never none.
theorem p2 : ¬ drop0% Std.Rxi.IsAlwaysFinite.finite 2 := fun h => by
  obtain ⟨n, hn⟩ := @h Loop1 inferInstance ⟨⟩; exact absurd (show (some ⟨⟩ : Option Loop1) = none from hn) (by simp)

-- `Std.Rcc.LawfulRcoIntersection.mem_intersection_iff` (hypothesis 4: `Std.Rcc.LawfulRcoIntersection α`): Nat with intersection r s := s, r = 5...5, s = 1...<2, a = 1.
theorem p3 : ¬ drop0% Std.Rcc.LawfulRcoIntersection.mem_intersection_iff 4 := fun h =>
  absurd (show 5 ≤ 1 from ((@h Nat inferInstance inferInstance (⟨fun _ s => s⟩ : Rcc.HasRcoIntersection Nat) 1 ⟨5, 5⟩ ⟨1, 2⟩).1 ⟨by decide, by decide⟩).1.1)
    (by decide)

-- `Std.Rco.LawfulRcoIntersection.mem_intersection_iff` (hypothesis 4: `Std.Rco.LawfulRcoIntersection α`): Nat with intersection r s := s, r = 5...<6, s = 1...<2, a = 1.
theorem p4 : ¬ drop0% Std.Rco.LawfulRcoIntersection.mem_intersection_iff 4 := fun h =>
  absurd (show 5 ≤ 1 from ((@h Nat inferInstance inferInstance (⟨fun _ s => s⟩ : Rco.HasRcoIntersection Nat) 1 ⟨5, 6⟩ ⟨1, 2⟩).1 ⟨by decide, by decide⟩).1.1)
    (by decide)

-- `Std.Rci.LawfulRcoIntersection.mem_intersection_iff` (hypothesis 4: `Std.Rci.LawfulRcoIntersection α`): Nat with intersection r s := s, r = 5...*, s = 1...<2, a = 1.
theorem p5 : ¬ drop0% Std.Rci.LawfulRcoIntersection.mem_intersection_iff 4 := fun h =>
  absurd (show 5 ≤ 1 from ((@h Nat inferInstance inferInstance (⟨fun _ s => s⟩ : Rci.HasRcoIntersection Nat) 1 ⟨5⟩ ⟨1, 2⟩).1 ⟨by decide, by decide⟩).1)
    (by decide)

-- `Std.Roc.LawfulRcoIntersection.mem_intersection_iff` (hypothesis 4: `Std.Roc.LawfulRcoIntersection α`): Nat with intersection r s := s, r = 5<...6, s = 1...<2, a = 1.
theorem p6 : ¬ drop0% Std.Roc.LawfulRcoIntersection.mem_intersection_iff 4 := fun h =>
  absurd (show 5 < 1 from ((@h Nat inferInstance inferInstance (⟨fun _ s => s⟩ : Roc.HasRcoIntersection Nat) 1 ⟨5, 6⟩ ⟨1, 2⟩).1 ⟨by decide, by decide⟩).1.1)
    (by decide)

-- `Std.Roo.LawfulRcoIntersection.mem_intersection_iff` (hypothesis 4: `Std.Roo.LawfulRcoIntersection α`): Nat with intersection r s := s, r = 5<...<7, s = 1...<2, a = 1.
theorem p7 : ¬ drop0% Std.Roo.LawfulRcoIntersection.mem_intersection_iff 4 := fun h =>
  absurd (show 5 < 1 from ((@h Nat inferInstance inferInstance (⟨fun _ s => s⟩ : Roo.HasRcoIntersection Nat) 1 ⟨5, 7⟩ ⟨1, 2⟩).1 ⟨by decide, by decide⟩).1.1)
    (by decide)

-- `Std.Roi.LawfulRcoIntersection.mem_intersection_iff` (hypothesis 4: `Std.Roi.LawfulRcoIntersection α`): Nat with intersection r s := s, r = 5<...*, s = 1...<2, a = 1.
theorem p8 : ¬ drop0% Std.Roi.LawfulRcoIntersection.mem_intersection_iff 4 := fun h =>
  absurd (show 5 < 1 from ((@h Nat inferInstance inferInstance (⟨fun _ s => s⟩ : Roi.HasRcoIntersection Nat) 1 ⟨5⟩ ⟨1, 2⟩).1 ⟨by decide, by decide⟩).1)
    (by decide)

-- `Std.Ric.LawfulRcoIntersection.mem_intersection_iff` (hypothesis 4: `Std.Ric.LawfulRcoIntersection α`): Nat with intersection r s := s, r = *...0, s = 1...<2, a = 1.
theorem p9 : ¬ drop0% Std.Ric.LawfulRcoIntersection.mem_intersection_iff 4 := fun h =>
  absurd (show 1 ≤ 0 from ((@h Nat inferInstance inferInstance (⟨fun _ s => s⟩ : Ric.HasRcoIntersection Nat) 1 ⟨0⟩ ⟨1, 2⟩).1 ⟨by decide, by decide⟩).1)
    (by decide)

-- `Std.Rio.LawfulRcoIntersection.mem_intersection_iff` (hypothesis 4: `Std.Rio.LawfulRcoIntersection α`): Nat with intersection r s := s, r = *...<1, s = 1...<2, a = 1.
theorem p10 : ¬ drop0% Std.Rio.LawfulRcoIntersection.mem_intersection_iff 4 := fun h =>
  absurd (show 1 < 1 from ((@h Nat inferInstance inferInstance (⟨fun _ s => s⟩ : Rio.HasRcoIntersection Nat) 1 ⟨1⟩ ⟨1, 2⟩).1 ⟨by decide, by decide⟩).1)
    (by decide)

end RangeNdBHand
