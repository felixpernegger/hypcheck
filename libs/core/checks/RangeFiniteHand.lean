import Lean

/-!
Hand pass `RangeFinite` (hand8): 220 open hypotheses `[Rxc.IsAlwaysFinite α]` resp.
`[Rxo.IsAlwaysFinite α]` of Range theorems that also assume `[LawfulUpwardEnumerable α]` and
`[LawfulUpwardEnumerableLE α]` resp. `[LawfulUpwardEnumerableLT α]`. All are removable, because
finiteness follows from these (`rxc_of_lawful`, `rxo_of_lawful`): if `init ≤ hi`, then `hi` is the
`m`-th successor of `init`; the `(m+1)`-th successor is `none` or some `x` with `¬ x ≤ hi`, since
`x ≤ hi` would make `hi` a proper successor of itself, which `ne_of_lt` forbids.

210 are dependent (`toList`/`toArray`/… take the instance as an argument): the declaration proves
`∀ indep, Hᵢ` (`indep% T i`). 10 are non-dependent: the declaration proves `T'` (`drop% T i`) from `T`.

Run with the lean4 repo's stage1 binary: `lean checks/RangeFiniteHand.lean`.
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

namespace RangeFiniteHand
open Std Std.PRange


theorem rxc_of_lawful {α : Type u} [UpwardEnumerable α] [LE α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] : Rxc.IsAlwaysFinite α where
  finite init hi := by
    by_cases h : init ≤ hi
    · obtain ⟨m, hm⟩ := (LawfulUpwardEnumerableLE.le_iff init hi).1 h
      refine ⟨m + 1, ?_⟩
      rw [LawfulUpwardEnumerable.succMany?_add_one, hm]
      cases hs : UpwardEnumerable.succ? hi with
      | none => simp [hs]
      | some x =>
        simp only [Option.bind_some, hs, Option.elim_some]
        intro hx
        obtain ⟨k, hk⟩ := (LawfulUpwardEnumerableLE.le_iff x hi).1 hx
        apply LawfulUpwardEnumerable.ne_of_lt hi hi _ rfl
        refine ⟨k, ?_⟩
        rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs]; simpa using hk
    · exact ⟨0, by simpa [LawfulUpwardEnumerable.succMany?_zero] using h⟩

theorem rxo_of_lawful {α : Type u} [UpwardEnumerable α] [LT α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] : Rxo.IsAlwaysFinite α where
  finite init hi := by
    by_cases h : init < hi
    · obtain ⟨m, hm⟩ := (LawfulUpwardEnumerableLT.lt_iff init hi).1 h
      refine ⟨m + 1, ?_⟩
      rw [hm]
      intro hx
      exact LawfulUpwardEnumerable.ne_of_lt hi hi ((LawfulUpwardEnumerableLT.lt_iff hi hi).1 hx) rfl
    · exact ⟨0, by simpa [LawfulUpwardEnumerable.succMany?_zero] using h⟩

theorem rxc_of_rxi {α : Type u} [UpwardEnumerable α] [LE α] [Rxi.IsAlwaysFinite α] :
    Rxc.IsAlwaysFinite α where
  finite init hi := by
    obtain ⟨n, hn⟩ := Rxi.IsAlwaysFinite.finite init; exact ⟨n, by simp [hn]⟩

attribute [local instance] rxc_of_lawful rxo_of_lawful

-- `Std.Rxc.Iterator.toList_eq_toList_rxoIterator` (hypothesis 6): removable, the instance is derivable by `rxc_of_lawful`.
theorem d0 : drop% Std.Rxc.Iterator.toList_eq_toList_rxoIterator 6 := by intros; apply Std.Rxc.Iterator.toList_eq_toList_rxoIterator <;> assumption

-- `Std.Rxc.Iterator.toList_eq_toList_rxoIterator` (hypothesis 7): removable, the instance is derivable by `rxo_of_lawful`.
theorem d1 : drop% Std.Rxc.Iterator.toList_eq_toList_rxoIterator 7 := by intros; apply Std.Rxc.Iterator.toList_eq_toList_rxoIterator <;> assumption

-- `Std.Rxc.Iterator.pairwise_toList_upwardEnumerableLt` (hypothesis 6): removable, the instance is derivable by `rxc_of_lawful`.
theorem d2 : drop% Std.Rxc.Iterator.pairwise_toList_upwardEnumerableLt 6 := by intros; apply Std.Rxc.Iterator.pairwise_toList_upwardEnumerableLt <;> assumption

-- `Std.Rxc.Iterator.toList_eq_match` (hypothesis 4): removable, the instance is derivable by `rxc_of_lawful`.
theorem d3 : drop% Std.Rxc.Iterator.toList_eq_match 4 := by intros; apply Std.Rxc.Iterator.toList_eq_match <;> assumption

-- `Std.Rxc.Iterator.toArray_eq_match` (hypothesis 4): removable, the instance is derivable by `rxc_of_lawful`.
theorem d4 : drop% Std.Rxc.Iterator.toArray_eq_match 4 := by intros; apply Std.Rxc.Iterator.toArray_eq_match <;> assumption

-- `Std.Rxo.Iterator.nodup_toList` (hypothesis 4): removable, the instance is derivable by `rxo_of_lawful`.
theorem d5 : drop% Std.Rxo.Iterator.nodup_toList 4 := by intros; apply Std.Rxo.Iterator.nodup_toList <;> assumption

-- `Std.Rxo.Iterator.toList_eq_match` (hypothesis 4): removable, the instance is derivable by `rxo_of_lawful`.
theorem d6 : drop% Std.Rxo.Iterator.toList_eq_match 4 := by intros; apply Std.Rxo.Iterator.toList_eq_match <;> assumption

-- `Std.Rxc.Iterator.nodup_toList` (hypothesis 4): removable, the instance is derivable by `rxc_of_lawful`.
theorem d7 : drop% Std.Rxc.Iterator.nodup_toList 4 := by intros; apply Std.Rxc.Iterator.nodup_toList <;> assumption

-- `Std.Rxo.Iterator.pairwise_toList_upwardEnumerableLt` (hypothesis 6): removable, the instance is derivable by `rxo_of_lawful`.
theorem d8 : drop% Std.Rxo.Iterator.pairwise_toList_upwardEnumerableLt 6 := by intros; apply Std.Rxo.Iterator.pairwise_toList_upwardEnumerableLt <;> assumption

-- `Std.Rxo.Iterator.toArray_eq_match` (hypothesis 4): removable, the instance is derivable by `rxo_of_lawful`.
theorem d9 : drop% Std.Rxo.Iterator.toArray_eq_match 4 := by intros; apply Std.Rxo.Iterator.toArray_eq_match <;> assumption

-- `Std.Rco.forIn'_eq_forIn'_toArray` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d10 : indep% Std.Rco.forIn'_eq_forIn'_toArray 8 := by intros; exact rxo_of_lawful

-- `Std.Ric.forIn'_toList_eq_forIn'` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d11 : indep% Std.Ric.forIn'_toList_eq_forIn' 8 := by intros; exact rxc_of_lawful

-- `Std.Rco.forIn'_toArray_eq_forIn'` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d12 : indep% Std.Rco.forIn'_toArray_eq_forIn' 8 := by intros; exact rxo_of_lawful

-- `Std.Rco.toArray_succ_succ_eq_map` (hypothesis 10, dependent): derivable by `rxo_of_lawful`.
theorem d13 : indep% Std.Rco.toArray_succ_succ_eq_map 10 := by intros; exact rxo_of_lawful

-- `Std.Ric.eq_succMany?_of_toArray_eq_append_append` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d14 : indep% Std.Ric.eq_succMany?_of_toArray_eq_append_append 9 := by intros; exact rxc_of_lawful

-- `Std.Roo.forIn'_eq_match` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d15 : indep% Std.Roo.forIn'_eq_match 6 := by intros; exact rxo_of_lawful

-- `Std.Rio.toList_succ_eq_map` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d16 : indep% Std.Rio.toList_succ_eq_map 8 := by intros; exact rxo_of_lawful

-- `Std.Rcc.eq_succMany?_of_toArray_eq_append_append` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d17 : indep% Std.Rcc.eq_succMany?_of_toArray_eq_append_append 7 := by intros; exact rxc_of_lawful

-- `Std.Rco.eq_succMany?_of_toArray_eq_append_append` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d18 : indep% Std.Rco.eq_succMany?_of_toArray_eq_append_append 7 := by intros; exact rxo_of_lawful

-- `Std.Rcc.ClosedOpen.toList_succ_succ_eq_map` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d19 : indep% Std.Rcc.ClosedOpen.toList_succ_succ_eq_map 7 := by intros; exact rxc_of_lawful

-- `Std.Rco.isSome_succMany?_of_lt_length_toList` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d20 : indep% Std.Rco.isSome_succMany?_of_lt_length_toList 7 := by intros; exact rxo_of_lawful

-- `Std.Rco.size_toArray` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d21 : indep% Std.Rco.size_toArray 8 := by intros; exact rxo_of_lawful

-- `Std.Rio.toList_eq_toList_rco` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d22 : indep% Std.Rio.toList_eq_toList_rco 9 := by intros; exact rxo_of_lawful

-- `Std.Roc.isSome_succMany?_of_lt_size_toArray` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d23 : indep% Std.Roc.isSome_succMany?_of_lt_size_toArray 7 := by intros; exact rxc_of_lawful

-- `Std.Roo.toArray_eq_empty_iff` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d24 : indep% Std.Roo.toArray_eq_empty_iff 8 := by intros; exact rxo_of_lawful

-- `Std.Roo.forIn'_congr` (hypothesis 5, dependent): derivable by `rxo_of_lawful`.
theorem d25 : indep% Std.Roo.forIn'_congr 5 := by intros; exact rxo_of_lawful

-- `Std.Ric.forIn'_eq_if_roc` (hypothesis 10, dependent): derivable by `rxc_of_lawful`.
theorem d26 : indep% Std.Ric.forIn'_eq_if_roc 10 := by intros; exact rxc_of_lawful

-- `Std.Rco.forIn'_eq_ite` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d27 : indep% Std.Rco.forIn'_eq_ite 9 := by intros; exact rxo_of_lawful

-- `Std.Ric.forIn'_toArray_eq_forIn'` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d28 : indep% Std.Ric.forIn'_toArray_eq_forIn' 8 := by intros; exact rxc_of_lawful

-- `Std.Ric.forIn'_eq_forIn'_toList` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d29 : indep% Std.Ric.forIn'_eq_forIn'_toList 8 := by intros; exact rxc_of_lawful

-- `Std.Rio.forIn'_toArray_eq_forIn'` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d30 : indep% Std.Rio.forIn'_toArray_eq_forIn' 8 := by intros; exact rxo_of_lawful

-- `Std.Rco.forIn'_toList_eq_forIn'` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d31 : indep% Std.Rco.forIn'_toList_eq_forIn' 8 := by intros; exact rxo_of_lawful

-- `Std.Rio.forIn'_eq_forIn'_toList` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d32 : indep% Std.Rio.forIn'_eq_forIn'_toList 8 := by intros; exact rxo_of_lawful

-- `Std.Rio.eq_succMany?_of_toArray_eq_append_append` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d33 : indep% Std.Rio.eq_succMany?_of_toArray_eq_append_append 9 := by intros; exact rxo_of_lawful

-- `Std.Rcc.forIn'_toList_eq_forIn'` (hypothesis 6, dependent): derivable by `rxc_of_lawful`.
theorem d34 : indep% Std.Rcc.forIn'_toList_eq_forIn' 6 := by intros; exact rxc_of_lawful

-- `Std.Roo.forIn'_toArray_eq_forIn'` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d35 : indep% Std.Roo.forIn'_toArray_eq_forIn' 6 := by intros; exact rxo_of_lawful

-- `Std.Roo.forIn'_toList_eq_forIn'` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d36 : indep% Std.Roo.forIn'_toList_eq_forIn' 6 := by intros; exact rxo_of_lawful

-- `Std.Ric.isSome_succMany?_of_lt_size_toArray` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d37 : indep% Std.Ric.isSome_succMany?_of_lt_size_toArray 9 := by intros; exact rxc_of_lawful

-- `Std.Rio.getElem_toList_eq` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d38 : indep% Std.Rio.getElem_toList_eq 9 := by intros; exact rxo_of_lawful

-- `Std.Rio.isSome_succMany?_of_lt_size_toArray` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d39 : indep% Std.Rio.isSome_succMany?_of_lt_size_toArray 9 := by intros; exact rxo_of_lawful

-- `Std.Ric.pairwise_toList_lt` (hypothesis 10, dependent): derivable by `rxc_of_lawful`.
theorem d40 : indep% Std.Ric.pairwise_toList_lt 10 := by intros; exact rxc_of_lawful

-- `Std.Ric.getElem_toList_eq` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d41 : indep% Std.Ric.getElem_toList_eq 9 := by intros; exact rxc_of_lawful

-- `Std.Rio.pairwise_toList_le` (hypothesis 11, dependent): derivable by `rxo_of_lawful`.
theorem d42 : indep% Std.Rio.pairwise_toList_le 11 := by intros; exact rxo_of_lawful

-- `Std.Roc.eq_succMany?_of_toList_eq_append_cons` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d43 : indep% Std.Roc.eq_succMany?_of_toList_eq_append_cons 7 := by intros; exact rxc_of_lawful

-- `Std.Rco.eq_succMany?_of_toList_eq_append_cons` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d44 : indep% Std.Rco.eq_succMany?_of_toList_eq_append_cons 7 := by intros; exact rxo_of_lawful

-- `Std.Roo.eq_succMany?_of_toList_eq_append_cons` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d45 : indep% Std.Roo.eq_succMany?_of_toList_eq_append_cons 7 := by intros; exact rxo_of_lawful

-- `Std.Roo.eq_succMany?_of_toArray_eq_append_append` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d46 : indep% Std.Roo.eq_succMany?_of_toArray_eq_append_append 7 := by intros; exact rxo_of_lawful

-- `Std.Rio.pairwise_toList_lt` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d47 : indep% Std.Rio.pairwise_toList_lt 9 := by intros; exact rxo_of_lawful

-- `Std.Rio.mem_toArray_iff_mem` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d48 : indep% Std.Rio.mem_toArray_iff_mem 9 := by intros; exact rxo_of_lawful

-- `Std.Ric.size_toArray` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d49 : indep% Std.Ric.size_toArray 9 := by intros; exact rxc_of_lawful

-- `Std.Ric.pairwise_toList_le` (hypothesis 10, dependent): derivable by `rxc_of_lawful`.
theorem d50 : indep% Std.Ric.pairwise_toList_le 10 := by intros; exact rxc_of_lawful

-- `Std.Rio.mem_toList_iff_mem` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d51 : indep% Std.Rio.mem_toList_iff_mem 9 := by intros; exact rxo_of_lawful

-- `Std.Ric.getElem?_toArray_eq` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d52 : indep% Std.Ric.getElem?_toArray_eq 9 := by intros; exact rxc_of_lawful

-- `Std.Rio.getElem?_toArray_eq` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d53 : indep% Std.Rio.getElem?_toArray_eq 9 := by intros; exact rxo_of_lawful

-- `Std.Rio.getElem?_toList_eq` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d54 : indep% Std.Rio.getElem?_toList_eq 9 := by intros; exact rxo_of_lawful

-- `Std.Rco.mem_toArray_iff_mem` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d55 : indep% Std.Rco.mem_toArray_iff_mem 9 := by intros; exact rxo_of_lawful

-- `Std.Rio.length_toList` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d56 : indep% Std.Rio.length_toList 9 := by intros; exact rxo_of_lawful

-- `Std.Ric.mem_toList_iff_mem` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d57 : indep% Std.Ric.mem_toList_iff_mem 9 := by intros; exact rxc_of_lawful

-- `Std.Ric.getElem?_toList_eq` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d58 : indep% Std.Ric.getElem?_toList_eq 9 := by intros; exact rxc_of_lawful

-- `Std.Roc.mem_toList_iff_mem` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d59 : indep% Std.Roc.mem_toList_iff_mem 9 := by intros; exact rxc_of_lawful

-- `Std.Ric.mem_toArray_iff_mem` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d60 : indep% Std.Ric.mem_toArray_iff_mem 9 := by intros; exact rxc_of_lawful

-- `Std.Ric.length_toList` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d61 : indep% Std.Ric.length_toList 9 := by intros; exact rxc_of_lawful

-- `Std.Rco.mem_toList_iff_mem` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d62 : indep% Std.Rco.mem_toList_iff_mem 9 := by intros; exact rxo_of_lawful

-- `Std.Rio.size_toArray` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d63 : indep% Std.Rio.size_toArray 9 := by intros; exact rxo_of_lawful

-- `Std.Roo.getElem_toArray_eq` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d64 : indep% Std.Roo.getElem_toArray_eq 6 := by intros; exact rxo_of_lawful

-- `Std.Roo.getElem_toList_eq` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d65 : indep% Std.Roo.getElem_toList_eq 7 := by intros; exact rxo_of_lawful

-- `Std.Rcc.isSome_succMany?_of_lt_size_toArray` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d66 : indep% Std.Rcc.isSome_succMany?_of_lt_size_toArray 7 := by intros; exact rxc_of_lawful

-- `Std.Roo.length_toList` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d67 : indep% Std.Roo.length_toList 8 := by intros; exact rxo_of_lawful

-- `Std.Roc.isSome_succMany?_of_lt_length_toList` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d68 : indep% Std.Roc.isSome_succMany?_of_lt_length_toList 7 := by intros; exact rxc_of_lawful

-- `Std.Ric.pairwise_toList_upwardEnumerableLt` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d69 : indep% Std.Ric.pairwise_toList_upwardEnumerableLt 9 := by intros; exact rxc_of_lawful

-- `Std.Rco.getElem_toList_eq` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d70 : indep% Std.Rco.getElem_toList_eq 7 := by intros; exact rxo_of_lawful

-- `Std.Ric.toArray_ne_empty` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d71 : indep% Std.Ric.toArray_ne_empty 9 := by intros; exact rxc_of_lawful

-- `Std.Rcc.pairwise_toList_lt` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d72 : indep% Std.Rcc.pairwise_toList_lt 9 := by intros; exact rxc_of_lawful

-- `Std.Rio.toList_eq_if_roo` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d73 : indep% Std.Rio.toList_eq_if_roo 9 := by intros; exact rxo_of_lawful

-- `Std.Rco.isSome_succMany?_of_lt_size_toArray` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d74 : indep% Std.Rco.isSome_succMany?_of_lt_size_toArray 7 := by intros; exact rxo_of_lawful

-- `Std.Rio.toList_eq_ite_roo` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d75 : indep% Std.Rio.toList_eq_ite_roo 9 := by intros; exact rxo_of_lawful

-- `Std.Ric.toArray_eq_if_roc` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d76 : indep% Std.Ric.toArray_eq_if_roc 9 := by intros; exact rxc_of_lawful

-- `Std.Roc.getElem_toArray_eq` (hypothesis 6, dependent): derivable by `rxc_of_lawful`.
theorem d77 : indep% Std.Roc.getElem_toArray_eq 6 := by intros; exact rxc_of_lawful

-- `Std.Roc.toArray_eq_empty_iff` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d78 : indep% Std.Roc.toArray_eq_empty_iff 9 := by intros; exact rxc_of_lawful

-- `Std.toList_roc_eq_toList_rcc_of_isSome_succ?` (hypothesis 6, dependent): derivable by `rxc_of_lawful`.
theorem d79 : indep% Std.toList_roc_eq_toList_rcc_of_isSome_succ? 6 := by intros; exact rxc_of_lawful

-- `Std.Rco.pairwise_toList_upwardEnumerableLt` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d80 : indep% Std.Rco.pairwise_toList_upwardEnumerableLt 8 := by intros; exact rxo_of_lawful

-- `Std.Roo.mem_toArray_iff_mem` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d81 : indep% Std.Roo.mem_toArray_iff_mem 7 := by intros; exact rxo_of_lawful

-- `Std.Rco.toList_eq_ite_rco` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d82 : indep% Std.Rco.toList_eq_ite_rco 6 := by intros; exact rxo_of_lawful

-- `Std.Rcc.toList_eq_if_roc` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d83 : indep% Std.Rcc.toList_eq_if_roc 7 := by intros; exact rxc_of_lawful

-- `Std.Rco.toList_eq_if_roo` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d84 : indep% Std.Rco.toList_eq_if_roo 6 := by intros; exact rxo_of_lawful

-- `Std.Rcc.pairwise_toList_upwardEnumerableLt` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d85 : indep% Std.Rcc.pairwise_toList_upwardEnumerableLt 7 := by intros; exact rxc_of_lawful

-- `Std.Rio.forIn'_eq_forIn'_rco` (hypothesis 10, dependent): derivable by `rxo_of_lawful`.
theorem d86 : indep% Std.Rio.forIn'_eq_forIn'_rco 10 := by intros; exact rxo_of_lawful

-- `Std.Roc.forIn'_toList_eq_forIn'` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d87 : indep% Std.Roc.forIn'_toList_eq_forIn' 9 := by intros; exact rxc_of_lawful

-- `Std.Ric.forIn'_eq_forIn'_rcc` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d88 : indep% Std.Ric.forIn'_eq_forIn'_rcc 8 := by intros; exact rxc_of_lawful

-- `Std.Roc.forIn'_eq_forIn'_toArray` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d89 : indep% Std.Roc.forIn'_eq_forIn'_toArray 8 := by intros; exact rxc_of_lawful

-- `Std.Rio.forIn'_eq_ite_roo` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d90 : indep% Std.Rio.forIn'_eq_ite_roo 8 := by intros; exact rxo_of_lawful

-- `Std.Roc.toList_succ_succ_eq_map` (hypothesis 10, dependent): derivable by `rxc_of_lawful`.
theorem d91 : indep% Std.Roc.toList_succ_succ_eq_map 10 := by intros; exact rxc_of_lawful

-- `Std.Roc.toArray_succ_succ_eq_map` (hypothesis 10, dependent): derivable by `rxc_of_lawful`.
theorem d92 : indep% Std.Roc.toArray_succ_succ_eq_map 10 := by intros; exact rxc_of_lawful

-- `Std.Rcc.forIn'_eq_forIn'_toList` (hypothesis 6, dependent): derivable by `rxc_of_lawful`.
theorem d93 : indep% Std.Rcc.forIn'_eq_forIn'_toList 6 := by intros; exact rxc_of_lawful

-- `Std.Rcc.forIn'_eq_forIn'_toArray` (hypothesis 6, dependent): derivable by `rxc_of_lawful`.
theorem d94 : indep% Std.Rcc.forIn'_eq_forIn'_toArray 6 := by intros; exact rxc_of_lawful

-- `Std.Rio.isSome_succMany?_of_lt_length_toList` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d95 : indep% Std.Rio.isSome_succMany?_of_lt_length_toList 9 := by intros; exact rxo_of_lawful

-- `Std.Roc.eq_succMany?_of_toArray_eq_append_append` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d96 : indep% Std.Roc.eq_succMany?_of_toArray_eq_append_append 7 := by intros; exact rxc_of_lawful

-- `Std.Rcc.toArray_succ_succ_eq_map` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d97 : indep% Std.Rcc.toArray_succ_succ_eq_map 7 := by intros; exact rxc_of_lawful

-- `Std.Roc.mem_toArray_iff_mem` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d98 : indep% Std.Roc.mem_toArray_iff_mem 9 := by intros; exact rxc_of_lawful

-- `Std.Roc.size_toArray` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d99 : indep% Std.Roc.size_toArray 8 := by intros; exact rxc_of_lawful

-- `Std.Rio.pairwise_toList_upwardEnumerableLt` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d100 : indep% Std.Rio.pairwise_toList_upwardEnumerableLt 9 := by intros; exact rxo_of_lawful

-- `Std.Ric.pairwise_toList_ne` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d101 : indep% Std.Ric.pairwise_toList_ne 9 := by intros; exact rxc_of_lawful

-- `Std.toList_roo_eq_toList_rco_of_isSome_succ?` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d102 : indep% Std.toList_roo_eq_toList_rco_of_isSome_succ? 6 := by intros; exact rxo_of_lawful

-- `Std.Rio.toList_eq_match_rco` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d103 : indep% Std.Rio.toList_eq_match_rco 8 := by intros; exact rxo_of_lawful

-- `Std.Ric.nodup_toList` (hypothesis 5, dependent): derivable by `rxc_of_lawful`.
theorem d104 : indep% Std.Ric.nodup_toList 5 := by intros; exact rxc_of_lawful

-- `Std.Rcc.mem_toList_iff_mem` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d105 : indep% Std.Rcc.mem_toList_iff_mem 7 := by intros; exact rxc_of_lawful

-- `Std.Rco.nodup_toList` (hypothesis 4, dependent): derivable by `rxo_of_lawful`.
theorem d106 : indep% Std.Rco.nodup_toList 4 := by intros; exact rxo_of_lawful

-- `Std.Roo.nodup_toList` (hypothesis 4, dependent): derivable by `rxo_of_lawful`.
theorem d107 : indep% Std.Roo.nodup_toList 4 := by intros; exact rxo_of_lawful

-- `Std.Roo.toList_eq_nil_iff` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d108 : indep% Std.Roo.toList_eq_nil_iff 8 := by intros; exact rxo_of_lawful

-- `Std.Rcc.getElem?_toArray_eq` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d109 : indep% Std.Rcc.getElem?_toArray_eq 7 := by intros; exact rxc_of_lawful

-- `Std.Ric.toList_eq_match_rcc` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d110 : indep% Std.Ric.toList_eq_match_rcc 8 := by intros; exact rxc_of_lawful

-- `Std.Rco.getElem?_toArray_eq` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d111 : indep% Std.Rco.getElem?_toArray_eq 7 := by intros; exact rxo_of_lawful

-- `Std.Roc.getElem?_toArray_eq` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d112 : indep% Std.Roc.getElem?_toArray_eq 7 := by intros; exact rxc_of_lawful

-- `Std.Rco.toArray_eq_ite_roo` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d113 : indep% Std.Rco.toArray_eq_ite_roo 6 := by intros; exact rxo_of_lawful

-- `Std.Roc.pairwise_toList_upwardEnumerableLt` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d114 : indep% Std.Roc.pairwise_toList_upwardEnumerableLt 7 := by intros; exact rxc_of_lawful

-- `Std.Rcc.toArray_eq_empty_iff` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d115 : indep% Std.Rcc.toArray_eq_empty_iff 7 := by intros; exact rxc_of_lawful

-- `Std.Rco.toArray_eq_ite_rco` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d116 : indep% Std.Rco.toArray_eq_ite_rco 6 := by intros; exact rxo_of_lawful

-- `Std.Rcc.pairwise_toList_ne` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d117 : indep% Std.Rcc.pairwise_toList_ne 7 := by intros; exact rxc_of_lawful

-- `Std.Roc.toList_eq_match` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d118 : indep% Std.Roc.toList_eq_match 7 := by intros; exact rxc_of_lawful

-- `Std.Roc.forIn'_congr` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d119 : indep% Std.Roc.forIn'_congr 7 := by intros; exact rxc_of_lawful

-- `Std.Rio.forIn'_congr` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d120 : indep% Std.Rio.forIn'_congr 7 := by intros; exact rxo_of_lawful

-- `Std.Ric.forIn'_eq_ite_roc` (hypothesis 10, dependent): derivable by `rxc_of_lawful`.
theorem d121 : indep% Std.Ric.forIn'_eq_ite_roc 10 := by intros; exact rxc_of_lawful

-- `Std.Roc.forIn'_toArray_eq_forIn'` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d122 : indep% Std.Roc.forIn'_toArray_eq_forIn' 9 := by intros; exact rxc_of_lawful

-- `Std.Rco.forIn'_eq_if` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d123 : indep% Std.Rco.forIn'_eq_if 9 := by intros; exact rxo_of_lawful

-- `Std.Roc.forIn'_eq_forIn'_toList` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d124 : indep% Std.Roc.forIn'_eq_forIn'_toList 8 := by intros; exact rxc_of_lawful

-- `Std.Rio.forIn'_eq_forIn'_toArray` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d125 : indep% Std.Rio.forIn'_eq_forIn'_toArray 8 := by intros; exact rxo_of_lawful

-- `Std.Rcc.forIn'_eq_ite` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d126 : indep% Std.Rcc.forIn'_eq_ite 8 := by intros; exact rxc_of_lawful

-- `Std.Roc.toList_eq_toList_roo` (hypothesis 10, dependent): derivable by `rxc_of_lawful`.
theorem d127 : indep% Std.Roc.toList_eq_toList_roo 10 := by intros; exact rxc_of_lawful

-- `Std.Roc.toList_eq_toList_roo` (hypothesis 11, dependent): derivable by `rxo_of_lawful`.
theorem d128 : indep% Std.Roc.toList_eq_toList_roo 11 := by intros; exact rxo_of_lawful

-- `Std.Rco.toList_succ_succ_eq_map` (hypothesis 10, dependent): derivable by `rxo_of_lawful`.
theorem d129 : indep% Std.Rco.toList_succ_succ_eq_map 10 := by intros; exact rxo_of_lawful

-- `Std.Ric.eq_succMany?_of_toList_eq_append_cons` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d130 : indep% Std.Ric.eq_succMany?_of_toList_eq_append_cons 9 := by intros; exact rxc_of_lawful

-- `Std.Rio.eq_succMany?_of_toList_eq_append_cons` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d131 : indep% Std.Rio.eq_succMany?_of_toList_eq_append_cons 9 := by intros; exact rxo_of_lawful

-- `Std.Ric.toArray_succ_eq_map` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d132 : indep% Std.Ric.toArray_succ_eq_map 9 := by intros; exact rxc_of_lawful

-- `Std.Rcc.isSome_succMany?_of_lt_length_toList` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d133 : indep% Std.Rcc.isSome_succMany?_of_lt_length_toList 7 := by intros; exact rxc_of_lawful

-- `Std.Rcc.getElem_toArray_eq` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d134 : indep% Std.Rcc.getElem_toArray_eq 7 := by intros; exact rxc_of_lawful

-- `Std.Rio.toArray_eq_if_roo` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d135 : indep% Std.Rio.toArray_eq_if_roo 9 := by intros; exact rxo_of_lawful

-- `Std.Rio.pairwise_toList_ne` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d136 : indep% Std.Rio.pairwise_toList_ne 9 := by intros; exact rxo_of_lawful

-- `Std.Rio.toArray_eq_nil_iff` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d137 : indep% Std.Rio.toArray_eq_nil_iff 9 := by intros; exact rxo_of_lawful

-- `Std.Ric.toList_eq_toList_rcc` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d138 : indep% Std.Ric.toList_eq_toList_rcc 9 := by intros; exact rxc_of_lawful

-- `Std.Rco.length_toList` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d139 : indep% Std.Rco.length_toList 8 := by intros; exact rxo_of_lawful

-- `Std.Roo.pairwise_toList_le` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d140 : indep% Std.Roo.pairwise_toList_le 9 := by intros; exact rxo_of_lawful

-- `Std.Roc.getElem_toList_eq` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d141 : indep% Std.Roc.getElem_toList_eq 7 := by intros; exact rxc_of_lawful

-- `Std.Rco.pairwise_toList_lt` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d142 : indep% Std.Rco.pairwise_toList_lt 8 := by intros; exact rxo_of_lawful

-- `Std.Rcc.nodup_toList` (hypothesis 4, dependent): derivable by `rxc_of_lawful`.
theorem d143 : indep% Std.Rcc.nodup_toList 4 := by intros; exact rxc_of_lawful

-- `Std.Roo.toArray_eq_match` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d144 : indep% Std.Roo.toArray_eq_match 8 := by intros; exact rxo_of_lawful

-- `Std.Rcc.mem_toArray_iff_mem` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d145 : indep% Std.Rcc.mem_toArray_iff_mem 7 := by intros; exact rxc_of_lawful

-- `Std.Roo.getElem?_toArray_eq` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d146 : indep% Std.Roo.getElem?_toArray_eq 7 := by intros; exact rxo_of_lawful

-- `Std.Roo.getElem?_toList_eq` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d147 : indep% Std.Roo.getElem?_toList_eq 7 := by intros; exact rxo_of_lawful

-- `Std.Roo.mem_toList_iff_mem` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d148 : indep% Std.Roo.mem_toList_iff_mem 7 := by intros; exact rxo_of_lawful

-- `Std.Rio.nodup_toList` (hypothesis 5, dependent): derivable by `rxo_of_lawful`.
theorem d149 : indep% Std.Rio.nodup_toList 5 := by intros; exact rxo_of_lawful

-- `Std.Roc.nodup_toList` (hypothesis 4, dependent): derivable by `rxc_of_lawful`.
theorem d150 : indep% Std.Roc.nodup_toList 4 := by intros; exact rxc_of_lawful

-- `Std.Rcc.getElem?_toList_eq` (hypothesis 6, dependent): derivable by `rxc_of_lawful`.
theorem d151 : indep% Std.Rcc.getElem?_toList_eq 6 := by intros; exact rxc_of_lawful

-- `Std.Roc.pairwise_toList_le` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d152 : indep% Std.Roc.pairwise_toList_le 8 := by intros; exact rxc_of_lawful

-- `Std.Rco.getElem?_toList_eq` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d153 : indep% Std.Rco.getElem?_toList_eq 6 := by intros; exact rxo_of_lawful

-- `Std.Rco.pairwise_toList_ne` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d154 : indep% Std.Rco.pairwise_toList_ne 8 := by intros; exact rxo_of_lawful

-- `Std.Roc.getElem?_toList_eq` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d155 : indep% Std.Roc.getElem?_toList_eq 7 := by intros; exact rxc_of_lawful

-- `Std.Rcc.pairwise_toList_le` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d156 : indep% Std.Rcc.pairwise_toList_le 8 := by intros; exact rxc_of_lawful

-- `Std.Rco.toList_eq_if_rco` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d157 : indep% Std.Rco.toList_eq_if_rco 6 := by intros; exact rxo_of_lawful

-- `Std.Roc.pairwise_toList_ne` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d158 : indep% Std.Roc.pairwise_toList_ne 7 := by intros; exact rxc_of_lawful

-- `Std.Roo.pairwise_toList_ne` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d159 : indep% Std.Roo.pairwise_toList_ne 7 := by intros; exact rxo_of_lawful

-- `Std.Rcc.toArray_eq_if_roc` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d160 : indep% Std.Rcc.toArray_eq_if_roc 7 := by intros; exact rxc_of_lawful

-- `Std.Roo.pairwise_toList_upwardEnumerableLt` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d161 : indep% Std.Roo.pairwise_toList_upwardEnumerableLt 7 := by intros; exact rxo_of_lawful

-- `Std.Rco.toList_eq_nil_iff` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d162 : indep% Std.Rco.toList_eq_nil_iff 7 := by intros; exact rxo_of_lawful

-- `Std.Rco.toArray_eq_if_rco` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d163 : indep% Std.Rco.toArray_eq_if_rco 6 := by intros; exact rxo_of_lawful

-- `Std.Rco.forIn'_congr` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d164 : indep% Std.Rco.forIn'_congr 7 := by intros; exact rxo_of_lawful

-- `Std.Rco.forIn'_eq_forIn'_toList` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d165 : indep% Std.Rco.forIn'_eq_forIn'_toList 8 := by intros; exact rxo_of_lawful

-- `Std.Rio.forIn'_toList_eq_forIn'` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d166 : indep% Std.Rio.forIn'_toList_eq_forIn' 8 := by intros; exact rxo_of_lawful

-- `Std.Rcc.forIn'_eq_if` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d167 : indep% Std.Rcc.forIn'_eq_if 8 := by intros; exact rxc_of_lawful

-- `Std.Roo.forIn'_eq_forIn'_toList` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d168 : indep% Std.Roo.forIn'_eq_forIn'_toList 6 := by intros; exact rxo_of_lawful

-- `Std.Ric.toList_succ_eq_map` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d169 : indep% Std.Ric.toList_succ_eq_map 8 := by intros; exact rxc_of_lawful

-- `Std.Ric.isSome_succMany?_of_lt_length_toList` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d170 : indep% Std.Ric.isSome_succMany?_of_lt_length_toList 9 := by intros; exact rxc_of_lawful

-- `Std.Ric.getElem_toArray_eq` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d171 : indep% Std.Ric.getElem_toArray_eq 8 := by intros; exact rxc_of_lawful

-- `Std.Rio.getElem_toArray_eq` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d172 : indep% Std.Rio.getElem_toArray_eq 8 := by intros; exact rxo_of_lawful

-- `Std.Roo.toList_eq_match` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d173 : indep% Std.Roo.toList_eq_match 7 := by intros; exact rxo_of_lawful

-- `Std.Roo.toList_eq_match_rco` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d174 : indep% Std.Roo.toList_eq_match_rco 7 := by intros; exact rxo_of_lawful

-- `Std.Roc.toArray_eq_match_rcc` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d175 : indep% Std.Roc.toArray_eq_match_rcc 7 := by intros; exact rxc_of_lawful

-- `Std.Rcc.toList_eq_ite_roc` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d176 : indep% Std.Rcc.toList_eq_ite_roc 7 := by intros; exact rxc_of_lawful

-- `Std.Rcc.toArray_eq_ite_roc` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d177 : indep% Std.Rcc.toArray_eq_ite_roc 7 := by intros; exact rxc_of_lawful

-- `Std.Rco.toArray_eq_if_roo` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d178 : indep% Std.Rco.toArray_eq_if_roo 6 := by intros; exact rxo_of_lawful

-- `Std.Ric.forIn'_congr` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d179 : indep% Std.Ric.forIn'_congr 7 := by intros; exact rxc_of_lawful

-- `Std.Rcc.forIn'_congr` (hypothesis 5, dependent): derivable by `rxc_of_lawful`.
theorem d180 : indep% Std.Rcc.forIn'_congr 5 := by intros; exact rxc_of_lawful

-- `Std.Roc.forIn'_eq_match` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d181 : indep% Std.Roc.forIn'_eq_match 9 := by intros; exact rxc_of_lawful

-- `Std.Rio.forIn'_eq_if_roo` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d182 : indep% Std.Rio.forIn'_eq_if_roo 8 := by intros; exact rxo_of_lawful

-- `Std.Ric.forIn'_eq_forIn'_toArray` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d183 : indep% Std.Ric.forIn'_eq_forIn'_toArray 8 := by intros; exact rxc_of_lawful

-- `Std.Rcc.toList_eq_toList_rco` (hypothesis 10, dependent): derivable by `rxc_of_lawful`.
theorem d184 : indep% Std.Rcc.toList_eq_toList_rco 10 := by intros; exact rxc_of_lawful

-- `Std.Rcc.toList_eq_toList_rco` (hypothesis 11, dependent): derivable by `rxo_of_lawful`.
theorem d185 : indep% Std.Rcc.toList_eq_toList_rco 11 := by intros; exact rxo_of_lawful

-- `Std.Rio.toArray_succ_eq_map` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d186 : indep% Std.Rio.toArray_succ_eq_map 9 := by intros; exact rxo_of_lawful

-- `Std.Roo.forIn'_eq_forIn'_toArray` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d187 : indep% Std.Roo.forIn'_eq_forIn'_toArray 6 := by intros; exact rxo_of_lawful

-- `Std.Rcc.forIn'_toArray_eq_forIn'` (hypothesis 6, dependent): derivable by `rxc_of_lawful`.
theorem d188 : indep% Std.Rcc.forIn'_toArray_eq_forIn' 6 := by intros; exact rxc_of_lawful

-- `Std.Rcc.eq_succMany?_of_toList_eq_append_cons` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d189 : indep% Std.Rcc.eq_succMany?_of_toList_eq_append_cons 7 := by intros; exact rxc_of_lawful

-- `Std.Roo.toList_succ_succ_eq_map` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d190 : indep% Std.Roo.toList_succ_succ_eq_map 7 := by intros; exact rxo_of_lawful

-- `Std.Roo.toArray_succ_succ_eq_map` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d191 : indep% Std.Roo.toArray_succ_succ_eq_map 7 := by intros; exact rxo_of_lawful

-- `Std.Rcc.toList_succ_succ_eq_map` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d192 : indep% Std.Rcc.toList_succ_succ_eq_map 7 := by intros; exact rxc_of_lawful

-- `Std.Roc.length_toList` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d193 : indep% Std.Roc.length_toList 8 := by intros; exact rxc_of_lawful

-- `Std.Roo.isSome_succMany?_of_lt_size_toArray` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d194 : indep% Std.Roo.isSome_succMany?_of_lt_size_toArray 7 := by intros; exact rxo_of_lawful

-- `Std.Ric.toList_eq_if_roc` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d195 : indep% Std.Ric.toList_eq_if_roc 9 := by intros; exact rxc_of_lawful

-- `Std.Rcc.length_toList` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d196 : indep% Std.Rcc.length_toList 8 := by intros; exact rxc_of_lawful

-- `Std.Rco.pairwise_toList_le` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d197 : indep% Std.Rco.pairwise_toList_le 9 := by intros; exact rxo_of_lawful

-- `Std.Ric.toList_eq_ite_roc` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d198 : indep% Std.Ric.toList_eq_ite_roc 9 := by intros; exact rxc_of_lawful

-- `Std.Rio.toList_eq_nil_iff` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d199 : indep% Std.Rio.toList_eq_nil_iff 9 := by intros; exact rxo_of_lawful

-- `Std.Roc.pairwise_toList_lt` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d200 : indep% Std.Roc.pairwise_toList_lt 9 := by intros; exact rxc_of_lawful

-- `Std.Ric.toArray_eq_ite_roc` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d201 : indep% Std.Ric.toArray_eq_ite_roc 9 := by intros; exact rxc_of_lawful

-- `Std.Rio.toArray_eq_toArray_rco` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d202 : indep% Std.Rio.toArray_eq_toArray_rco 9 := by intros; exact rxo_of_lawful

-- `Std.Rcc.size_toArray` (hypothesis 8, dependent): derivable by `rxc_of_lawful`.
theorem d203 : indep% Std.Rcc.size_toArray 8 := by intros; exact rxc_of_lawful

-- `Std.Rcc.getElem_toList_eq` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d204 : indep% Std.Rcc.getElem_toList_eq 7 := by intros; exact rxc_of_lawful

-- `Std.Roo.isSome_succMany?_of_lt_length_toList` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d205 : indep% Std.Roo.isSome_succMany?_of_lt_length_toList 7 := by intros; exact rxo_of_lawful

-- `Std.Rco.getElem_toArray_eq` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d206 : indep% Std.Rco.getElem_toArray_eq 7 := by intros; exact rxo_of_lawful

-- `Std.Roc.toList_eq_nil_iff` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d207 : indep% Std.Roc.toList_eq_nil_iff 9 := by intros; exact rxc_of_lawful

-- `Std.Ric.toList_ne_nil` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d208 : indep% Std.Ric.toList_ne_nil 9 := by intros; exact rxc_of_lawful

-- `Std.Ric.toArray_eq_toArray_rcc` (hypothesis 9, dependent): derivable by `rxc_of_lawful`.
theorem d209 : indep% Std.Ric.toArray_eq_toArray_rcc 9 := by intros; exact rxc_of_lawful

-- `Std.Rio.toArray_eq_ite_roo` (hypothesis 9, dependent): derivable by `rxo_of_lawful`.
theorem d210 : indep% Std.Rio.toArray_eq_ite_roo 9 := by intros; exact rxo_of_lawful

-- `Std.Roo.size_toArray` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d211 : indep% Std.Roo.size_toArray 8 := by intros; exact rxo_of_lawful

-- `Std.Rio.toArray_eq_match_rco` (hypothesis 8, dependent): derivable by `rxo_of_lawful`.
theorem d212 : indep% Std.Rio.toArray_eq_match_rco 8 := by intros; exact rxo_of_lawful

-- `Std.Roo.pairwise_toList_lt` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d213 : indep% Std.Roo.pairwise_toList_lt 7 := by intros; exact rxo_of_lawful

-- `Std.Roo.toArray_eq_match_rco` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d214 : indep% Std.Roo.toArray_eq_match_rco 7 := by intros; exact rxo_of_lawful

-- `Std.Rcc.toList_eq_nil_iff` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d215 : indep% Std.Rcc.toList_eq_nil_iff 7 := by intros; exact rxc_of_lawful

-- `Std.Roc.toArray_eq_match` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d216 : indep% Std.Roc.toArray_eq_match 7 := by intros; exact rxc_of_lawful

-- `Std.Rco.toList_eq_ite_roo` (hypothesis 6, dependent): derivable by `rxo_of_lawful`.
theorem d217 : indep% Std.Rco.toList_eq_ite_roo 6 := by intros; exact rxo_of_lawful

-- `Std.Rco.toArray_eq_empty_iff` (hypothesis 7, dependent): derivable by `rxo_of_lawful`.
theorem d218 : indep% Std.Rco.toArray_eq_empty_iff 7 := by intros; exact rxo_of_lawful

-- `Std.Roc.toList_eq_match_rcc` (hypothesis 7, dependent): derivable by `rxc_of_lawful`.
theorem d219 : indep% Std.Roc.toList_eq_match_rcc 7 := by intros; exact rxc_of_lawful

end RangeFiniteHand
