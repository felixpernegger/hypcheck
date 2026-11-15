import Std
import Lean

/-!
Hand pass `DoSpecA` (hand15): the 189 unresolved hypotheses of the first half of
`Std.Do.Triple.SpecLemmas` (`List.Cursor.ext`, the monad specs `Spec.pure'/bind'/map'/seq'`, the loop
specs over lists, legacy ranges, `Std.Rcc/Rco/Roc/Roo/Ric/Rio/Rci/Roi/Rii`, slices and iterators,
and the `Spec.IterM.forIn_*`/`foldM_*` combinator specs).

173 necessary, 16 removable, 0 independent, 0 left unresolved.

Removable (16):
* `List.Cursor.ext` idx 4 and 5: either field equation implies the other, since both append to `l`.
* `Rxc.IsAlwaysFinite α` (6 rows: rcc/roc/ric) and `Rxo.IsAlwaysFinite α` (6 rows: rco/roo/rio), dependent:
  derivable from `LawfulUpwardEnumerable` + `LawfulUpwardEnumerableLE` resp. `LT` (other binders), lemmas
  `rxcF`/`rxoF` (an endless chain below `hi` would reach `hi` and then cycle, contradicting `ne_of_lt`).
* `LawfulMonad m` of `Spec.IterM.forIn_filterMap`/`forIn_filter`: the base equations hold without it
  (law-free proofs copied from `checks/ItMonadMAHand.lean`, namespace `DoSpecAMA.MA.Rem`).

Necessary, by kind:
* `h` of `Spec.pure'/bind'/map'/seq'` and of the `Spec.IterM` combinator specs: everything in `Id`,
  precondition `True`, postcondition `False`.
* loop `step` premises: in `Id`, invariant `suffix ≠ []` on a one-element collection (true at the start,
  false at the end; no loop evaluation), resp. value invariants for the `_const_inv` variants; ranges
  over `Nat`, `Fin 2` for `Rci/Roi/Rii`; slice `Slice SL` (list iterator `[0]`).
* dependent range-class rows: models (copied from `checks/RangeDepAHand.lean`) `M0`, `U1`, `NLE`,
  `NLT`, `NLeast`, and new finite one-point carriers `U0F` (LE empty), `U0T` (LT total), `U0N`
  (`least? = none`), all with `Rxi.IsAlwaysFinite`; `Nat.not_RxiF` for `Rxi.IsAlwaysFinite`.
* `Finite α Id`/`Finite α m`: the non-finite iterator `AD` with two vacuously lawful loops `NoLoop`
  (returns `init`) and `ADLoop 0` (runs the body once): for the `Iter` specs the invariant
  `acc = cursor position` makes the opaque `toList.length` equal `0` and `1`; for the combinator specs
  the combinator side (default loop) is the same term while the hypothesis holds for `0` resp. `1`.
* `LawfulIteratorLoop`: `NoLoop` on the list iterator (`Iter` specs), resp. the finite iterator `FD`
  with the two unlawful loops `NoLoop`/`FDLoop 0` (combinator specs; `foldM` ones with
  `o = StateT Unit Id`, so that the `n`-loop can stay the lawful default).
* `LawfulMonad n`, `WeaklyLawfulMonadAttach n`, `LawfulMonadLiftT m n/n o`, `LawfulMonad m` of
  `forIn_map`: the broken monads/lifts of `checks/ItMonadMAHand.lean`; the WP monad (`NW`, `NW2`,
  `NWb`, `W`, `Id`) gets a `WPMonad` instance via a monad morphism into `StateM σ` and a pin lemma
  `(∀ P Q, Triple y P Q → Triple x P Q) → x = y` (both copied from `checks/DoSpecBHand.lean`,
  namespace renamed `DoSpecAMA`), then the base refutation runs unchanged.

Reusable models: `DoSpecAHand.AD`/`ADLoop`/`NoLoop`/`FD`/`FDLoop` (+ `trip_of`/`of_trip`,
`trip_ofS`/`of_tripS`), `DoSpecAHand.U0F/U0T/U0N`, `DoSpecAHand.rxcF/rxoF`.

Run with the lean4 repo's stage1 binary: `runs/hand15/lean.sh checks/DoSpecAHand.lean`.
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


set_option linter.deprecated false
set_option warn.classDefReducibility false
set_option linter.unusedSimpArgs false
open Std Std.Do Std.PRange Std.Iterators

namespace DoSpecAHand

/-! ## Range models -/

/-- `M0`: one point, `succMany?` constantly `none` (so `succMany? 0 a ≠ some a`); `≤`, `<` empty. -/
inductive M0 | pt deriving DecidableEq
instance : UpwardEnumerable M0 := { succ? := fun a => some a, succMany? := fun _ _ => none }
instance : LE M0 := ⟨fun _ _ => False⟩
instance : LT M0 := ⟨fun _ _ => False⟩
instance : DecidableLE M0 := fun _ _ => isFalse id
instance : DecidableLT M0 := fun _ _ => isFalse id
instance : Least? M0 := ⟨some .pt⟩
instance : Rxc.HasSize M0 := ⟨fun _ _ => 0⟩
instance : Rxo.HasSize M0 := ⟨fun _ _ => 0⟩
instance : LawfulUpwardEnumerableLE M0 := ⟨fun _ _ => ⟨False.elim, fun ⟨_, h⟩ => nomatch h⟩⟩
instance : LawfulUpwardEnumerableLT M0 := ⟨fun _ _ => ⟨False.elim, fun ⟨_, h⟩ => nomatch h⟩⟩
instance : InfinitelyUpwardEnumerable M0 := ⟨fun _ => rfl⟩
instance : LinearlyUpwardEnumerable M0 := ⟨fun .pt .pt _ => rfl⟩
instance : Rxc.IsAlwaysFinite M0 := ⟨fun _ _ => ⟨0, trivial⟩⟩
instance : Rxo.IsAlwaysFinite M0 := ⟨fun _ _ => ⟨0, trivial⟩⟩
instance : Rxc.LawfulHasSize M0 := ⟨fun _ _ _ => rfl, fun _ _ h => h.elim, fun _ _ _ h => h.elim⟩
instance : Rxo.LawfulHasSize M0 := ⟨fun _ _ _ => rfl, fun _ _ h => h.elim, fun _ _ _ h => h.elim⟩
theorem M0.not_LUE : ¬ LawfulUpwardEnumerable M0 := fun h => nomatch h.succMany?_zero .pt
theorem M0.not_LLeast : ¬ LawfulUpwardEnumerableLeast? M0 := fun h => by
  obtain ⟨_, _, _, h⟩ := h.least?_le .pt; exact nomatch h

/-- `U1`: one point, `succ? = some`, but `succMany? n = none` for `n > 0`; `≤` true, `<` empty. -/
inductive U1 | pt deriving DecidableEq
instance : UpwardEnumerable U1 :=
  { succ? := fun a => some a, succMany? := fun n a => if n = 0 then some a else none }
instance : LE U1 := ⟨fun _ _ => True⟩
instance : LT U1 := ⟨fun _ _ => False⟩
instance : DecidableLE U1 := fun _ _ => isTrue trivial
instance : DecidableLT U1 := fun _ _ => isFalse id
instance : Least? U1 := ⟨some .pt⟩
instance : Rxc.HasSize U1 := ⟨fun _ _ => 1⟩
instance : Rxo.HasSize U1 := ⟨fun _ _ => 0⟩
instance : LawfulUpwardEnumerableLE U1 := ⟨fun .pt .pt => ⟨fun _ => ⟨0, rfl⟩, fun _ => trivial⟩⟩
instance : LawfulUpwardEnumerableLT U1 := ⟨fun _ _ => ⟨False.elim, fun ⟨_, h⟩ => nomatch h⟩⟩
instance : LawfulUpwardEnumerableLeast? U1 := ⟨fun .pt => ⟨.pt, rfl, 0, rfl⟩⟩
instance : InfinitelyUpwardEnumerable U1 := ⟨fun _ => rfl⟩
instance : LinearlyUpwardEnumerable U1 := ⟨fun .pt .pt _ => rfl⟩
instance : Rxc.IsAlwaysFinite U1 := ⟨fun _ _ => ⟨1, trivial⟩⟩
instance : Rxo.IsAlwaysFinite U1 := ⟨fun _ _ => ⟨0, id⟩⟩
instance : Rxo.LawfulHasSize U1 := ⟨fun _ _ _ => rfl, fun _ _ h => h.elim, fun _ _ _ h => h.elim⟩
theorem U1.not_LUE : ¬ LawfulUpwardEnumerable U1 := fun h => nomatch h.succMany?_add_one 0 .pt
theorem U1.not_RxcLawfulHasSize : ¬ Rxc.LawfulHasSize U1 := fun h =>
  nomatch h.size_eq_succ_of_succ?_eq_some .pt .pt .pt trivial rfl

/-- Nat with a broken `≤` (`a ≤ b + 1`); everything else is Nat's. -/
def NLE := Nat
def NLE.pt (n : Nat) : NLE := n
instance : UpwardEnumerable NLE := { succ? := fun (n : Nat) => some (n + 1), succMany? := fun k (n : Nat) => some (n + k) }
instance : LE NLE := ⟨fun (a b : Nat) => a ≤ b + 1⟩
instance : DecidableLE NLE := fun (a b : Nat) => Nat.decLe a (b + 1)
instance : LT NLE := inferInstanceAs (LT Nat)
instance : DecidableLT NLE := inferInstanceAs (DecidableLT Nat)
instance : Least? NLE := ⟨some (NLE.pt 0)⟩
instance : LawfulUpwardEnumerable NLE := inferInstanceAs (LawfulUpwardEnumerable Nat)
instance : LawfulUpwardEnumerableLT NLE := inferInstanceAs (LawfulUpwardEnumerableLT Nat)
instance : LawfulUpwardEnumerableLeast? NLE := inferInstanceAs (LawfulUpwardEnumerableLeast? Nat)
instance : InfinitelyUpwardEnumerable NLE := inferInstanceAs (InfinitelyUpwardEnumerable Nat)
instance : LinearlyUpwardEnumerable NLE := inferInstanceAs (LinearlyUpwardEnumerable Nat)
instance : Rxo.IsAlwaysFinite NLE := inferInstanceAs (Rxo.IsAlwaysFinite Nat)
instance : Rxc.IsAlwaysFinite NLE :=
  ⟨fun (i hi : Nat) => ⟨hi + 2, show ¬ (i + (hi + 2) ≤ hi + 1) by omega⟩⟩
theorem NLE.not_LLE : ¬ LawfulUpwardEnumerableLE NLE := fun h => by
  obtain ⟨n, hn⟩ := (h.le_iff (1 : Nat) (0 : Nat)).1 (show (1 : Nat) ≤ 0 + 1 by omega)
  change some (1 + n) = some 0 at hn; simp at hn


/-- Nat with a broken `<` (`a < b + 1`, i.e. `≤`); everything else is Nat's. -/
def NLT := Nat
def NLT.pt (n : Nat) : NLT := n
instance : UpwardEnumerable NLT := { succ? := fun (n : Nat) => some (n + 1), succMany? := fun k (n : Nat) => some (n + k) }
instance : LE NLT := inferInstanceAs (LE Nat)
instance : DecidableLE NLT := inferInstanceAs (DecidableLE Nat)
instance : LT NLT := ⟨fun (a b : Nat) => a < b + 1⟩
instance : DecidableLT NLT := fun (a b : Nat) => Nat.decLt a (b + 1)
instance : Least? NLT := ⟨some (NLT.pt 0)⟩
instance : LawfulUpwardEnumerable NLT := inferInstanceAs (LawfulUpwardEnumerable Nat)
instance : LawfulUpwardEnumerableLE NLT := inferInstanceAs (LawfulUpwardEnumerableLE Nat)
instance : LawfulUpwardEnumerableLeast? NLT := inferInstanceAs (LawfulUpwardEnumerableLeast? Nat)
instance : InfinitelyUpwardEnumerable NLT := inferInstanceAs (InfinitelyUpwardEnumerable Nat)
instance : LinearlyUpwardEnumerable NLT := inferInstanceAs (LinearlyUpwardEnumerable Nat)
instance : Rxc.IsAlwaysFinite NLT := inferInstanceAs (Rxc.IsAlwaysFinite Nat)
instance : Rxo.IsAlwaysFinite NLT :=
  ⟨fun (i hi : Nat) => ⟨hi + 1, show ¬ (i + (hi + 1) < hi + 1) by omega⟩⟩
theorem NLT.not_LLT : ¬ LawfulUpwardEnumerableLT NLT := fun h => by
  obtain ⟨n, hn⟩ := (h.lt_iff (0 : Nat) (0 : Nat)).1 (show (0 : Nat) < 0 + 1 by omega)
  change some (0 + (n + 1)) = some 0 at hn; simp at hn

/-- Nat with `least? = some 1`; everything else is Nat's. -/
def NLeast := Nat
def NLeast.pt (n : Nat) : NLeast := n
instance : UpwardEnumerable NLeast := { succ? := fun (n : Nat) => some (n + 1), succMany? := fun k (n : Nat) => some (n + k) }
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

instance : Rxi.IsAlwaysFinite M0 := ⟨fun _ => ⟨0, rfl⟩⟩
instance : Rxi.IsAlwaysFinite U1 := ⟨fun _ => ⟨1, rfl⟩⟩

/-- `U0F`: one point without successor, `≤` empty (so `LawfulUpwardEnumerableLE` fails). -/
inductive U0F | pt deriving DecidableEq
instance : UpwardEnumerable U0F := { succ? := fun _ => none, succMany? := fun n a => if n = 0 then some a else none }
instance : LE U0F := ⟨fun _ _ => False⟩
instance : DecidableLE U0F := fun _ _ => isFalse id
instance : LawfulUpwardEnumerable U0F where
  ne_of_lt _ _ := fun ⟨_, h⟩ => nomatch h
  succMany?_zero _ := rfl
  succMany?_add_one n a := by cases n <;> rfl
instance : Rxi.IsAlwaysFinite U0F := ⟨fun _ => ⟨1, rfl⟩⟩
theorem U0F.not_LLE : ¬ LawfulUpwardEnumerableLE U0F := fun h =>
  ((h.le_iff .pt .pt).2 ⟨0, rfl⟩).elim

/-- `U0T`: one point without successor, `<` total (so `LawfulUpwardEnumerableLT` fails). -/
inductive U0T | pt deriving DecidableEq
instance : UpwardEnumerable U0T := { succ? := fun _ => none, succMany? := fun n a => if n = 0 then some a else none }
instance : LT U0T := ⟨fun _ _ => True⟩
instance : DecidableLT U0T := fun _ _ => isTrue trivial
instance : LawfulUpwardEnumerable U0T where
  ne_of_lt _ _ := fun ⟨_, h⟩ => nomatch h
  succMany?_zero _ := rfl
  succMany?_add_one n a := by cases n <;> rfl
instance : Rxi.IsAlwaysFinite U0T := ⟨fun _ => ⟨1, rfl⟩⟩
theorem U0T.not_LLT : ¬ LawfulUpwardEnumerableLT U0T := fun h => by
  obtain ⟨_, hn⟩ := (h.lt_iff .pt .pt).1 trivial; exact nomatch hn

/-- `U0N`: one point without successor, `least? = none` (so `LawfulUpwardEnumerableLeast?` fails). -/
inductive U0N | pt deriving DecidableEq
instance : UpwardEnumerable U0N := { succ? := fun _ => none, succMany? := fun n a => if n = 0 then some a else none }
instance : Least? U0N := ⟨none⟩
instance : LawfulUpwardEnumerable U0N where
  ne_of_lt _ _ := fun ⟨_, h⟩ => nomatch h
  succMany?_zero _ := rfl
  succMany?_add_one n a := by cases n <;> rfl
instance : Rxi.IsAlwaysFinite U0N := ⟨fun _ => ⟨1, rfl⟩⟩
theorem U0N.not_LLeast : ¬ LawfulUpwardEnumerableLeast? U0N := fun h => by
  obtain ⟨_, h1, _⟩ := h.least?_le .pt; exact nomatch h1

theorem Nat.not_RxiF : ¬ Rxi.IsAlwaysFinite Nat := fun h => by
  obtain ⟨n, hn⟩ := h.finite 0
  simp [UpwardEnumerable.succMany?] at hn

theorem rxcF {α : Type u} [UpwardEnumerable α] [LE α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] : Rxc.IsAlwaysFinite α := by
  constructor
  intro init hi
  by_cases h : init ≤ hi
  · obtain ⟨k, hk⟩ := (LawfulUpwardEnumerableLE.le_iff init hi).1 h
    refine ⟨k + 1, ?_⟩
    rw [LawfulUpwardEnumerable.succMany?_add_one, hk]
    cases hs : UpwardEnumerable.succ? hi with
    | none => simp [hs]
    | some y =>
      simp only [Option.bind_some, hs, Option.elim_some]
      intro hy
      obtain ⟨j, hj⟩ := (LawfulUpwardEnumerableLE.le_iff y hi).1 hy
      apply LawfulUpwardEnumerable.ne_of_lt hi hi _ rfl
      exact ⟨j, by rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs]; exact hj⟩
  · exact ⟨0, by simp [LawfulUpwardEnumerable.succMany?_zero, h]⟩

theorem rxoF {α : Type u} [UpwardEnumerable α] [LT α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] : Rxo.IsAlwaysFinite α := by
  constructor
  intro init hi
  by_cases h : init < hi
  · obtain ⟨k, hk⟩ := (LawfulUpwardEnumerableLT.lt_iff init hi).1 h
    refine ⟨k + 1, ?_⟩
    rw [hk]
    simp only [Option.elim_some]
    intro hh
    exact LawfulUpwardEnumerable.ne_of_lt hi hi ((LawfulUpwardEnumerableLT.lt_iff hi hi).1 hh) rfl
  · exact ⟨0, by simp [LawfulUpwardEnumerable.succMany?_zero, h]⟩


/-! ## Iterator and loop models -/

/-- Triples in `Id` with precondition `True`. -/
theorem trip_of {α : Type} {x : Id α} {p : α → Prop} (h : p x.run) :
    Triple x ⌜True⌝ (fun r => ⌜p r⌝, ExceptConds.false) := by
  simp [Triple, wp]; exact h
theorem of_trip {α : Type} {x : Id α} {p : α → Prop}
    (h : Triple x ⌜True⌝ (fun r => ⌜p r⌝, ExceptConds.false)) : p x.run := by
  simpa [Triple, wp] using h

theorem acc_not_self {α : Sort _} {r : α → α → Prop} {x : α} (h : Acc r x) : ¬ r x x := by
  induction h with | intro x _ ih => exact fun hxx => ih x hxx hxx

structure AD where
  u : Unit
instance AD.inst {m : Type → Type} [Pure m] : Iterator AD m Nat where
  IsPlausibleStep it s := s = .skip it ∨ ∃ n, s = .yield it n
  step it := pure (.deflate ⟨.skip it, Or.inl rfl⟩)
abbrev AD.it : Iter (α := AD) Nat := ⟨⟨()⟩⟩
theorem AD.not_wf {m : Type → Type} [Monad m] {γ : Type} [Nonempty γ] (Pl : Nat → γ → ForInStep γ → Prop) :
    ¬ IteratorLoop.WellFounded AD m Pl := fun wf =>
  acc_not_self (wf.apply (⟨⟨()⟩⟩, Classical.ofNonempty)) (Or.inr ⟨Or.inl rfl, rfl⟩)
theorem AD.out {m : Type → Type} [Monad m] (it : IterM (α := AD) m Nat) (n : Nat) : it.IsPlausibleIndirectOutput n :=
  .direct ⟨it, Or.inr ⟨n, rfl⟩⟩

/-- Loop that returns `init` without running the body. -/
def NoLoop {α β : Type} {m n : Type → Type} [Iterator α m β] [Pure n] : IteratorLoop α m n where
  forIn _ _ _ _ init _ := pure init

def ADLoop (k : Nat) {m n : Type → Type} [Monad m] [Functor n] : IteratorLoop AD m n where
  forIn _ γ _ it init f := (fun r => r.val.value) <$> f k (AD.out it k) init

theorem NoLoop.lawfulAD {m n : Type → Type} [Monad m] [Monad n] :
    @LawfulIteratorLoop _ AD m n _ _ _ (NoLoop (n := n)) :=
  @LawfulIteratorLoop.mk _ AD m n _ _ _ (NoLoop (n := n)) (fun _ _ _ _ init Pl wf _ => absurd wf (@AD.not_wf m _ _ ⟨init⟩ Pl))
theorem ADLoop.lawful (k : Nat) {m n : Type → Type} [Monad m] [Monad n] :
    @LawfulIteratorLoop _ AD m n _ _ _ (ADLoop k (n := n)) :=
  @LawfulIteratorLoop.mk _ AD m n _ _ _ (ADLoop k (n := n)) (fun _ _ _ _ init Pl wf _ => absurd wf (@AD.not_wf m _ _ ⟨init⟩ Pl))

/-- Finite iterator: state `true` may yield any `n` (and yields `0`), then state `false` is done. -/
structure FD where
  b : Bool
instance FD.inst {m : Type → Type} [Pure m] : Iterator FD m Nat where
  IsPlausibleStep it s := (it.internalState.b = true ∧ ∃ n, s = .yield ⟨⟨false⟩⟩ n) ∨
    (it.internalState.b = false ∧ s = .done)
  step it := match h : it.internalState.b with
    | true => pure (.deflate ⟨.yield ⟨⟨false⟩⟩ 0, Or.inl ⟨rfl, 0, rfl⟩⟩)
    | false => pure (.deflate ⟨.done, Or.inr ⟨rfl, rfl⟩⟩)
theorem FD.acc_false {m : Type → Type} [Pure m] : Acc (IterM.IsPlausibleSuccessorOf (α := FD) (m := m)) ⟨⟨false⟩⟩ :=
  ⟨_, fun _ ⟨s, hs, hp⟩ => by
    rcases hp with ⟨h, _⟩ | ⟨_, rfl⟩
    · exact nomatch h
    · exact nomatch hs⟩
instance FD.finite {m : Type → Type} [Pure m] : Finite FD m :=
  ⟨⟨fun it => ⟨_, fun it' ⟨s, hs, hp⟩ => by
    rcases hp with ⟨_, n, rfl⟩ | ⟨_, rfl⟩
    · cases hs; exact FD.acc_false
    · exact nomatch hs⟩⟩⟩
theorem FD.out {m : Type → Type} [Pure m] (it : IterM (α := FD) m Nat) (h : it.internalState.b = true) (n : Nat) :
    it.IsPlausibleIndirectOutput n :=
  .direct ⟨⟨⟨false⟩⟩, Or.inl ⟨h, n, rfl⟩⟩
/-- Not lawful: in state `true` runs the body once on `k`, else returns `init`. -/
def FDLoop (k : Nat) {m n : Type → Type} [Monad m] [Monad n] : IteratorLoop FD m n where
  forIn _ γ _ it init f := if h : it.internalState.b = true then
    (fun r => r.val.value) <$> f k (FD.out it h k) init else pure init

theorem trip_ofS {α : Type} {x : StateT Unit Id α} {p : α → Prop} (h : p (x.run ()).1) :
    Triple x ⌜True⌝ (fun r => ⌜p r⌝, ExceptConds.false) := by
  simp [Triple, wp]; exact fun _ => h
theorem of_tripS {α : Type} {x : StateT Unit Id α} {p : α → Prop}
    (h : Triple x ⌜True⌝ (fun r => ⌜p r⌝, ExceptConds.false)) : p (x.run ()).1 := by
  simp [Triple, wp] at h; exact h ()

/-- Slice types whose iterators are the list iterator over `[0]` resp. `AD`. -/
structure SL
structure SA
instance : ToIterator (Slice SL) Id (Types.ListIterator Nat) Nat := ⟨fun _ => [0].iterM Id⟩
instance : ToIterator (Slice SA) Id AD Nat := ⟨fun _ => ⟨⟨()⟩⟩⟩
theorem SL.toList : (⟨⟨⟩⟩ : Slice SL).toList = [0] := by
  first
  | exact (List.toList_iter (l := [0]))
  | (simp only [Slice.toList, Slice.Internal.iter]; exact List.toList_iter (l := [0]))
  | (simp [Slice.toList, Slice.Internal.iter, ToIterator.iter, ToIterator.iterM]; done)


/-! ## Verdicts -/

-- `List.Cursor.ext` (idx 4): removable; with equal suffixes the prefixes agree, since both append to `l`.
theorem Cursor_ext_4 : drop% List.Cursor.ext 4 := by
  intro α l x y h
  have hx := x.property; have hy := y.property
  ext1
  · have e := hx.trans hy.symm; rw [h] at e; exact List.append_cancel_right e
  · exact h

-- `List.Cursor.ext` (idx 5): removable; with equal prefixes the suffixes agree, since both append to `l`.
theorem Cursor_ext_5 : drop% List.Cursor.ext 5 := by
  intro α l x y h
  have hx := x.property; have hy := y.property
  ext1
  · exact h
  · have e := hx.trans hy.symm; rw [h] at e; exact List.append_cancel_left e


-- `Std.Do.Spec.pure'` (idx 8): necessary; in Id with precondition True and postcondition False the triple fails
theorem purep_8 : ¬ drop0% Std.Do.Spec.pure' 8 := fun H => by
  have := H (m := Id) (a := 0) (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.bind'` (idx 10): necessary; in Id with precondition True and postcondition False the triple fails
theorem bindp_10 : ¬ drop0% Std.Do.Spec.bind' 10 := fun H => by
  have := H (m := Id) (x := (pure 0 : Id Nat)) (f := fun _ => (pure 0 : Id Nat)) (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.map'` (idx 10): necessary; in Id with precondition True and postcondition False the triple fails
theorem mapp_10 : ¬ drop0% Std.Do.Spec.map' 10 := fun H => by
  have := H (m := Id) (x := (pure 0 : Id Nat)) (f := id) (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.seq'` (idx 10): necessary; in Id with precondition True and postcondition False the triple fails
theorem seqp_10 : ¬ drop0% Std.Do.Spec.seq' 10 := fun H => by
  have := H (m := Id) (x := (pure id : Id (Nat → Nat))) (y := (pure 0 : Id Nat)) (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.forIn'_rcc` (idx 9, dependent): removable; derivable: LawfulUpwardEnumerable with LawfulUpwardEnumerableLE/LT (other binders) implies Rxc/Rxo.IsAlwaysFinite (an infinite chain below hi would reach hi and then a cycle, contradicting ne_of_lt)
theorem forInp_rcc_9 : indep% Std.Do.Spec.forIn'_rcc 9 := by
  intros; exact rxcF

-- `Std.Do.Spec.forIn'_rcc` (idx 10, dependent): necessary; M0 (one point, succMany? constantly none) satisfies the other instance binders but not this class
theorem forInp_rcc_10 : ¬ indep0% Std.Do.Spec.forIn'_rcc 10 := fun H => by
  first
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rcc.mk .pt .pt) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rcc.mk .pt .pt) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rcc.mk .pt .pt) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_rcc` (idx 11, dependent): necessary; NLE (Nat with a ≤ b := a ≤ b + 1) satisfies the other instance binders but not this class
theorem forInp_rcc_11 : ¬ indep0% Std.Do.Spec.forIn'_rcc 11 := fun H => by
  first
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Rcc.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Rcc.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Rcc.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_rcc` (idx 16): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forInp_rcc_16 : ¬ drop0% Std.Do.Spec.forIn'_rcc 16 := fun H => by
  have := H (m := Id) (α := Nat) (xs := Rcc.mk 0 0) (init := ()) (f := fun _ _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this

-- `Std.Do.Spec.forIn_rcc` (idx 9, dependent): removable; derivable: LawfulUpwardEnumerable with LawfulUpwardEnumerableLE/LT (other binders) implies Rxc/Rxo.IsAlwaysFinite (an infinite chain below hi would reach hi and then a cycle, contradicting ne_of_lt)
theorem forIn_rcc_9 : indep% Std.Do.Spec.forIn_rcc 9 := by
  intros; exact rxcF

-- `Std.Do.Spec.forIn_rcc` (idx 10, dependent): necessary; M0 (one point, succMany? constantly none) satisfies the other instance binders but not this class
theorem forIn_rcc_10 : ¬ indep0% Std.Do.Spec.forIn_rcc 10 := fun H => by
  first
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rcc.mk .pt .pt) (init := ()) (f := fun _ b => pure (.done b)))
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rcc.mk .pt .pt) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rcc.mk .pt .pt) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_rcc` (idx 11, dependent): necessary; NLE (Nat with a ≤ b := a ≤ b + 1) satisfies the other instance binders but not this class
theorem forIn_rcc_11 : ¬ indep0% Std.Do.Spec.forIn_rcc 11 := fun H => by
  first
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Rcc.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ b => pure (.done b)))
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Rcc.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Rcc.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_rcc` (idx 16): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forIn_rcc_16 : ¬ drop0% Std.Do.Spec.forIn_rcc 16 := fun H => by
  have := H (m := Id) (α := Nat) (xs := Rcc.mk 0 0) (init := ()) (f := fun _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this

-- `Std.Do.Spec.forIn'_rco` (idx 10, dependent): removable; derivable: LawfulUpwardEnumerable with LawfulUpwardEnumerableLE/LT (other binders) implies Rxc/Rxo.IsAlwaysFinite (an infinite chain below hi would reach hi and then a cycle, contradicting ne_of_lt)
theorem forInp_rco_10 : indep% Std.Do.Spec.forIn'_rco 10 := by
  intros; exact rxoF

-- `Std.Do.Spec.forIn'_rco` (idx 11, dependent): necessary; M0 (one point, succMany? constantly none) satisfies the other instance binders but not this class
theorem forInp_rco_11 : ¬ indep0% Std.Do.Spec.forIn'_rco 11 := fun H => by
  first
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rco.mk .pt .pt) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rco.mk .pt .pt) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rco.mk .pt .pt) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_rco` (idx 12, dependent): necessary; NLE (Nat with a ≤ b := a ≤ b + 1) satisfies the other instance binders but not this class
theorem forInp_rco_12 : ¬ indep0% Std.Do.Spec.forIn'_rco 12 := fun H => by
  first
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Rco.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Rco.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Rco.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_rco` (idx 13, dependent): necessary; NLT (Nat with a < b := a < b + 1) satisfies the other instance binders but not this class
theorem forInp_rco_13 : ¬ indep0% Std.Do.Spec.forIn'_rco 13 := fun H => by
  first
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Rco.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Rco.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Rco.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_rco` (idx 18): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forInp_rco_18 : ¬ drop0% Std.Do.Spec.forIn'_rco 18 := fun H => by
  have := H (m := Id) (α := Nat) (xs := Rco.mk 0 1) (init := ()) (f := fun _ _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this

-- `Std.Do.Spec.forIn_rco` (idx 10, dependent): removable; derivable: LawfulUpwardEnumerable with LawfulUpwardEnumerableLE/LT (other binders) implies Rxc/Rxo.IsAlwaysFinite (an infinite chain below hi would reach hi and then a cycle, contradicting ne_of_lt)
theorem forIn_rco_10 : indep% Std.Do.Spec.forIn_rco 10 := by
  intros; exact rxoF

-- `Std.Do.Spec.forIn_rco` (idx 11, dependent): necessary; M0 (one point, succMany? constantly none) satisfies the other instance binders but not this class
theorem forIn_rco_11 : ¬ indep0% Std.Do.Spec.forIn_rco 11 := fun H => by
  first
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rco.mk .pt .pt) (init := ()) (f := fun _ b => pure (.done b)))
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rco.mk .pt .pt) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rco.mk .pt .pt) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_rco` (idx 12, dependent): necessary; NLE (Nat with a ≤ b := a ≤ b + 1) satisfies the other instance binders but not this class
theorem forIn_rco_12 : ¬ indep0% Std.Do.Spec.forIn_rco 12 := fun H => by
  first
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Rco.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ b => pure (.done b)))
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Rco.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Rco.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_rco` (idx 13, dependent): necessary; NLT (Nat with a < b := a < b + 1) satisfies the other instance binders but not this class
theorem forIn_rco_13 : ¬ indep0% Std.Do.Spec.forIn_rco 13 := fun H => by
  first
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Rco.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ b => pure (.done b)))
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Rco.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Rco.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_rco` (idx 18): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forIn_rco_18 : ¬ drop0% Std.Do.Spec.forIn_rco 18 := fun H => by
  have := H (m := Id) (α := Nat) (xs := Rco.mk 0 1) (init := ()) (f := fun _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this

-- `Std.Do.Spec.forIn'_rci` (idx 8, dependent): necessary; Nat (lawful, but Rxi ranges over Nat are infinite) satisfies the other instance binders but not this class
theorem forInp_rci_8 : ¬ indep0% Std.Do.Spec.forIn'_rci 8 := fun H => by
  first
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Rci.mk 0) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Rci.mk 0) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Rci.mk 0) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_rci` (idx 9, dependent): necessary; M0 (one point, succMany? constantly none) satisfies the other instance binders but not this class
theorem forInp_rci_9 : ¬ indep0% Std.Do.Spec.forIn'_rci 9 := fun H => by
  first
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rci.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rci.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rci.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_rci` (idx 10, dependent): necessary; U0F (one point, ≤ empty) satisfies the other instance binders but not this class
theorem forInp_rci_10 : ¬ indep0% Std.Do.Spec.forIn'_rci 10 := fun H => by
  first
  | exact U0F.not_LLE (H (α := U0F) (m := Id) (β := Unit) (xs := Rci.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact U0F.not_LLE (H (α := U0F) (m := Id) (β := Unit) (xs := Rci.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact U0F.not_LLE (H (α := U0F) (m := Id) (β := Unit) (xs := Rci.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_rci` (idx 15): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forInp_rci_15 : ¬ drop0% Std.Do.Spec.forIn'_rci 15 := fun H => by
  have := H (m := Id) (α := Fin 2) (xs := Rci.mk 0) (init := ()) (f := fun _ _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this
  exact List.ne_nil_of_mem (Rci.mem_toList_iff_mem.2 (show (0 : Fin 2) ∈ Rci.mk 0 from Fin.le_refl _)) this

-- `Std.Do.Spec.forIn_rci` (idx 8, dependent): necessary; Nat (lawful, but Rxi ranges over Nat are infinite) satisfies the other instance binders but not this class
theorem forIn_rci_8 : ¬ indep0% Std.Do.Spec.forIn_rci 8 := fun H => by
  first
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Rci.mk 0) (init := ()) (f := fun _ b => pure (.done b)))
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Rci.mk 0) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Rci.mk 0) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_rci` (idx 9, dependent): necessary; M0 (one point, succMany? constantly none) satisfies the other instance binders but not this class
theorem forIn_rci_9 : ¬ indep0% Std.Do.Spec.forIn_rci 9 := fun H => by
  first
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rci.mk .pt) (init := ()) (f := fun _ b => pure (.done b)))
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rci.mk .pt) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Rci.mk .pt) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_rci` (idx 10, dependent): necessary; U0F (one point, ≤ empty) satisfies the other instance binders but not this class
theorem forIn_rci_10 : ¬ indep0% Std.Do.Spec.forIn_rci 10 := fun H => by
  first
  | exact U0F.not_LLE (H (α := U0F) (m := Id) (β := Unit) (xs := Rci.mk .pt) (init := ()) (f := fun _ b => pure (.done b)))
  | exact U0F.not_LLE (H (α := U0F) (m := Id) (β := Unit) (xs := Rci.mk .pt) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact U0F.not_LLE (H (α := U0F) (m := Id) (β := Unit) (xs := Rci.mk .pt) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_rci` (idx 15): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forIn_rci_15 : ¬ drop0% Std.Do.Spec.forIn_rci 15 := fun H => by
  have := H (m := Id) (α := Fin 2) (xs := Rci.mk 0) (init := ()) (f := fun _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this
  exact List.ne_nil_of_mem (Rci.mem_toList_iff_mem.2 (show (0 : Fin 2) ∈ Rci.mk 0 from Fin.le_refl _)) this

-- `Std.Do.Spec.forIn'_roc` (idx 10, dependent): removable; derivable: LawfulUpwardEnumerable with LawfulUpwardEnumerableLE/LT (other binders) implies Rxc/Rxo.IsAlwaysFinite (an infinite chain below hi would reach hi and then a cycle, contradicting ne_of_lt)
theorem forInp_roc_10 : indep% Std.Do.Spec.forIn'_roc 10 := by
  intros; exact rxcF

-- `Std.Do.Spec.forIn'_roc` (idx 11, dependent): necessary; M0 (one point, succMany? constantly none) satisfies the other instance binders but not this class
theorem forInp_roc_11 : ¬ indep0% Std.Do.Spec.forIn'_roc 11 := fun H => by
  first
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roc.mk .pt .pt) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roc.mk .pt .pt) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roc.mk .pt .pt) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_roc` (idx 12, dependent): necessary; NLE (Nat with a ≤ b := a ≤ b + 1) satisfies the other instance binders but not this class
theorem forInp_roc_12 : ¬ indep0% Std.Do.Spec.forIn'_roc 12 := fun H => by
  first
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Roc.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Roc.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Roc.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_roc` (idx 13, dependent): necessary; NLT (Nat with a < b := a < b + 1) satisfies the other instance binders but not this class
theorem forInp_roc_13 : ¬ indep0% Std.Do.Spec.forIn'_roc 13 := fun H => by
  first
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Roc.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Roc.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Roc.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_roc` (idx 18): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forInp_roc_18 : ¬ drop0% Std.Do.Spec.forIn'_roc 18 := fun H => by
  have := H (m := Id) (α := Nat) (xs := Roc.mk 0 1) (init := ()) (f := fun _ _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this

-- `Std.Do.Spec.forIn_roc` (idx 10, dependent): removable; derivable: LawfulUpwardEnumerable with LawfulUpwardEnumerableLE/LT (other binders) implies Rxc/Rxo.IsAlwaysFinite (an infinite chain below hi would reach hi and then a cycle, contradicting ne_of_lt)
theorem forIn_roc_10 : indep% Std.Do.Spec.forIn_roc 10 := by
  intros; exact rxcF

-- `Std.Do.Spec.forIn_roc` (idx 11, dependent): necessary; M0 (one point, succMany? constantly none) satisfies the other instance binders but not this class
theorem forIn_roc_11 : ¬ indep0% Std.Do.Spec.forIn_roc 11 := fun H => by
  first
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roc.mk .pt .pt) (init := ()) (f := fun _ b => pure (.done b)))
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roc.mk .pt .pt) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roc.mk .pt .pt) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_roc` (idx 12, dependent): necessary; NLE (Nat with a ≤ b := a ≤ b + 1) satisfies the other instance binders but not this class
theorem forIn_roc_12 : ¬ indep0% Std.Do.Spec.forIn_roc 12 := fun H => by
  first
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Roc.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ b => pure (.done b)))
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Roc.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Roc.mk (NLE.pt 0) (NLE.pt 0)) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_roc` (idx 13, dependent): necessary; NLT (Nat with a < b := a < b + 1) satisfies the other instance binders but not this class
theorem forIn_roc_13 : ¬ indep0% Std.Do.Spec.forIn_roc 13 := fun H => by
  first
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Roc.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ b => pure (.done b)))
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Roc.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Roc.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_roc` (idx 18): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forIn_roc_18 : ¬ drop0% Std.Do.Spec.forIn_roc 18 := fun H => by
  have := H (m := Id) (α := Nat) (xs := Roc.mk 0 1) (init := ()) (f := fun _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this

-- `Std.Do.Spec.forIn'_roo` (idx 9, dependent): removable; derivable: LawfulUpwardEnumerable with LawfulUpwardEnumerableLE/LT (other binders) implies Rxc/Rxo.IsAlwaysFinite (an infinite chain below hi would reach hi and then a cycle, contradicting ne_of_lt)
theorem forInp_roo_9 : indep% Std.Do.Spec.forIn'_roo 9 := by
  intros; exact rxoF

-- `Std.Do.Spec.forIn'_roo` (idx 10, dependent): necessary; M0 (one point, succMany? constantly none) satisfies the other instance binders but not this class
theorem forInp_roo_10 : ¬ indep0% Std.Do.Spec.forIn'_roo 10 := fun H => by
  first
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roo.mk .pt .pt) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roo.mk .pt .pt) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roo.mk .pt .pt) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_roo` (idx 11, dependent): necessary; NLT (Nat with a < b := a < b + 1) satisfies the other instance binders but not this class
theorem forInp_roo_11 : ¬ indep0% Std.Do.Spec.forIn'_roo 11 := fun H => by
  first
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Roo.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Roo.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Roo.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_roo` (idx 16): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forInp_roo_16 : ¬ drop0% Std.Do.Spec.forIn'_roo 16 := fun H => by
  have := H (m := Id) (α := Nat) (xs := Roo.mk 0 2) (init := ()) (f := fun _ _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this

-- `Std.Do.Spec.forIn_roo` (idx 9, dependent): removable; derivable: LawfulUpwardEnumerable with LawfulUpwardEnumerableLE/LT (other binders) implies Rxc/Rxo.IsAlwaysFinite (an infinite chain below hi would reach hi and then a cycle, contradicting ne_of_lt)
theorem forIn_roo_9 : indep% Std.Do.Spec.forIn_roo 9 := by
  intros; exact rxoF

-- `Std.Do.Spec.forIn_roo` (idx 10, dependent): necessary; M0 (one point, succMany? constantly none) satisfies the other instance binders but not this class
theorem forIn_roo_10 : ¬ indep0% Std.Do.Spec.forIn_roo 10 := fun H => by
  first
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roo.mk .pt .pt) (init := ()) (f := fun _ b => pure (.done b)))
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roo.mk .pt .pt) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roo.mk .pt .pt) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_roo` (idx 11, dependent): necessary; NLT (Nat with a < b := a < b + 1) satisfies the other instance binders but not this class
theorem forIn_roo_11 : ¬ indep0% Std.Do.Spec.forIn_roo 11 := fun H => by
  first
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Roo.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ b => pure (.done b)))
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Roo.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Roo.mk (NLT.pt 0) (NLT.pt 0)) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_roo` (idx 16): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forIn_roo_16 : ¬ drop0% Std.Do.Spec.forIn_roo 16 := fun H => by
  have := H (m := Id) (α := Nat) (xs := Roo.mk 0 2) (init := ()) (f := fun _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this

-- `Std.Do.Spec.forIn'_roi` (idx 9, dependent): necessary; Nat (lawful, but Rxi ranges over Nat are infinite) satisfies the other instance binders but not this class
theorem forInp_roi_9 : ¬ indep0% Std.Do.Spec.forIn'_roi 9 := fun H => by
  first
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Roi.mk 0) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Roi.mk 0) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Roi.mk 0) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_roi` (idx 10, dependent): necessary; M0 (one point, succMany? constantly none) satisfies the other instance binders but not this class
theorem forInp_roi_10 : ¬ indep0% Std.Do.Spec.forIn'_roi 10 := fun H => by
  first
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roi.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roi.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roi.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_roi` (idx 11, dependent): necessary; U0T (one point, < total) satisfies the other instance binders but not this class
theorem forInp_roi_11 : ¬ indep0% Std.Do.Spec.forIn'_roi 11 := fun H => by
  first
  | exact U0T.not_LLT (H (α := U0T) (m := Id) (β := Unit) (xs := Roi.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact U0T.not_LLT (H (α := U0T) (m := Id) (β := Unit) (xs := Roi.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact U0T.not_LLT (H (α := U0T) (m := Id) (β := Unit) (xs := Roi.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_roi` (idx 16): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forInp_roi_16 : ¬ drop0% Std.Do.Spec.forIn'_roi 16 := fun H => by
  have := H (m := Id) (α := Fin 2) (xs := Roi.mk 0) (init := ()) (f := fun _ _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this
  exact List.ne_nil_of_mem (Roi.mem_toList_iff_mem.2 (show (1 : Fin 2) ∈ Roi.mk 0 from by decide)) this

-- `Std.Do.Spec.forIn_roi` (idx 9, dependent): necessary; Nat (lawful, but Rxi ranges over Nat are infinite) satisfies the other instance binders but not this class
theorem forIn_roi_9 : ¬ indep0% Std.Do.Spec.forIn_roi 9 := fun H => by
  first
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Roi.mk 0) (init := ()) (f := fun _ b => pure (.done b)))
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Roi.mk 0) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Roi.mk 0) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_roi` (idx 10, dependent): necessary; M0 (one point, succMany? constantly none) satisfies the other instance binders but not this class
theorem forIn_roi_10 : ¬ indep0% Std.Do.Spec.forIn_roi 10 := fun H => by
  first
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roi.mk .pt) (init := ()) (f := fun _ b => pure (.done b)))
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roi.mk .pt) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact M0.not_LUE (H (α := M0) (m := Id) (β := Unit) (xs := Roi.mk .pt) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_roi` (idx 11, dependent): necessary; U0T (one point, < total) satisfies the other instance binders but not this class
theorem forIn_roi_11 : ¬ indep0% Std.Do.Spec.forIn_roi 11 := fun H => by
  first
  | exact U0T.not_LLT (H (α := U0T) (m := Id) (β := Unit) (xs := Roi.mk .pt) (init := ()) (f := fun _ b => pure (.done b)))
  | exact U0T.not_LLT (H (α := U0T) (m := Id) (β := Unit) (xs := Roi.mk .pt) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact U0T.not_LLT (H (α := U0T) (m := Id) (β := Unit) (xs := Roi.mk .pt) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_roi` (idx 16): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forIn_roi_16 : ¬ drop0% Std.Do.Spec.forIn_roi 16 := fun H => by
  have := H (m := Id) (α := Fin 2) (xs := Roi.mk 0) (init := ()) (f := fun _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this
  exact List.ne_nil_of_mem (Roi.mem_toList_iff_mem.2 (show (1 : Fin 2) ∈ Roi.mk 0 from by decide)) this

-- `Std.Do.Spec.forIn'_ric` (idx 10, dependent): removable; derivable: LawfulUpwardEnumerable with LawfulUpwardEnumerableLE/LT (other binders) implies Rxc/Rxo.IsAlwaysFinite (an infinite chain below hi would reach hi and then a cycle, contradicting ne_of_lt)
theorem forInp_ric_10 : indep% Std.Do.Spec.forIn'_ric 10 := by
  intros; exact rxcF

-- `Std.Do.Spec.forIn'_ric` (idx 11, dependent): necessary; U1 (one point, succMany? 1 = none although succ? = some) satisfies the other instance binders but not this class
theorem forInp_ric_11 : ¬ indep0% Std.Do.Spec.forIn'_ric 11 := fun H => by
  first
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Ric.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Ric.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Ric.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_ric` (idx 12, dependent): necessary; NLeast (Nat with least? = some 1) satisfies the other instance binders but not this class
theorem forInp_ric_12 : ¬ indep0% Std.Do.Spec.forIn'_ric 12 := fun H => by
  first
  | exact NLeast.not_LLeast (H (α := NLeast) (m := Id) (β := Unit) (xs := Ric.mk (NLeast.pt 1)) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact NLeast.not_LLeast (H (α := NLeast) (m := Id) (β := Unit) (xs := Ric.mk (NLeast.pt 1)) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLeast.not_LLeast (H (α := NLeast) (m := Id) (β := Unit) (xs := Ric.mk (NLeast.pt 1)) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_ric` (idx 13, dependent): necessary; NLE (Nat with a ≤ b := a ≤ b + 1) satisfies the other instance binders but not this class
theorem forInp_ric_13 : ¬ indep0% Std.Do.Spec.forIn'_ric 13 := fun H => by
  first
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Ric.mk (NLE.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Ric.mk (NLE.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Ric.mk (NLE.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_ric` (idx 18): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forInp_ric_18 : ¬ drop0% Std.Do.Spec.forIn'_ric 18 := fun H => by
  have := H (m := Id) (α := Nat) (xs := Ric.mk 0) (init := ()) (f := fun _ _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this

-- `Std.Do.Spec.forIn_ric` (idx 10, dependent): removable; derivable: LawfulUpwardEnumerable with LawfulUpwardEnumerableLE/LT (other binders) implies Rxc/Rxo.IsAlwaysFinite (an infinite chain below hi would reach hi and then a cycle, contradicting ne_of_lt)
theorem forIn_ric_10 : indep% Std.Do.Spec.forIn_ric 10 := by
  intros; exact rxcF

-- `Std.Do.Spec.forIn_ric` (idx 11, dependent): necessary; U1 (one point, succMany? 1 = none although succ? = some) satisfies the other instance binders but not this class
theorem forIn_ric_11 : ¬ indep0% Std.Do.Spec.forIn_ric 11 := fun H => by
  first
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Ric.mk .pt) (init := ()) (f := fun _ b => pure (.done b)))
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Ric.mk .pt) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Ric.mk .pt) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_ric` (idx 12, dependent): necessary; NLeast (Nat with least? = some 1) satisfies the other instance binders but not this class
theorem forIn_ric_12 : ¬ indep0% Std.Do.Spec.forIn_ric 12 := fun H => by
  first
  | exact NLeast.not_LLeast (H (α := NLeast) (m := Id) (β := Unit) (xs := Ric.mk (NLeast.pt 1)) (init := ()) (f := fun _ b => pure (.done b)))
  | exact NLeast.not_LLeast (H (α := NLeast) (m := Id) (β := Unit) (xs := Ric.mk (NLeast.pt 1)) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLeast.not_LLeast (H (α := NLeast) (m := Id) (β := Unit) (xs := Ric.mk (NLeast.pt 1)) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_ric` (idx 13, dependent): necessary; NLE (Nat with a ≤ b := a ≤ b + 1) satisfies the other instance binders but not this class
theorem forIn_ric_13 : ¬ indep0% Std.Do.Spec.forIn_ric 13 := fun H => by
  first
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Ric.mk (NLE.pt 0)) (init := ()) (f := fun _ b => pure (.done b)))
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Ric.mk (NLE.pt 0)) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLE.not_LLE (H (α := NLE) (m := Id) (β := Unit) (xs := Ric.mk (NLE.pt 0)) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_ric` (idx 18): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forIn_ric_18 : ¬ drop0% Std.Do.Spec.forIn_ric 18 := fun H => by
  have := H (m := Id) (α := Nat) (xs := Ric.mk 0) (init := ()) (f := fun _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this

-- `Std.Do.Spec.forIn'_rio` (idx 10, dependent): removable; derivable: LawfulUpwardEnumerable with LawfulUpwardEnumerableLE/LT (other binders) implies Rxc/Rxo.IsAlwaysFinite (an infinite chain below hi would reach hi and then a cycle, contradicting ne_of_lt)
theorem forInp_rio_10 : indep% Std.Do.Spec.forIn'_rio 10 := by
  intros; exact rxoF

-- `Std.Do.Spec.forIn'_rio` (idx 11, dependent): necessary; U1 (one point, succMany? 1 = none although succ? = some) satisfies the other instance binders but not this class
theorem forInp_rio_11 : ¬ indep0% Std.Do.Spec.forIn'_rio 11 := fun H => by
  first
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Rio.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Rio.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Rio.mk .pt) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_rio` (idx 12, dependent): necessary; NLeast (Nat with least? = some 1) satisfies the other instance binders but not this class
theorem forInp_rio_12 : ¬ indep0% Std.Do.Spec.forIn'_rio 12 := fun H => by
  first
  | exact NLeast.not_LLeast (H (α := NLeast) (m := Id) (β := Unit) (xs := Rio.mk (NLeast.pt 1)) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact NLeast.not_LLeast (H (α := NLeast) (m := Id) (β := Unit) (xs := Rio.mk (NLeast.pt 1)) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLeast.not_LLeast (H (α := NLeast) (m := Id) (β := Unit) (xs := Rio.mk (NLeast.pt 1)) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_rio` (idx 13, dependent): necessary; NLT (Nat with a < b := a < b + 1) satisfies the other instance binders but not this class
theorem forInp_rio_13 : ¬ indep0% Std.Do.Spec.forIn'_rio 13 := fun H => by
  first
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Rio.mk (NLT.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Rio.mk (NLT.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Rio.mk (NLT.pt 0)) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_rio` (idx 18): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forInp_rio_18 : ¬ drop0% Std.Do.Spec.forIn'_rio 18 := fun H => by
  have := H (m := Id) (α := Nat) (xs := Rio.mk 1) (init := ()) (f := fun _ _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this

-- `Std.Do.Spec.forIn_rio` (idx 10, dependent): removable; derivable: LawfulUpwardEnumerable with LawfulUpwardEnumerableLE/LT (other binders) implies Rxc/Rxo.IsAlwaysFinite (an infinite chain below hi would reach hi and then a cycle, contradicting ne_of_lt)
theorem forIn_rio_10 : indep% Std.Do.Spec.forIn_rio 10 := by
  intros; exact rxoF

-- `Std.Do.Spec.forIn_rio` (idx 11, dependent): necessary; U1 (one point, succMany? 1 = none although succ? = some) satisfies the other instance binders but not this class
theorem forIn_rio_11 : ¬ indep0% Std.Do.Spec.forIn_rio 11 := fun H => by
  first
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Rio.mk .pt) (init := ()) (f := fun _ b => pure (.done b)))
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Rio.mk .pt) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Rio.mk .pt) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_rio` (idx 12, dependent): necessary; NLeast (Nat with least? = some 1) satisfies the other instance binders but not this class
theorem forIn_rio_12 : ¬ indep0% Std.Do.Spec.forIn_rio 12 := fun H => by
  first
  | exact NLeast.not_LLeast (H (α := NLeast) (m := Id) (β := Unit) (xs := Rio.mk (NLeast.pt 1)) (init := ()) (f := fun _ b => pure (.done b)))
  | exact NLeast.not_LLeast (H (α := NLeast) (m := Id) (β := Unit) (xs := Rio.mk (NLeast.pt 1)) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLeast.not_LLeast (H (α := NLeast) (m := Id) (β := Unit) (xs := Rio.mk (NLeast.pt 1)) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_rio` (idx 13, dependent): necessary; NLT (Nat with a < b := a < b + 1) satisfies the other instance binders but not this class
theorem forIn_rio_13 : ¬ indep0% Std.Do.Spec.forIn_rio 13 := fun H => by
  first
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Rio.mk (NLT.pt 0)) (init := ()) (f := fun _ b => pure (.done b)))
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Rio.mk (NLT.pt 0)) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact NLT.not_LLT (H (α := NLT) (m := Id) (β := Unit) (xs := Rio.mk (NLT.pt 0)) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_rio` (idx 18): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forIn_rio_18 : ¬ drop0% Std.Do.Spec.forIn_rio 18 := fun H => by
  have := H (m := Id) (α := Nat) (xs := Rio.mk 1) (init := ()) (f := fun _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this

-- `Std.Do.Spec.forIn'_rii` (idx 8, dependent): necessary; Nat (lawful, but Rxi ranges over Nat are infinite) satisfies the other instance binders but not this class
theorem forInp_rii_8 : ¬ indep0% Std.Do.Spec.forIn'_rii 8 := fun H => by
  first
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_rii` (idx 9, dependent): necessary; U1 (one point, succMany? 1 = none although succ? = some) satisfies the other instance binders but not this class
theorem forInp_rii_9 : ¬ indep0% Std.Do.Spec.forIn'_rii 9 := fun H => by
  first
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_rii` (idx 10, dependent): necessary; U0N (one point, least? = none) satisfies the other instance binders but not this class
theorem forInp_rii_10 : ¬ indep0% Std.Do.Spec.forIn'_rii 10 := fun H => by
  first
  | exact U0N.not_LLeast (H (α := U0N) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ _ b => pure (.done b)))
  | exact U0N.not_LLeast (H (α := U0N) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact U0N.not_LLeast (H (α := U0N) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn'_rii` (idx 15): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forInp_rii_15 : ¬ drop0% Std.Do.Spec.forIn'_rii 15 := fun H => by
  have := H (m := Id) (α := Fin 2) (xs := Rii.mk) (init := ()) (f := fun _ _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this
  exact List.ne_nil_of_mem (Rii.mem_toList (a := (0 : Fin 2))) this

-- `Std.Do.Spec.forIn_rii` (idx 8, dependent): necessary; Nat (lawful, but Rxi ranges over Nat are infinite) satisfies the other instance binders but not this class
theorem forIn_rii_8 : ¬ indep0% Std.Do.Spec.forIn_rii 8 := fun H => by
  first
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ b => pure (.done b)))
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact Nat.not_RxiF (H (α := Nat) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_rii` (idx 9, dependent): necessary; U1 (one point, succMany? 1 = none although succ? = some) satisfies the other instance binders but not this class
theorem forIn_rii_9 : ¬ indep0% Std.Do.Spec.forIn_rii 9 := fun H => by
  first
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ b => pure (.done b)))
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact U1.not_LUE (H (α := U1) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_rii` (idx 10, dependent): necessary; U0N (one point, least? = none) satisfies the other instance binders but not this class
theorem forIn_rii_10 : ¬ indep0% Std.Do.Spec.forIn_rii 10 := fun H => by
  first
  | exact U0N.not_LLeast (H (α := U0N) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ b => pure (.done b)))
  | exact U0N.not_LLeast (H (α := U0N) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ b => pure (.done b)) ⟨fun _ => ⌜True⌝, ExceptConds.false⟩)
  | exact U0N.not_LLeast (H (α := U0N) (m := Id) (β := Unit) (xs := Rii.mk) (init := ()) (f := fun _ b => pure (.done b))
      ⟨fun _ => ⌜True⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp]))

-- `Std.Do.Spec.forIn_rii` (idx 15): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forIn_rii_15 : ¬ drop0% Std.Do.Spec.forIn_rii 15 := fun H => by
  have := H (m := Id) (α := Fin 2) (xs := Rii.mk) (init := ()) (f := fun _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this
  exact List.ne_nil_of_mem (Rii.mem_toList (a := (0 : Fin 2))) this

-- `Std.Do.Spec.forIn'_list` (idx 10): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forInp_list_10 : ¬ drop0% Std.Do.Spec.forIn'_list 10 := fun H => by
  have := H (m := Id) (xs := [0]) (init := ()) (f := fun _ _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp, List.toList_iter, List.toList_iterM, SL.toList] at this

-- `Std.Do.Spec.forIn'_list_const_inv` (idx 10): necessary; in Id over [0] with invariant b = 0 and a body returning 1: the loop result 1 violates the postcondition
theorem forInp_list_const_inv_10 : ¬ drop0% Std.Do.Spec.forIn'_list_const_inv 10 := fun H => by
  have := H (m := Id) (xs := [0]) (init := 0) (f := fun _ _ _ => pure (.done 1))
    (inv := ⟨fun b => ⌜b = 0⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this

-- `Std.Do.Spec.forIn_list` (idx 10): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forIn_list_10 : ¬ drop0% Std.Do.Spec.forIn_list 10 := fun H => by
  have := H (m := Id) (xs := [0]) (init := ()) (f := fun _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp, List.toList_iter, List.toList_iterM, SL.toList] at this

-- `Std.Do.Spec.forIn_list_const_inv` (idx 10): necessary; in Id over [0] with invariant b = 0 and a body returning 1: the loop result 1 violates the postcondition
theorem forIn_list_const_inv_10 : ¬ drop0% Std.Do.Spec.forIn_list_const_inv 10 := fun H => by
  have := H (m := Id) (xs := [0]) (init := 0) (f := fun _ _ => pure (.done 1))
    (inv := ⟨fun b => ⌜b = 0⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this

-- `Std.Do.Spec.foldlM_list` (idx 10): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem foldlM_list_10 : ¬ drop0% Std.Do.Spec.foldlM_list 10 := fun H => by
  have := H (m := Id) (xs := [0]) (init := ()) (f := fun b _ => pure b)
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp, List.toList_iter, List.toList_iterM, SL.toList] at this

-- `Std.Do.Spec.foldlM_list_const_inv` (idx 10): necessary; in Id over [0] with invariant b = 0 and a body returning 1: the loop result 1 violates the postcondition
theorem foldlM_list_const_inv_10 : ¬ drop0% Std.Do.Spec.foldlM_list_const_inv 10 := fun H => by
  have := H (m := Id) (xs := [0]) (init := 0) (f := fun _ _ => pure 1)
    (inv := ⟨fun b => ⌜b = 0⌝, ExceptConds.false⟩)
  simp [Triple, wp] at this

-- `Std.Do.Spec.forIn'_range` (idx 9): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forInp_range_9 : ¬ drop0% Std.Do.Spec.forIn'_range 9 := fun H => by
  have := H (m := Id) (xs := [0:1]) (init := ()) (f := fun _ _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp, List.toList_iter, List.toList_iterM, SL.toList] at this

-- `Std.Do.Spec.forIn_range` (idx 9): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forIn_range_9 : ¬ drop0% Std.Do.Spec.forIn_range 9 := fun H => by
  have := H (m := Id) (xs := [0:1]) (init := ()) (f := fun _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp, List.toList_iter, List.toList_iterM, SL.toList] at this

-- `Std.Do.Spec.forIn_slice` (idx 18): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forIn_slice_18 : ¬ drop0% Std.Do.Spec.forIn_slice 18 := fun H => by
  have := H (m := Id) (xs := (⟨⟨⟩⟩ : Slice SL)) (init := ()) (f := fun _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp, List.toList_iter, List.toList_iterM, SL.toList] at this

-- `Std.Do.Spec.forIn_iter` (idx 15): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forIn_iter_15 : ¬ drop0% Std.Do.Spec.forIn_iter 15 := fun H => by
  have := H (n := Id) (it := [0].iter) (init := ()) (f := fun _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp, List.toList_iter, List.toList_iterM, SL.toList] at this

-- `Std.Do.Spec.forIn_iterM_id` (idx 15): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem forIn_iterM_id_15 : ¬ drop0% Std.Do.Spec.forIn_iterM_id 15 := fun H => by
  have := H (n := Id) (it := [0].iterM Id) (init := ()) (f := fun _ b => pure (.done b))
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp, List.toList_iter, List.toList_iterM, SL.toList] at this

-- `Std.Do.Spec.foldM_iter` (idx 15): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem foldM_iter_15 : ¬ drop0% Std.Do.Spec.foldM_iter 15 := fun H => by
  have := H (n := Id) (it := [0].iter) (init := ()) (f := fun b _ => pure b)
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp, List.toList_iter, List.toList_iterM, SL.toList] at this

-- `Std.Do.Spec.foldM_iterM_id` (idx 15): necessary; in Id, invariant suffix ≠ [] on a one-element collection: true at the start, false at the end, so the conclusion fails without any evaluation
theorem foldM_iterM_id_15 : ¬ drop0% Std.Do.Spec.foldM_iterM_id 15 := fun H => by
  have := H (n := Id) (it := [0].iterM Id) (init := ()) (f := fun b _ => pure b)
    (inv := ⟨fun p => ⌜p.1.suffix ≠ []⌝, ExceptConds.false⟩)
  simp [Triple, wp, List.toList_iter, List.toList_iterM, SL.toList] at this

-- `Std.Do.Spec.forIn_slice` (idx 12): necessary; list iterator [0] with the unlawful loop NoLoop (returns init); invariant acc = cursor position, body adds one: the result 0 is not the length 1
theorem forIn_slice_12 : ¬ drop0% Std.Do.Spec.forIn_slice 12 := fun H => by
  letI : IteratorLoop (Types.ListIterator Nat) Id Id := NoLoop
  have := H (m := Id) (xs := (⟨⟨⟩⟩ : Slice SL)) (init := 0) (f := fun _ b => pure (.yield (b+1))) ⟨fun p => ⌜p.2 = p.1.prefix.length⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp])
  simp [Triple, wp, List.toList_iter, List.toList_iterM, SL.toList] at this
  exact Nat.zero_ne_one this

-- `Std.Do.Spec.forIn_slice` (idx 13): necessary; non-finite iterator AD with two (vacuously lawful) loops NoLoop/ADLoop 0; invariant acc = cursor position, body adds one: the conclusion makes the same opaque toList.length equal to 0 and 1
theorem forIn_slice_13 : ¬ drop0% Std.Do.Spec.forIn_slice 13 := fun H => by
  have e0 : (⟨⟨⟩⟩ : Slice SA).toList.length = 0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    have := H (m := Id) (xs := (⟨⟨⟩⟩ : Slice SA)) (init := 0) (f := fun _ b => pure (.yield (b+1))) ⟨fun p => ⌜p.2 = p.1.prefix.length⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp])
    simp [Triple, wp] at this; exact this.symm
  have e1 : (⟨⟨⟩⟩ : Slice SA).toList.length = 1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    have := H (m := Id) (xs := (⟨⟨⟩⟩ : Slice SA)) (init := 0) (f := fun _ b => pure (.yield (b+1))) ⟨fun p => ⌜p.2 = p.1.prefix.length⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp])
    simp [Triple, wp] at this; exact this.symm
  omega

-- `Std.Do.Spec.forIn_iter` (idx 8): necessary; non-finite iterator AD with two (vacuously lawful) loops NoLoop/ADLoop 0; invariant acc = cursor position, body adds one: the conclusion makes the same opaque toList.length equal to 0 and 1
theorem forIn_iter_8 : ¬ drop0% Std.Do.Spec.forIn_iter 8 := fun H => by
  have e0 : AD.it.toList.length = 0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    have := H (n := Id) (it := AD.it) (init := 0) (f := fun _ b => pure (.yield (b+1))) ⟨fun p => ⌜p.2 = p.1.prefix.length⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp])
    simp [Triple, wp] at this; exact this.symm
  have e1 : AD.it.toList.length = 1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    have := H (n := Id) (it := AD.it) (init := 0) (f := fun _ b => pure (.yield (b+1))) ⟨fun p => ⌜p.2 = p.1.prefix.length⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp])
    simp [Triple, wp] at this; exact this.symm
  omega

-- `Std.Do.Spec.forIn_iter` (idx 10): necessary; list iterator [0] with the unlawful loop NoLoop (returns init); invariant acc = cursor position, body adds one: the result 0 is not the length 1
theorem forIn_iter_10 : ¬ drop0% Std.Do.Spec.forIn_iter 10 := fun H => by
  letI : IteratorLoop (Types.ListIterator Nat) Id Id := NoLoop
  have := H (n := Id) (it := [0].iter) (init := 0) (f := fun _ b => pure (.yield (b+1))) ⟨fun p => ⌜p.2 = p.1.prefix.length⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp])
  simp [Triple, wp, List.toList_iter, List.toList_iterM, SL.toList] at this
  exact Nat.zero_ne_one this

-- `Std.Do.Spec.forIn_iterM_id` (idx 8): necessary; non-finite iterator AD with two (vacuously lawful) loops NoLoop/ADLoop 0; invariant acc = cursor position, body adds one: the conclusion makes the same opaque toList.length equal to 0 and 1
theorem forIn_iterM_id_8 : ¬ drop0% Std.Do.Spec.forIn_iterM_id 8 := fun H => by
  have e0 : (⟨⟨()⟩⟩ : IterM (α := AD) Id Nat).toList.run.length = 0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    have := H (n := Id) (it := (⟨⟨()⟩⟩ : IterM (α := AD) Id Nat)) (init := 0) (f := fun _ b => pure (.yield (b+1))) ⟨fun p => ⌜p.2 = p.1.prefix.length⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp])
    simp [Triple, wp] at this; exact this.symm
  have e1 : (⟨⟨()⟩⟩ : IterM (α := AD) Id Nat).toList.run.length = 1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    have := H (n := Id) (it := (⟨⟨()⟩⟩ : IterM (α := AD) Id Nat)) (init := 0) (f := fun _ b => pure (.yield (b+1))) ⟨fun p => ⌜p.2 = p.1.prefix.length⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp])
    simp [Triple, wp] at this; exact this.symm
  omega

-- `Std.Do.Spec.forIn_iterM_id` (idx 10): necessary; list iterator [0] with the unlawful loop NoLoop (returns init); invariant acc = cursor position, body adds one: the result 0 is not the length 1
theorem forIn_iterM_id_10 : ¬ drop0% Std.Do.Spec.forIn_iterM_id 10 := fun H => by
  letI : IteratorLoop (Types.ListIterator Nat) Id Id := NoLoop
  have := H (n := Id) (it := [0].iterM Id) (init := 0) (f := fun _ b => pure (.yield (b+1))) ⟨fun p => ⌜p.2 = p.1.prefix.length⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp])
  simp [Triple, wp, List.toList_iter, List.toList_iterM, SL.toList] at this
  exact Nat.zero_ne_one this

-- `Std.Do.Spec.foldM_iter` (idx 8): necessary; non-finite iterator AD with two (vacuously lawful) loops NoLoop/ADLoop 0; invariant acc = cursor position, body adds one: the conclusion makes the same opaque toList.length equal to 0 and 1
theorem foldM_iter_8 : ¬ drop0% Std.Do.Spec.foldM_iter 8 := fun H => by
  have e0 : AD.it.toList.length = 0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    have := H (n := Id) (it := AD.it) (init := 0) (f := fun b _ => pure (b+1)) ⟨fun p => ⌜p.2 = p.1.prefix.length⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp])
    simp [Triple, wp] at this; exact this.symm
  have e1 : AD.it.toList.length = 1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    have := H (n := Id) (it := AD.it) (init := 0) (f := fun b _ => pure (b+1)) ⟨fun p => ⌜p.2 = p.1.prefix.length⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp])
    simp [Triple, wp] at this; exact this.symm
  omega

-- `Std.Do.Spec.foldM_iter` (idx 10): necessary; list iterator [0] with the unlawful loop NoLoop (returns init); invariant acc = cursor position, body adds one: the result 0 is not the length 1
theorem foldM_iter_10 : ¬ drop0% Std.Do.Spec.foldM_iter 10 := fun H => by
  letI : IteratorLoop (Types.ListIterator Nat) Id Id := NoLoop
  have := H (n := Id) (it := [0].iter) (init := 0) (f := fun b _ => pure (b+1)) ⟨fun p => ⌜p.2 = p.1.prefix.length⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp])
  simp [Triple, wp, List.toList_iter, List.toList_iterM, SL.toList] at this
  exact Nat.zero_ne_one this

-- `Std.Do.Spec.foldM_iterM_id` (idx 8): necessary; non-finite iterator AD with two (vacuously lawful) loops NoLoop/ADLoop 0; invariant acc = cursor position, body adds one: the conclusion makes the same opaque toList.length equal to 0 and 1
theorem foldM_iterM_id_8 : ¬ drop0% Std.Do.Spec.foldM_iterM_id 8 := fun H => by
  have e0 : (⟨⟨()⟩⟩ : IterM (α := AD) Id Nat).toList.run.length = 0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    have := H (n := Id) (it := (⟨⟨()⟩⟩ : IterM (α := AD) Id Nat)) (init := 0) (f := fun b _ => pure (b+1)) ⟨fun p => ⌜p.2 = p.1.prefix.length⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp])
    simp [Triple, wp] at this; exact this.symm
  have e1 : (⟨⟨()⟩⟩ : IterM (α := AD) Id Nat).toList.run.length = 1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    have := H (n := Id) (it := (⟨⟨()⟩⟩ : IterM (α := AD) Id Nat)) (init := 0) (f := fun b _ => pure (b+1)) ⟨fun p => ⌜p.2 = p.1.prefix.length⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp])
    simp [Triple, wp] at this; exact this.symm
  omega

-- `Std.Do.Spec.foldM_iterM_id` (idx 10): necessary; list iterator [0] with the unlawful loop NoLoop (returns init); invariant acc = cursor position, body adds one: the result 0 is not the length 1
theorem foldM_iterM_id_10 : ¬ drop0% Std.Do.Spec.foldM_iterM_id 10 := fun H => by
  letI : IteratorLoop (Types.ListIterator Nat) Id Id := NoLoop
  have := H (n := Id) (it := [0].iterM Id) (init := 0) (f := fun b _ => pure (b+1)) ⟨fun p => ⌜p.2 = p.1.prefix.length⌝, ExceptConds.false⟩ (fun _ _ _ _ _ => by simp [Triple, wp])
  simp [Triple, wp, List.toList_iter, List.toList_iterM, SL.toList] at this
  exact Nat.zero_ne_one this

-- `Std.Do.Spec.IterM.forIn_filterMapWithPostcondition` (idx 20): necessary; non-finite base iterator AD, all monads Id; with the vacuously lawful base loops NoLoop and ADLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_filterMapWithPostcondition_20 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMapWithPostcondition 20 := fun H => by
  have h0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_filterMapWithPostcondition` (idx 22): necessary; finite base iterator FD, all monads Id; with the unlawful base loops NoLoop and FDLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_filterMapWithPostcondition_22 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMapWithPostcondition 22 := fun H => by
  have h0 := by
    letI : IteratorLoop FD Id Id := NoLoop
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop FD Id Id := FDLoop 0
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_filterMapWithPostcondition` (idx 29): necessary; all monads Id, list iterator [0], precondition True, postcondition False: the triple fails
theorem IterM_forIn_filterMapWithPostcondition_29 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMapWithPostcondition 29 := fun H => by
  have := H (m := Id) (n := Id) (o := Id) (it := [0].iterM Id) (f := fun x => pure (some x)) (init := 0) (g := fun c _ => pure (.done (c+1)))
    (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.IterM.forIn_filterMapM` (idx 22): necessary; non-finite base iterator AD, all monads Id; with the vacuously lawful base loops NoLoop and ADLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_filterMapM_22 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMapM 22 := fun H => by
  have h0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_filterMapM` (idx 24): necessary; finite base iterator FD, all monads Id; with the unlawful base loops NoLoop and FDLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_filterMapM_24 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMapM 24 := fun H => by
  have h0 := by
    letI : IteratorLoop FD Id Id := NoLoop
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop FD Id Id := FDLoop 0
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_filterMapM` (idx 31): necessary; all monads Id, list iterator [0], precondition True, postcondition False: the triple fails
theorem IterM_forIn_filterMapM_31 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMapM 31 := fun H => by
  have := H (m := Id) (n := Id) (o := Id) (it := [0].iterM Id) (f := fun x => pure (some x)) (init := 0) (g := fun c _ => pure (.done (c+1)))
    (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.IterM.forIn_filterMap` (idx 15): necessary; non-finite base iterator AD, all monads Id; with the vacuously lawful base loops NoLoop and ADLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_filterMap_15 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMap 15 := fun H => by
  have h0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (it := ⟨⟨()⟩⟩) (f := some) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (it := ⟨⟨()⟩⟩) (f := some) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_filterMap` (idx 17): necessary; finite base iterator FD, all monads Id; with the unlawful base loops NoLoop and FDLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_filterMap_17 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMap 17 := fun H => by
  have h0 := by
    letI : IteratorLoop FD Id Id := NoLoop
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (it := ⟨⟨true⟩⟩) (f := some) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop FD Id Id := FDLoop 0
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (it := ⟨⟨true⟩⟩) (f := some) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_filterMap` (idx 24): necessary; all monads Id, list iterator [0], precondition True, postcondition False: the triple fails
theorem IterM_forIn_filterMap_24 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMap 24 := fun H => by
  have := H (m := Id) (n := Id) (it := [0].iterM Id) (f := some) (init := 0) (g := fun c _ => pure (.done (c+1)))
    (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.IterM.forIn_mapWithPostcondition` (idx 20): necessary; non-finite base iterator AD, all monads Id; with the vacuously lawful base loops NoLoop and ADLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_mapWithPostcondition_20 : ¬ drop0% Std.Do.Spec.IterM.forIn_mapWithPostcondition 20 := fun H => by
  have h0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure x) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure x) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_mapWithPostcondition` (idx 22): necessary; finite base iterator FD, all monads Id; with the unlawful base loops NoLoop and FDLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_mapWithPostcondition_22 : ¬ drop0% Std.Do.Spec.IterM.forIn_mapWithPostcondition 22 := fun H => by
  have h0 := by
    letI : IteratorLoop FD Id Id := NoLoop
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure x) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop FD Id Id := FDLoop 0
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure x) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_mapWithPostcondition` (idx 29): necessary; all monads Id, list iterator [0], precondition True, postcondition False: the triple fails
theorem IterM_forIn_mapWithPostcondition_29 : ¬ drop0% Std.Do.Spec.IterM.forIn_mapWithPostcondition 29 := fun H => by
  have := H (m := Id) (n := Id) (o := Id) (it := [0].iterM Id) (f := fun x => pure x) (init := 0) (g := fun c _ => pure (.done (c+1)))
    (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.IterM.forIn_mapM` (idx 22): necessary; non-finite base iterator AD, all monads Id; with the vacuously lawful base loops NoLoop and ADLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_mapM_22 : ¬ drop0% Std.Do.Spec.IterM.forIn_mapM 22 := fun H => by
  have h0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure x) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure x) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_mapM` (idx 24): necessary; finite base iterator FD, all monads Id; with the unlawful base loops NoLoop and FDLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_mapM_24 : ¬ drop0% Std.Do.Spec.IterM.forIn_mapM 24 := fun H => by
  have h0 := by
    letI : IteratorLoop FD Id Id := NoLoop
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure x) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop FD Id Id := FDLoop 0
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure x) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_mapM` (idx 31): necessary; all monads Id, list iterator [0], precondition True, postcondition False: the triple fails
theorem IterM_forIn_mapM_31 : ¬ drop0% Std.Do.Spec.IterM.forIn_mapM 31 := fun H => by
  have := H (m := Id) (n := Id) (o := Id) (it := [0].iterM Id) (f := fun x => pure x) (init := 0) (g := fun c _ => pure (.done (c+1)))
    (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.IterM.forIn_map` (idx 15): necessary; non-finite base iterator AD, all monads Id; with the vacuously lawful base loops NoLoop and ADLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_map_15 : ¬ drop0% Std.Do.Spec.IterM.forIn_map 15 := fun H => by
  have h0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (it := ⟨⟨()⟩⟩) (f := id) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (it := ⟨⟨()⟩⟩) (f := id) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_map` (idx 17): necessary; finite base iterator FD, all monads Id; with the unlawful base loops NoLoop and FDLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_map_17 : ¬ drop0% Std.Do.Spec.IterM.forIn_map 17 := fun H => by
  have h0 := by
    letI : IteratorLoop FD Id Id := NoLoop
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (it := ⟨⟨true⟩⟩) (f := id) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop FD Id Id := FDLoop 0
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (it := ⟨⟨true⟩⟩) (f := id) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_map` (idx 24): necessary; all monads Id, list iterator [0], precondition True, postcondition False: the triple fails
theorem IterM_forIn_map_24 : ¬ drop0% Std.Do.Spec.IterM.forIn_map 24 := fun H => by
  have := H (m := Id) (n := Id) (it := [0].iterM Id) (f := id) (init := 0) (g := fun c _ => pure (.done (c+1)))
    (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.IterM.forIn_filterWithPostcondition` (idx 19): necessary; non-finite base iterator AD, all monads Id; with the vacuously lawful base loops NoLoop and ADLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_filterWithPostcondition_19 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterWithPostcondition 19 := fun H => by
  have h0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_filterWithPostcondition` (idx 21): necessary; finite base iterator FD, all monads Id; with the unlawful base loops NoLoop and FDLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_filterWithPostcondition_21 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterWithPostcondition 21 := fun H => by
  have h0 := by
    letI : IteratorLoop FD Id Id := NoLoop
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨true⟩⟩) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop FD Id Id := FDLoop 0
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨true⟩⟩) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_filterWithPostcondition` (idx 28): necessary; all monads Id, list iterator [0], precondition True, postcondition False: the triple fails
theorem IterM_forIn_filterWithPostcondition_28 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterWithPostcondition 28 := fun H => by
  have := H (m := Id) (n := Id) (o := Id) (it := [0].iterM Id) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun c _ => pure (.done (c+1)))
    (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.IterM.forIn_filterM` (idx 21): necessary; non-finite base iterator AD, all monads Id; with the vacuously lawful base loops NoLoop and ADLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_filterM_21 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterM 21 := fun H => by
  have h0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_filterM` (idx 23): necessary; finite base iterator FD, all monads Id; with the unlawful base loops NoLoop and FDLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_filterM_23 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterM 23 := fun H => by
  have h0 := by
    letI : IteratorLoop FD Id Id := NoLoop
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨true⟩⟩) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop FD Id Id := FDLoop 0
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨true⟩⟩) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_filterM` (idx 30): necessary; all monads Id, list iterator [0], precondition True, postcondition False: the triple fails
theorem IterM_forIn_filterM_30 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterM 30 := fun H => by
  have := H (m := Id) (n := Id) (o := Id) (it := [0].iterM Id) (f := fun _ => pure (ULift.up true)) (init := 0) (g := fun c _ => pure (.done (c+1)))
    (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.IterM.forIn_filter` (idx 14): necessary; non-finite base iterator AD, all monads Id; with the vacuously lawful base loops NoLoop and ADLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_filter_14 : ¬ drop0% Std.Do.Spec.IterM.forIn_filter 14 := fun H => by
  have h0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (it := ⟨⟨()⟩⟩) (f := fun _ => true) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (it := ⟨⟨()⟩⟩) (f := fun _ => true) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_filter` (idx 16): necessary; finite base iterator FD, all monads Id; with the unlawful base loops NoLoop and FDLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_forIn_filter_16 : ¬ drop0% Std.Do.Spec.IterM.forIn_filter 16 := fun H => by
  have h0 := by
    letI : IteratorLoop FD Id Id := NoLoop
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (it := ⟨⟨true⟩⟩) (f := fun _ => true) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop FD Id Id := FDLoop 0
    exact of_trip (H (α := FD) (β := Nat) (m := Id) (n := Id) (it := ⟨⟨true⟩⟩) (f := fun _ => true) (init := 0) (g := fun c _ => pure (.done (c+1)))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.forIn_filter` (idx 23): necessary; all monads Id, list iterator [0], precondition True, postcondition False: the triple fails
theorem IterM_forIn_filter_23 : ¬ drop0% Std.Do.Spec.IterM.forIn_filter 23 := fun H => by
  have := H (m := Id) (n := Id) (it := [0].iterM Id) (f := fun _ => true) (init := 0) (g := fun c _ => pure (.done (c+1)))
    (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.IterM.foldM_filterMapWithPostcondition` (idx 9): necessary; non-finite base iterator AD, all monads Id; with the vacuously lawful base loops NoLoop and ADLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_foldM_filterMapWithPostcondition_9 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMapWithPostcondition 9 := fun H => by
  have h0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.foldM_filterMapWithPostcondition` (idx 20): necessary; finite base iterator FD, o = StateT Unit Id; with the unlawful base loops NoLoop and FDLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_foldM_filterMapWithPostcondition_20 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMapWithPostcondition 20 := fun H => by
  have h0 := by
    letI : IteratorLoop FD Id Id := .defaultImplementation
    letI : IteratorLoop FD Id (StateT Unit Id) := NoLoop
    exact of_tripS (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := StateT Unit Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_ofS rfl))
  have h1 := by
    letI : IteratorLoop FD Id Id := .defaultImplementation
    letI : IteratorLoop FD Id (StateT Unit Id) := FDLoop 0
    exact of_tripS (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := StateT Unit Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_ofS rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.foldM_filterMapWithPostcondition` (idx 31): necessary; all monads Id, list iterator [0], precondition True, postcondition False: the triple fails
theorem IterM_foldM_filterMapWithPostcondition_31 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMapWithPostcondition 31 := fun H => by
  have := H (m := Id) (n := Id) (o := Id) (it := [0].iterM Id) (f := fun x => pure (some x)) (init := 0) (g := fun _ c => pure (c+1))
    (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.IterM.foldM_filterMapM` (idx 9): necessary; non-finite base iterator AD, all monads Id; with the vacuously lawful base loops NoLoop and ADLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_foldM_filterMapM_9 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMapM 9 := fun H => by
  have h0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.foldM_filterMapM` (idx 22): necessary; finite base iterator FD, o = StateT Unit Id; with the unlawful base loops NoLoop and FDLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_foldM_filterMapM_22 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMapM 22 := fun H => by
  have h0 := by
    letI : IteratorLoop FD Id Id := .defaultImplementation
    letI : IteratorLoop FD Id (StateT Unit Id) := NoLoop
    exact of_tripS (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := StateT Unit Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_ofS rfl))
  have h1 := by
    letI : IteratorLoop FD Id Id := .defaultImplementation
    letI : IteratorLoop FD Id (StateT Unit Id) := FDLoop 0
    exact of_tripS (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := StateT Unit Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure (some x)) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_ofS rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.foldM_filterMapM` (idx 33): necessary; all monads Id, list iterator [0], precondition True, postcondition False: the triple fails
theorem IterM_foldM_filterMapM_33 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMapM 33 := fun H => by
  have := H (m := Id) (n := Id) (o := Id) (it := [0].iterM Id) (f := fun x => pure (some x)) (init := 0) (g := fun _ c => pure (c+1))
    (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.IterM.foldM_mapWithPostcondition` (idx 9): necessary; non-finite base iterator AD, all monads Id; with the vacuously lawful base loops NoLoop and ADLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_foldM_mapWithPostcondition_9 : ¬ drop0% Std.Do.Spec.IterM.foldM_mapWithPostcondition 9 := fun H => by
  have h0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure x) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure x) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.foldM_mapWithPostcondition` (idx 20): necessary; finite base iterator FD, o = StateT Unit Id; with the unlawful base loops NoLoop and FDLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_foldM_mapWithPostcondition_20 : ¬ drop0% Std.Do.Spec.IterM.foldM_mapWithPostcondition 20 := fun H => by
  have h0 := by
    letI : IteratorLoop FD Id Id := .defaultImplementation
    letI : IteratorLoop FD Id (StateT Unit Id) := NoLoop
    exact of_tripS (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := StateT Unit Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure x) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_ofS rfl))
  have h1 := by
    letI : IteratorLoop FD Id Id := .defaultImplementation
    letI : IteratorLoop FD Id (StateT Unit Id) := FDLoop 0
    exact of_tripS (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := StateT Unit Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure x) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_ofS rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.foldM_mapWithPostcondition` (idx 31): necessary; all monads Id, list iterator [0], precondition True, postcondition False: the triple fails
theorem IterM_foldM_mapWithPostcondition_31 : ¬ drop0% Std.Do.Spec.IterM.foldM_mapWithPostcondition 31 := fun H => by
  have := H (m := Id) (n := Id) (o := Id) (it := [0].iterM Id) (f := fun x => pure x) (init := 0) (g := fun _ c => pure (c+1))
    (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this

-- `Std.Do.Spec.IterM.foldM_mapM` (idx 9): necessary; non-finite base iterator AD, all monads Id; with the vacuously lawful base loops NoLoop and ADLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_foldM_mapM_9 : ¬ drop0% Std.Do.Spec.IterM.foldM_mapM 9 := fun H => by
  have h0 := by
    letI : IteratorLoop AD Id Id := NoLoop
    haveI := NoLoop.lawfulAD (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure x) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_of rfl))
  have h1 := by
    letI : IteratorLoop AD Id Id := ADLoop 0
    haveI := ADLoop.lawful 0 (m := Id) (n := Id)
    exact of_trip (H (α := AD) (β := Nat) (m := Id) (n := Id) (o := Id) (it := ⟨⟨()⟩⟩) (f := fun x => pure x) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_of rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.foldM_mapM` (idx 22): necessary; finite base iterator FD, o = StateT Unit Id; with the unlawful base loops NoLoop and FDLoop 0 the hypothesis holds for results 0 resp. 1, while the combinator side (default loop) is the same term both times
theorem IterM_foldM_mapM_22 : ¬ drop0% Std.Do.Spec.IterM.foldM_mapM 22 := fun H => by
  have h0 := by
    letI : IteratorLoop FD Id Id := .defaultImplementation
    letI : IteratorLoop FD Id (StateT Unit Id) := NoLoop
    exact of_tripS (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := StateT Unit Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure x) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 0⌝, ExceptConds.false)) (trip_ofS rfl))
  have h1 := by
    letI : IteratorLoop FD Id Id := .defaultImplementation
    letI : IteratorLoop FD Id (StateT Unit Id) := FDLoop 0
    exact of_tripS (H (α := FD) (β := Nat) (m := Id) (n := Id) (o := StateT Unit Id) (it := ⟨⟨true⟩⟩) (f := fun x => pure x) (init := 0) (g := fun _ c => pure (c+1))
      (P := ⌜True⌝) (Q := (fun r => ⌜r = 1⌝, ExceptConds.false)) (trip_ofS rfl))
  rw [h0] at h1; exact Nat.zero_ne_one h1

-- `Std.Do.Spec.IterM.foldM_mapM` (idx 33): necessary; all monads Id, list iterator [0], precondition True, postcondition False: the triple fails
theorem IterM_foldM_mapM_33 : ¬ drop0% Std.Do.Spec.IterM.foldM_mapM 33 := fun H => by
  have := H (m := Id) (n := Id) (o := Id) (it := [0].iterM Id) (f := fun x => pure x) (init := 0) (g := fun _ c => pure (c+1))
    (P := ⌜True⌝) (Q := (fun _ => ⌜False⌝, ExceptConds.false))
  simp [Triple, wp] at this


end DoSpecAHand

/-! ## Monad-law rows: broken monads and lifts of the hand8 pass (`checks/ItMonadMAHand.lean`), with the WP monad pinned -/

open Std Std.Do Std.Iterators
namespace DoSpecAMA

theorem pinId {α : Type} {x y : Id α} (H : ∀ P Q, Triple y P Q → Triple x P Q) : x = y := by
  have := H ⌜True⌝ (PostCond.noThrow fun r => ⌜r = y.run⌝) (fun _ => rfl)
  exact this trivial

end DoSpecAMA

/-! ## WP interpretations through `StateM σ` -/
namespace DoSpecAMA
open Std Std.Do

/-- A `WP` instance read off a map `φ` into `StateM σ`. -/
@[instance_reducible] def wpVia {o : Type → Type} {σ : Type} (φ : ∀ {α : Type}, o α → StateM σ α) :
    WP o (.arg σ .pure) := ⟨fun x => wp (φ x)⟩

/-- `wpVia φ` is a `WPMonad` when `φ` is a monad morphism. -/
@[instance_reducible] def wpmVia {o : Type → Type} [Monad o] [LawfulMonad o] {σ : Type}
    (φ : ∀ {α : Type}, o α → StateM σ α)
    (hp : ∀ {α : Type} (a : α), φ (pure a) = pure a)
    (hb : ∀ {α β : Type} (x : o α) (f : α → o β), φ (x >>= f) = φ x >>= fun a => φ (f a)) :
    WPMonad o (.arg σ .pure) :=
  @WPMonad.mk o _ _ inferInstance (wpVia φ)
    (fun a => by show wp (φ (pure a)) = _; rw [hp, WPMonad.wp_pure])
    (fun x f => by show wp (φ (x >>= f)) = _; rw [hb, WPMonad.wp_bind]; rfl)

/-- If every triple of `y` is one of `x`, then `x` and `y` agree under `φ` at every start state. -/
theorem pinVia {o : Type → Type} {σ : Type} (φ : ∀ {α : Type}, o α → StateM σ α) {α : Type} {x y : o α}
    (H : ∀ P Q, @Triple o (.arg σ .pure) (wpVia φ) α y P Q → @Triple o (.arg σ .pure) (wpVia φ) α x P Q)
    (s : σ) : φ x s = φ y s := by
  have := H (fun s' => ⌜s' = s⌝) (fun r s' => ⌜(r, s') = φ y s⌝, ()) (fun s' hs => by cases hs; exact rfl)
  exact this s rfl

end DoSpecAMA
namespace DoSpecAMA.MA
open Std Std.Iterators Std.Iterators.Types Std.Internal

/-! ## Unfolding lemmas for the consumers, without monad laws -/

theorem toArray_go_eq {α β : Type} {m : Type → Type} [Monad m] [Iterator α m β] [Finite α m]
    (it : IterM (α := α) m β) (acc : Array β) :
    IterM.toArray.go it acc = (do
      match (← it.step).inflate with
      | .yield it' out _ => IterM.toArray.go it' (acc.push out)
      | .skip it' _ => IterM.toArray.go it' acc
      | .done _ => return acc) := by
  rw [IterM.toArray.go, WellFounded.extrinsicFix₂_eq_apply]
  · rfl
  · simp only [show (IterM.finitelyManySteps! = IterM.finitelyManySteps) by rfl]
    exact InvImage.wf _ WellFoundedRelation.wf

theorem toListRev_go_eq {α β : Type} {m : Type → Type} [Monad m] [Iterator α m β] [Finite α m]
    (it : IterM (α := α) m β) (acc : List β) :
    IterM.toListRev.go it acc = (do
      match (← it.step).inflate with
      | .yield it' out _ => IterM.toListRev.go it' (out :: acc)
      | .skip it' _ => IterM.toListRev.go it' acc
      | .done _ => return acc) := by
  rw [IterM.toListRev.go, WellFounded.extrinsicFix₂_eq_apply]
  · apply bind_congr; intro s
    cases s.inflate using PlausibleIterStep.casesOn <;> rfl
  · simp only [show (IterM.finitelyManySteps! = IterM.finitelyManySteps) by rfl]
    exact InvImage.wf _ WellFoundedRelation.wf

theorem forIn'_eq {α β : Type} {m : Type → Type} [Iterator α m β] [Finite α m] {n : Type → Type}
    [Monad n] (lift : (γ : Type) → (δ : Type) → (γ → n δ) → m γ → n δ) (γ : Type)
    (Pl : β → γ → ForInStep γ → Prop) (it : IterM (α := α) m β) (init : γ) (P : β → Prop)
    (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b)
    (f : (b : β) → P b → (c : γ) → n (Subtype (Pl b c))) :
    IterM.DefaultConsumers.forIn' lift γ Pl it init P hP f =
      (lift _ _ · it.step) fun s =>
        match s.inflate with
        | .yield it' out h => do
          match ← f out (hP out <| .direct ⟨_, h⟩) init with
          | ⟨.yield c, _⟩ =>
            (IterM.DefaultConsumers.forIn' lift γ Pl it' c P
              (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f)
          | ⟨.done c, _⟩ => return c
        | .skip it' h =>
            (IterM.DefaultConsumers.forIn' lift γ Pl it' init P
              (fun _ h' => hP _ <| .indirect ⟨_, rfl, h⟩ h') f)
        | .done _ => return init := by
  haveI : Nonempty γ := ⟨init⟩
  rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply]
  · congr 1; funext s
    cases s.inflate using PlausibleIterStep.casesOn
    · apply bind_congr; intro r
      rcases r with ⟨_ | _, _⟩ <;> rfl
    · rfl
    · rfl
  · exact InvImage.wf _ IteratorLoop.wellFounded_of_finite

/-- The step of a `map`-type iterator, stated on the `Map` type (unfolding the combinator to
`FilterMap` would produce terms that only typecheck up to unfolding `Map`). -/
theorem map_step_eq {α β γ : Type} {m n : Type → Type} [Monad n] [Iterator α m β]
    {lift : ⦃α : Type⦄ → m α → n α} {f : β → PostconditionT n γ} (it : IterM (α := α) m β) :
    (IterM.InternalCombinators.map lift f it).step = (do
      match (← lift it.step).inflate with
      | .yield it' out h => do
        match ← (PostconditionT.map some (f out)).operation with
        | ⟨none, h'⟩ => pure (.deflate
            (.skip (IterM.InternalCombinators.map lift f it') (by exact .yieldNone h h')))
        | ⟨some out', h'⟩ => pure (.deflate
            (.yield (IterM.InternalCombinators.map lift f it') out' (by exact .yieldSome h h')))
      | .skip it' h => pure (.deflate
          (.skip (IterM.InternalCombinators.map lift f it') (by exact .skip h)))
      | .done h => pure (.deflate (.done (by exact .done h)))) := by
  apply bind_congr; intro s
  obtain ⟨t, rfl⟩ : ∃ t, s = Shrink.deflate t := ⟨s.inflate, Shrink.deflate_inflate.symm⟩
  rcases t with ⟨_ | _ | _, h⟩ <;> (try simp only [Shrink.inflate_deflate]) <;>
    (try erw [Shrink.inflate_deflate]) <;> (try rfl) <;>
    (apply bind_congr; intro r; rcases r with ⟨_ | _, _⟩ <;> rfl)

theorem filterMap_step_eq {α β γ : Type} {m n : Type → Type} [Monad n] [Iterator α m β]
    {lift : ⦃α : Type⦄ → m α → n α} {f : β → PostconditionT n (Option γ)}
    (it : IterM (α := α) m β) :
    (IterM.InternalCombinators.filterMap lift f it).step = (do
      match (← lift it.step).inflate with
      | .yield it' out h => do
        match ← (f out).operation with
        | ⟨none, h'⟩ => pure (.deflate
            (.skip (IterM.InternalCombinators.filterMap lift f it') (by exact .yieldNone h h')))
        | ⟨some out', h'⟩ => pure (.deflate
            (.yield (IterM.InternalCombinators.filterMap lift f it') out' (by exact .yieldSome h h')))
      | .skip it' h => pure (.deflate
          (.skip (IterM.InternalCombinators.filterMap lift f it') (by exact .skip h)))
      | .done h => pure (.deflate (.done (by exact .done h)))) := by
  apply bind_congr; intro s
  obtain ⟨t, rfl⟩ : ∃ t, s = Shrink.deflate t := ⟨s.inflate, Shrink.deflate_inflate.symm⟩
  rcases t with ⟨_ | _ | _, h⟩ <;> (try simp only [Shrink.inflate_deflate]) <;>
    (try erw [Shrink.inflate_deflate]) <;> (try rfl) <;>
    (apply bind_congr; intro r; rcases r with ⟨_ | _, _⟩ <;> rfl)

theorem attach_step_eq {α β : Type} {m : Type → Type} [Monad m] [Iterator α m β] {P : β → Prop}
    (it : IterM (α := Attach α m P) m {out : β // P out}) :
    it.step = (fun step => .deflate ⟨Attach.Monadic.modifyStep it step.inflate, step.inflate, rfl⟩) <$>
      it.internalState.inner.step := rfl

theorem list_step_nil {β : Type} {m : Type → Type} [Pure m] :
    (([] : List β).iterM m).step = pure (.deflate ⟨.done, rfl⟩) := rfl
theorem list_step_cons {β : Type} {m : Type → Type} [Pure m] (x : β) (xs : List β) :
    ((x :: xs).iterM m).step = pure (.deflate ⟨.yield (xs.iterM m) x, rfl⟩) := rfl

/-! ## An `IteratorLoop` instance that is lawful but returns `init` for non-lawful lift functions -/

set_option warn.classDefReducibility false in
open Classical in
noncomputable def evilLoop {α β : Type} {m n : Type → Type} [Monad m] [Monad n] [Iterator α m β] :
    IteratorLoop α m n where
  forIn lift γ Pl it init f :=
    if LawfulMonadLiftBindFunction lift then
      IteratorLoop.defaultImplementation.forIn lift γ Pl it init f
    else pure init

open Classical in
theorem evilLoop_lawful {α β : Type} {m n : Type → Type} [Monad m] [Monad n] [Iterator α m β] :
    letI : IteratorLoop α m n := evilLoop
    LawfulIteratorLoop α m n := by
  letI : IteratorLoop α m n := evilLoop
  constructor
  intro lift hl γ it init Pl wf f
  show (if LawfulMonadLiftBindFunction lift then _ else _) = _
  rw [if_pos hl]

open Classical in
theorem evilLoop_forIn {α β : Type} {m n : Type → Type} [Monad m] [Monad n] [Iterator α m β]
    {lift} {γ Pl it init f} (h : ¬ LawfulMonadLiftBindFunction lift) :
    (evilLoop (α := α) (β := β) (m := m) (n := n)).forIn lift γ Pl it init f = pure init := by
  show (if LawfulMonadLiftBindFunction lift then _ else _) = _
  rw [if_neg h]

theorem not_lawful_of {m n : Type → Type} [Monad m] [Monad n]
    {L : (γ : Type) → (δ : Type) → (γ → n δ) → m γ → n δ} {γ δ : Type} (f : γ → n δ) (a : γ)
    (h : L γ δ f (pure a) ≠ f a) : ¬ LawfulMonadLiftBindFunction L :=
  fun hl => h (hl.liftBind_pure f a)

/-! ## Monads -/

theorem pc_attachLift_op {m : Type → Type} [MonadAttach m] {α : Type} (x : m α) :
    (PostconditionT.attachLift x).operation = MonadAttach.attach x := rfl
theorem pc_lift_op {m : Type → Type} [Functor m] {α : Type} (x : m α) :
    (PostconditionT.lift x).operation = (fun a => ⟨a, .intro⟩) <$> x := rfl
theorem pc_pure_op {m : Type → Type} [Pure m] {α : Type} (a : α) :
    (PostconditionT.pure a : PostconditionT m α).operation = pure ⟨a, rfl⟩ := rfl
theorem pc_map_op {m : Type → Type} [Functor m] {α β : Type} (f : α → β) (x : PostconditionT m α) :
    (PostconditionT.map f x).operation =
      Functor.map (β := Subtype (PostconditionT.map f x).Property)
        (fun a => ⟨f a.val, _, rfl⟩) x.operation := rfl
theorem ml_lift {m n : Type → Type} (f : {α : Type} → m α → n α) {α : Type} (x : m α) :
    @MonadLift.monadLift m n ⟨@f⟩ α x = f x := rfl
theorem ml_trans {m n o : Type → Type} [MonadLift n o] [MonadLiftT m n] {α : Type} (x : m α) :
    (monadLift x : o α) = MonadLift.monadLift (monadLift x : n α) := rfl
theorem ml_Id {n : Type → Type} [Pure n] {α : Type} (x : Id α) : (monadLift x : n α) = pure x.run := rfl
theorem Id_bind_eq {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl
theorem Id_pure_eq {α : Type} (a : α) : (pure a : Id α) = a := rfl
theorem Id_map_eq {α β : Type} (f : α → β) (x : Id α) : f <$> x = f x := rfl


/-- Counting monad: `bind` adds one; `pure` and `map` add nothing. Not lawful. -/
structure CM (α : Type) where
  c : Nat
  v : α
instance : Monad CM where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c + 1, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
instance : MonadAttach CM := .trivial
theorem CM.attach_eq {α} (x : CM α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, trivial⟩⟩ := rfl
instance : WeaklyLawfulMonadAttach CM := ⟨rfl⟩
theorem CM.bind_eq {α β} (x : CM α) (f : α → CM β) : x >>= f = ⟨x.c + (f x.v).c + 1, (f x.v).v⟩ := rfl
theorem CM.pure_eq {α} (a : α) : (pure a : CM α) = ⟨0, a⟩ := rfl
theorem CM.map_eq {α β} (f : α → β) (x : CM α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
theorem CM.not_lawful {m : Type → Type} [Monad m] (lift : ⦃α : Type⦄ → m α → CM α) :
    ¬ LawfulMonadLiftBindFunction (m := m) (n := CM) (fun _ _ f x => lift x >>= f) :=
  not_lawful_of (m := m) (n := CM) (L := fun _ _ f x => lift x >>= f) (γ := Nat)
    (fun _ => (⟨0, 0⟩ : CM Nat)) 0 (by simp [CM.bind_eq])

/-- Counting monad where `map` also adds one. Not lawful. -/
structure CM2 (α : Type) where
  c : Nat
  v : α
instance : Monad CM2 where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c + 1, (f x.v).v⟩
  map f x := ⟨x.c + 1, f x.v⟩
instance : MonadAttach CM2 := .trivial
theorem CM2.bind_eq {α β} (x : CM2 α) (f : α → CM2 β) : x >>= f = ⟨x.c + (f x.v).c + 1, (f x.v).v⟩ := rfl
theorem CM2.pure_eq {α} (a : α) : (pure a : CM2 α) = ⟨0, a⟩ := rfl
theorem CM2.map_eq {α β} (f : α → β) (x : CM2 α) : f <$> x = ⟨x.c + 1, f x.v⟩ := rfl
theorem CM2.attach_eq {α} (x : CM2 α) : MonadAttach.attach x = ⟨x.c + 1, ⟨x.v, trivial⟩⟩ := rfl

/-- Bind adds one exactly when the continuation's result has a nonzero count: `pure`/`pure` binds
are free (so `pure` from a lawful monad is a lawful lift), but `pure a >>= f ≠ f a`. -/
structure QM (α : Type) where
  c : Nat
  v : α
instance : Monad QM where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c + min (f x.v).c 1, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
instance : MonadAttach QM := .trivial
theorem QM.attach_eq {α} (x : QM α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, trivial⟩⟩ := rfl
instance : WeaklyLawfulMonadAttach QM := ⟨rfl⟩
theorem QM.bind_eq {α β} (x : QM α) (f : α → QM β) :
    x >>= f = ⟨x.c + (f x.v).c + min (f x.v).c 1, (f x.v).v⟩ := rfl
theorem QM.pure_eq {α} (a : α) : (pure a : QM α) = ⟨0, a⟩ := rfl
theorem QM.map_eq {α β} (f : α → β) (x : QM α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
instance : LawfulMonadLiftT Id QM where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl
theorem QM.not_lawful {m : Type → Type} [Monad m] (lift : ⦃α : Type⦄ → m α → QM α) :
    ¬ LawfulMonadLiftBindFunction (m := m) (n := QM) (fun _ _ f x => lift x >>= f) :=
  not_lawful_of (m := m) (n := QM) (L := fun _ _ f x => lift x >>= f) (γ := Nat)
    (fun _ => (⟨1, 0⟩ : QM Nat)) 0 (by simp [QM.bind_eq])

/-- Weighted counting monad: `bind x f` doubles the count of `x`. `pure` from `Id` is a lawful lift
and `pure a >>= f = f a`, but `x >>= pure ≠ x` and `bind` is not associative. -/
structure WM (α : Type) where
  c : Nat
  v : α
instance : Monad WM where
  pure a := ⟨0, a⟩
  bind x f := ⟨2 * x.c + (f x.v).c, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
instance : MonadAttach WM := .trivial
instance : WeaklyLawfulMonadAttach WM := ⟨rfl⟩
theorem WM.bind_eq {α β} (x : WM α) (f : α → WM β) : x >>= f = ⟨2 * x.c + (f x.v).c, (f x.v).v⟩ := rfl
theorem WM.pure_eq {α} (a : α) : (pure a : WM α) = ⟨0, a⟩ := rfl
theorem WM.map_eq {α β} (f : α → β) (x : WM α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
theorem WM.attach_eq {α} (x : WM α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, trivial⟩⟩ := rfl
instance : LawfulMonadLiftT Id WM where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

/-- Lawful `Nat` writer. -/
structure NW (α : Type) where
  c : Nat
  v : α
instance : Monad NW where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
theorem NW.bind_eq {α β} (x : NW α) (f : α → NW β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := rfl
theorem NW.pure_eq {α} (a : α) : (pure a : NW α) = ⟨0, a⟩ := rfl
theorem NW.map_eq {α β} (f : α → β) (x : NW α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
theorem NW.ext' {α} {x y : NW α} (h1 : x.c = y.c) (h2 : x.v = y.v) : x = y := by
  cases x; cases y; simp_all
instance : LawfulMonad NW := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => NW.ext' (Nat.zero_add _) rfl)
  (bind_assoc := fun _ _ _ => NW.ext' (Nat.add_assoc _ _ _) rfl)
  (bind_pure_comp := fun _ _ => rfl)
instance : MonadAttach NW := .trivial
theorem NW.attach_eq {α} (x : NW α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, trivial⟩⟩ := rfl
instance : WeaklyLawfulMonadAttach NW := ⟨rfl⟩

/-- Lawful `Bool` writer (`or`). -/
structure W (α : Type) where
  c : Bool
  v : α
instance : Monad W where
  pure a := ⟨false, a⟩
  bind x f := ⟨x.c || (f x.v).c, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
theorem W.bind_eq {α β} (x : W α) (f : α → W β) : x >>= f = ⟨x.c || (f x.v).c, (f x.v).v⟩ := rfl
theorem W.pure_eq {α} (a : α) : (pure a : W α) = ⟨false, a⟩ := rfl
theorem W.map_eq {α β} (f : α → β) (x : W α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
theorem W.ext' {α} {x y : W α} (h1 : x.c = y.c) (h2 : x.v = y.v) : x = y := by
  cases x; cases y; simp_all
instance : LawfulMonad W := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => W.ext' (Bool.false_or _) rfl)
  (bind_assoc := fun _ _ _ => W.ext' (Bool.or_assoc _ _ _) rfl)
  (bind_pure_comp := fun _ _ => W.ext' (Bool.or_false _) rfl)
instance : MonadAttach W := .trivial
theorem W.attach_eq {α} (x : W α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, trivial⟩⟩ := rfl
instance : WeaklyLawfulMonadAttach W := ⟨rfl⟩

/-- `Bool` writer whose `map` and `attach` flip the flag: bind and pure are lawful, `map` is not. -/
structure FM (α : Type) where
  c : Bool
  v : α
instance : Monad FM where
  pure a := ⟨false, a⟩
  bind x f := ⟨x.c || (f x.v).c, (f x.v).v⟩
  map f x := ⟨!x.c, f x.v⟩
instance : MonadAttach FM where
  CanReturn _ _ := True
  attach x := ⟨!x.c, ⟨x.v, trivial⟩⟩
instance : WeaklyLawfulMonadAttach FM := ⟨by intro α x; cases x; simp [Functor.map, MonadAttach.attach]⟩
theorem FM.bind_eq {α β} (x : FM α) (f : α → FM β) : x >>= f = ⟨x.c || (f x.v).c, (f x.v).v⟩ := rfl
theorem FM.pure_eq {α} (a : α) : (pure a : FM α) = ⟨false, a⟩ := rfl
theorem FM.map_eq {α β} (f : α → β) (x : FM α) : f <$> x = ⟨!x.c, f x.v⟩ := rfl
theorem FM.attach_eq {α} (x : FM α) : MonadAttach.attach x = ⟨!x.c, ⟨x.v, trivial⟩⟩ := rfl
instance : LawfulMonadLiftT Id FM where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl
instance : MonadLift FM W := ⟨fun x => ⟨x.c, x.v⟩⟩
theorem FM.lift_eq {α} (x : FM α) : (MonadLift.monadLift x : W α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLift FM W where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

/-- Copies of `NW` (lawful), and variants with a broken `attach` (reset resp. increment the count). -/
structure NW2 (α : Type) where
  c : Nat
  v : α
instance : Monad NW2 where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
theorem NW2.bind_eq {α β} (x : NW2 α) (f : α → NW2 β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := rfl
theorem NW2.pure_eq {α} (a : α) : (pure a : NW2 α) = ⟨0, a⟩ := rfl
theorem NW2.map_eq {α β} (f : α → β) (x : NW2 α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
theorem NW2.ext' {α} {x y : NW2 α} (h1 : x.c = y.c) (h2 : x.v = y.v) : x = y := by
  cases x; cases y; simp_all
instance : LawfulMonad NW2 := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => NW2.ext' (Nat.zero_add _) rfl)
  (bind_assoc := fun _ _ _ => NW2.ext' (Nat.add_assoc _ _ _) rfl)
  (bind_pure_comp := fun _ _ => rfl)
instance : MonadAttach NW2 := .trivial
theorem NW2.attach_eq {α} (x : NW2 α) : MonadAttach.attach x = ⟨x.c, ⟨x.v, trivial⟩⟩ := rfl
instance : WeaklyLawfulMonadAttach NW2 := ⟨rfl⟩

/-- `NW` with an `attach` that drops the count (not weakly lawful). -/
structure NWa (α : Type) where
  c : Nat
  v : α
instance : Monad NWa where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
theorem NWa.bind_eq {α β} (x : NWa α) (f : α → NWa β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := rfl
theorem NWa.pure_eq {α} (a : α) : (pure a : NWa α) = ⟨0, a⟩ := rfl
theorem NWa.map_eq {α β} (f : α → β) (x : NWa α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
theorem NWa.ext' {α} {x y : NWa α} (h1 : x.c = y.c) (h2 : x.v = y.v) : x = y := by
  cases x; cases y; simp_all
instance : LawfulMonad NWa := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => NWa.ext' (Nat.zero_add _) rfl)
  (bind_assoc := fun _ _ _ => NWa.ext' (Nat.add_assoc _ _ _) rfl)
  (bind_pure_comp := fun _ _ => rfl)
instance : MonadAttach NWa where
  CanReturn _ _ := True
  attach x := ⟨0, ⟨x.v, trivial⟩⟩
theorem NWa.attach_eq {α} (x : NWa α) : MonadAttach.attach x = ⟨0, ⟨x.v, trivial⟩⟩ := rfl
instance : LawfulMonadLiftT Id NWa where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl
instance : MonadLift NWa NW := ⟨fun x => ⟨x.c, x.v⟩⟩
theorem NWa.lift_eq {α} (x : NWa α) : (MonadLift.monadLift x : NW α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLift NWa NW where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

/-- `NW` with an `attach` that adds one to the count (not weakly lawful). -/
structure NWb (α : Type) where
  c : Nat
  v : α
instance : Monad NWb where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map f x := ⟨x.c, f x.v⟩
theorem NWb.bind_eq {α β} (x : NWb α) (f : α → NWb β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := rfl
theorem NWb.pure_eq {α} (a : α) : (pure a : NWb α) = ⟨0, a⟩ := rfl
theorem NWb.map_eq {α β} (f : α → β) (x : NWb α) : f <$> x = ⟨x.c, f x.v⟩ := rfl
theorem NWb.ext' {α} {x y : NWb α} (h1 : x.c = y.c) (h2 : x.v = y.v) : x = y := by
  cases x; cases y; simp_all
instance : LawfulMonad NWb := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => NWb.ext' (Nat.zero_add _) rfl)
  (bind_assoc := fun _ _ _ => NWb.ext' (Nat.add_assoc _ _ _) rfl)
  (bind_pure_comp := fun _ _ => rfl)
instance : MonadAttach NWb where
  CanReturn _ _ := True
  attach x := ⟨x.c + 1, ⟨x.v, trivial⟩⟩
theorem NWb.attach_eq {α} (x : NWb α) : MonadAttach.attach x = ⟨x.c + 1, ⟨x.v, trivial⟩⟩ := rfl
instance : LawfulMonadLiftT Id NWb where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl
instance : MonadLift NWb NW := ⟨fun x => ⟨x.c, x.v⟩⟩
theorem NWb.lift_eq {α} (x : NWb α) : (MonadLift.monadLift x : NW α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLift NWb NW where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

/-- `NW` whose `map` adds one to the count (bind and pure are lawful, `map` is not). -/
structure MB (α : Type) where
  c : Nat
  v : α
instance : Monad MB where
  pure a := ⟨0, a⟩
  bind x f := ⟨x.c + (f x.v).c, (f x.v).v⟩
  map f x := ⟨x.c + 1, f x.v⟩
theorem MB.bind_eq {α β} (x : MB α) (f : α → MB β) : x >>= f = ⟨x.c + (f x.v).c, (f x.v).v⟩ := rfl
theorem MB.pure_eq {α} (a : α) : (pure a : MB α) = ⟨0, a⟩ := rfl
theorem MB.map_eq {α β} (f : α → β) (x : MB α) : f <$> x = ⟨x.c + 1, f x.v⟩ := rfl
instance : MonadLift MB NW := ⟨fun x => ⟨x.c, x.v⟩⟩
theorem MB.lift_eq {α} (x : MB α) : (MonadLift.monadLift x : NW α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLift MB NW where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

/-- Lifts that add one to the count (not lawful). -/
@[instance_reducible] def tickNW2 : MonadLift NW2 NW := ⟨fun x => ⟨x.c + 1, x.v⟩⟩
@[instance_reducible] def tickNW : MonadLift NW NW2 := ⟨fun x => ⟨x.c + 1, x.v⟩⟩
theorem tickNW2_eq {α} (x : NW2 α) : @MonadLift.monadLift NW2 NW tickNW2 α x = ⟨x.c + 1, x.v⟩ := rfl
theorem tickNW_eq {α} (x : NW α) : @MonadLift.monadLift NW NW2 tickNW α x = ⟨x.c + 1, x.v⟩ := rfl

/-- Lawful lifts out of `NW`: forgetting the count into `QM`, and the identity into `NWb`. -/
instance : MonadLift NW QM := ⟨fun x => ⟨0, x.v⟩⟩
theorem NW.liftQ_eq {α} (x : NW α) : (MonadLift.monadLift x : QM α) = ⟨0, x.v⟩ := rfl
instance : LawfulMonadLift NW QM where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl
instance : MonadLift NW NWb := ⟨fun x => ⟨x.c, x.v⟩⟩
theorem NW.liftB_eq {α} (x : NW α) : (MonadLift.monadLift x : NWb α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLift NW NWb where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

/-- `Bool` writer whose `map` flips the flag iff the target type is a subsingleton, and whose
`attach` flips it iff the value type is a subsingleton (`CanReturn x a := a = x.v`). Bind and pure
are lawful, `attach` is weakly lawful, but `map` is not (it is not parametric). -/
structure SM (α : Type) where
  c : Bool
  v : α
open Classical in
noncomputable instance : Monad SM where
  pure a := ⟨false, a⟩
  bind x f := ⟨x.c || (f x.v).c, (f x.v).v⟩
  map {_ β} f x := ⟨xor x.c (decide (Subsingleton β)), f x.v⟩
open Classical in
noncomputable instance : MonadAttach SM where
  CanReturn x a := a = x.v
  attach {α} x := ⟨xor x.c (decide (Subsingleton α)), ⟨x.v, rfl⟩⟩
instance : WeaklyLawfulMonadAttach SM := ⟨by
  intro α x; cases x; simp [Functor.map, MonadAttach.attach]⟩
/-- A type with two distinct elements. -/
class NonSub (α : Type) : Prop where
  ns : ¬ Subsingleton α
instance : NonSub Nat := ⟨fun h => absurd (h.allEq 0 1) (by decide)⟩
instance : NonSub (ULift Bool) := ⟨fun h => absurd (h.allEq ⟨false⟩ ⟨true⟩) (by simp)⟩
instance {α : Type} [Inhabited α] : NonSub (Option α) :=
  ⟨fun h => absurd (h.allEq none (some default)) (by simp)⟩
theorem SM.bind_eq {α β} (x : SM α) (f : α → SM β) : x >>= f = ⟨x.c || (f x.v).c, (f x.v).v⟩ := rfl
theorem SM.pure_eq {α} (a : α) : (pure a : SM α) = ⟨false, a⟩ := rfl
theorem SM.map_sub {α β} [h : Subsingleton β] (f : α → β) (x : SM α) : f <$> x = ⟨!x.c, f x.v⟩ := by
  simp [Functor.map, h]
theorem SM.map_nsub {α β} [h : NonSub β] (f : α → β) (x : SM α) : f <$> x = ⟨x.c, f x.v⟩ := by
  simp [Functor.map, h.ns]
theorem SM.attach_nsub {α} [h : NonSub α] (x : SM α) :
    MonadAttach.attach x = ⟨x.c, ⟨x.v, rfl⟩⟩ := by
  simp [MonadAttach.attach, h.ns]
instance {α : Type} (x : SM α) : Subsingleton (Subtype (MonadAttach.CanReturn x)) :=
  ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
instance {m : Type → Type} [Pure m] {α : Type} (a : α) :
    Subsingleton (Subtype (PostconditionT.pure a : PostconditionT m α).Property) :=
  ⟨fun x y => Subtype.ext (x.2.symm.trans y.2)⟩
instance {m : Type → Type} [MonadAttach m] {α : Type} (x : m α)
    [Subsingleton (Subtype (MonadAttach.CanReturn x))] :
    Subsingleton (Subtype (PostconditionT.attachLift x).Property) :=
  inferInstanceAs (Subsingleton (Subtype (MonadAttach.CanReturn x)))
instance {m : Type → Type} [Functor m] {α β : Type} (g : α → β) (x : PostconditionT m α)
    [Subsingleton (Subtype x.Property)] :
    Subsingleton (Subtype (PostconditionT.map g x).Property) :=
  ⟨fun a b => by
    obtain ⟨_, a', rfl⟩ := a; obtain ⟨_, b', rfl⟩ := b
    rw [Subsingleton.elim a' b']⟩
instance : LawfulMonadLiftT Id SM where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl
instance : MonadLift SM W := ⟨fun x => ⟨x.c, x.v⟩⟩
theorem SM.lift_eq {α} (x : SM α) : (MonadLift.monadLift x : W α) = ⟨x.c, x.v⟩ := rfl
instance : LawfulMonadLift SM W where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

instance : LawfulMonadLiftT Id W where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl
instance : LawfulMonadLiftT Id NW where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := rfl

end DoSpecAMA.MA


namespace DoSpecAMA.MA
open Std Std.Iterators Std.Iterators.Types Std.Internal

/-- Structural unfolding of consumers, combinators and the list iterator (nothing that occurs in
types, so that types and instance arguments stay in sync). -/
macro "ev_unfold" : tactic => `(tactic| dsimp only [IterM.toArray, IterM.toList, IterM.toListRev,
  IterM.foldM, IterM.fold, IterM.anyM, IterM.allM, IterM.any, IterM.all, IterM.length,
  ForIn.forIn, ForIn'.forIn', instForInOfForIn', IterM.instForInOfIteratorLoop, IterM.instForIn',
  IteratorLoop.finiteForIn', IteratorLoop.defaultImplementation, IteratorLoop.forIn,
  ListIterator.instIteratorLoop, FilterMap.instIteratorLoop, Map.instIteratorLoop,
  IterM.filterMap, IterM.map, IterM.filter, IterM.filterMapM, IterM.mapM, IterM.filterM,
  IterM.filterWithPostcondition, IterM.mapWithPostcondition, IterM.filterMapWithPostcondition,
  Attach.Monadic.modifyStep, IterM.attachWith] at *)

/-- Monad operations of the models, lifts, `PostconditionT`, `Shrink`; never inside types. -/
macro "ev_simp" : tactic => `(tactic| simp (config := { dsimp := false }) only [liftM, ↓map_step_eq, ↓filterMap_step_eq, ↓list_step_nil, ↓list_step_cons,
  ↓IterM.step_append, ↓IterM.Intermediate.step_appendSnd, ↓attach_step_eq,
  ↓NWa.lift_eq, ↓NW.liftQ_eq, ↓NW.liftB_eq, ↓NWb.lift_eq, ↓MB.lift_eq, ↓tickNW2_eq, ↓tickNW_eq,
  ↓monadLift_self, ↓ml_lift, ↓ml_trans, ↓ml_Id, ↓FM.lift_eq, ↓pc_attachLift_op, ↓pc_lift_op, ↓pc_pure_op, ↓pc_map_op, ↓PostconditionT.operation_pure, ↓PostconditionT.run_eq_map, ↓CM.bind_eq, ↓CM.pure_eq, ↓CM.map_eq, ↓CM.attach_eq, ↓QM.bind_eq, ↓QM.pure_eq, ↓QM.map_eq, ↓QM.attach_eq, ↓NW.bind_eq, ↓NW.pure_eq, ↓NW.map_eq, ↓NW.attach_eq, ↓W.bind_eq, ↓W.pure_eq, ↓W.map_eq, ↓W.attach_eq, ↓FM.bind_eq, ↓FM.pure_eq, ↓FM.map_eq, ↓FM.attach_eq, ↓NW2.bind_eq, ↓NW2.pure_eq, ↓NW2.map_eq, ↓NW2.attach_eq, ↓NWa.bind_eq, ↓NWa.pure_eq, ↓NWa.map_eq, ↓NWa.attach_eq, ↓NWb.bind_eq, ↓NWb.pure_eq, ↓NWb.map_eq, ↓NWb.attach_eq, ↓MB.bind_eq, ↓MB.pure_eq, ↓MB.map_eq, Id.run_pure, Id.run_bind, Id.run_map, Id.run, ↓Id_bind_eq, ↓Id_pure_eq, ↓SM.bind_eq, ↓SM.pure_eq, ↓SM.map_sub, ↓SM.map_nsub, ↓SM.attach_nsub, ↓SM.lift_eq, ↓WM.bind_eq, ↓WM.pure_eq, ↓WM.map_eq, ↓WM.attach_eq, ↓CM2.bind_eq, ↓CM2.pure_eq, ↓CM2.map_eq, ↓CM2.attach_eq,
  Shrink.inflate_deflate, ite_true, ite_false, ↓reduceIte] at *)

macro "ev_all" : tactic => `(tactic| repeat (first
  | (rw [toArray_go_eq] at *) | (rw [toListRev_go_eq] at *) | (rw [forIn'_eq] at *)
  | ev_unfold | ev_simp))

end DoSpecAMA.MA

namespace DoSpecAMA.MA
open Std Std.Do

def NW.φ {α : Type} (x : NW α) : StateM Nat α := fun s => (x.v, s + x.c)
instance NW.wpm : WPMonad NW (.arg Nat .pure) := wpmVia NW.φ
  (fun a => by funext s; simp [NW.φ, NW.pure_eq]; rfl)
  (fun x f => by funext s; show ((f x.v).v, s + (x.c + (f x.v).c)) = ((f x.v).v, s + x.c + (f x.v).c); rw [Nat.add_assoc])
theorem NW.pin {α : Type} {x y : NW α} (H : ∀ P Q, Triple y P Q → Triple x P Q) : x = y := by
  have := pinVia NW.φ H 0
  simp [NW.φ] at this
  have := Prod.mk.inj this
  exact NW.ext' this.2 this.1

end DoSpecAMA.MA

namespace DoSpecAMA.MA
open Std Std.Do

def NW2.φ {α : Type} (x : NW2 α) : StateM Nat α := fun s => (x.v, s + x.c)
instance NW2.wpm : WPMonad NW2 (.arg Nat .pure) := wpmVia NW2.φ
  (fun a => by funext s; simp [NW2.φ, NW2.pure_eq]; rfl)
  (fun x f => by funext s; show ((f x.v).v, s + (x.c + (f x.v).c)) = ((f x.v).v, s + x.c + (f x.v).c); rw [Nat.add_assoc])
theorem NW2.pin {α : Type} {x y : NW2 α} (H : ∀ P Q, Triple y P Q → Triple x P Q) : x = y := by
  have := pinVia NW2.φ H 0
  simp [NW2.φ] at this
  have := Prod.mk.inj this
  exact NW2.ext' this.2 this.1

def NWb.φ {α : Type} (x : NWb α) : StateM Nat α := fun s => (x.v, s + x.c)
instance NWb.wpm : WPMonad NWb (.arg Nat .pure) := wpmVia NWb.φ
  (fun a => by funext s; simp [NWb.φ, NWb.pure_eq]; rfl)
  (fun x f => by funext s; show ((f x.v).v, s + (x.c + (f x.v).c)) = ((f x.v).v, s + x.c + (f x.v).c); rw [Nat.add_assoc])
theorem NWb.pin {α : Type} {x y : NWb α} (H : ∀ P Q, Triple y P Q → Triple x P Q) : x = y := by
  have := pinVia NWb.φ H 0
  simp [NWb.φ] at this
  have := Prod.mk.inj this
  exact NWb.ext' this.2 this.1

def W.φ {α : Type} (x : W α) : StateM Bool α := fun s => (x.v, s || x.c)
instance W.wpm : WPMonad W (.arg Bool .pure) := wpmVia W.φ
  (fun a => by funext s; simp [W.φ, W.pure_eq]; rfl)
  (fun x f => by funext s; show ((f x.v).v, s || (x.c || (f x.v).c)) = ((f x.v).v, (s || x.c) || (f x.v).c); rw [Bool.or_assoc])
theorem W.pin {α : Type} {x y : W α} (H : ∀ P Q, Triple y P Q → Triple x P Q) : x = y := by
  have := pinVia W.φ H false
  simp [W.φ] at this
  have := Prod.mk.inj this
  exact W.ext' this.2 this.1

end DoSpecAMA.MA


namespace DoSpecAMA.MA
open Std Std.Do Std.Iterators Std.Iterators.Types

-- `Std.Do.Spec.IterM.forIn_filterMapWithPostcondition`, idx 11 (LawfulMonad n): as for the base lemma Std.IterM.forIn_filterMapWithPostcondition (checks/ItMonadMAHand.lean): m = Id, n = FM (Bool writer whose map and attach flip the flag: bind/pure lawful, weakly lawful attach, lawful lifts from Id and to o = W), list iterator [0]: the left side binds f's operation (resp. attach) directly, the right side maps it.; the WP monad pins the value
theorem IterM.forIn_filterMapWithPostcondition.h11 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMapWithPostcondition 11 := by
  intro h
  have := W.pin fun P Q => h (m := Id) (n := FM) (o := W) (it := [0].iterM Id) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_filterMapWithPostcondition`, idx 16 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.forIn_filterMapWithPostcondition (checks/ItMonadMAHand.lean): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.forIn_filterMapWithPostcondition.h16 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMapWithPostcondition 16 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_filterMapWithPostcondition`, idx 18 (LawfulMonadLiftT n o): as for the base lemma Std.IterM.forIn_filterMapWithPostcondition (checks/ItMonadMAHand.lean): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.forIn_filterMapWithPostcondition.h18 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMapWithPostcondition 18 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := NW2.pin fun P Q => h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_filterMapM`, idx 11 (LawfulMonad n): as for the base lemma Std.IterM.forIn_filterMapM (checks/ItMonadMAHand.lean): m = Id, n = FM (Bool writer whose map and attach flip the flag: bind/pure lawful, weakly lawful attach, lawful lifts from Id and to o = W), list iterator [0]: the left side binds f's operation (resp. attach) directly, the right side maps it.; the WP monad pins the value
theorem IterM.forIn_filterMapM.h11 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMapM 11 := by
  intro h
  have := W.pin fun P Q => h (m := Id) (n := FM) (o := W) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_filterMapM`, idx 16 (WeaklyLawfulMonadAttach n): as for the base lemma Std.IterM.forIn_filterMapM (checks/ItMonadMAHand.lean): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.; the WP monad pins the value
theorem IterM.forIn_filterMapM.h16 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMapM 16 := by
  intro h
  have := NW.pin fun P Q => h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_filterMapM`, idx 18 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.forIn_filterMapM (checks/ItMonadMAHand.lean): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.forIn_filterMapM.h18 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMapM 18 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_filterMapM`, idx 20 (LawfulMonadLiftT n o): as for the base lemma Std.IterM.forIn_filterMapM (checks/ItMonadMAHand.lean): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.forIn_filterMapM.h20 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMapM 20 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := NW2.pin fun P Q => h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_filterMap`, idx 13 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.forIn_filterMap (checks/ItMonadMAHand.lean): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.; the WP monad pins the value
theorem IterM.forIn_filterMap.h13 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterMap 13 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := some) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_mapWithPostcondition`, idx 11 (LawfulMonad n): as for the base lemma Std.IterM.forIn_mapWithPostcondition (checks/ItMonadMAHand.lean): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).; the WP monad pins the value
theorem IterM.forIn_mapWithPostcondition.h11 : ¬ drop0% Std.Do.Spec.IterM.forIn_mapWithPostcondition 11 := by
  intro h
  have := W.pin fun P Q => h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_mapWithPostcondition`, idx 16 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.forIn_mapWithPostcondition (checks/ItMonadMAHand.lean): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.forIn_mapWithPostcondition.h16 : ¬ drop0% Std.Do.Spec.IterM.forIn_mapWithPostcondition 16 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_mapWithPostcondition`, idx 18 (LawfulMonadLiftT n o): as for the base lemma Std.IterM.forIn_mapWithPostcondition (checks/ItMonadMAHand.lean): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.forIn_mapWithPostcondition.h18 : ¬ drop0% Std.Do.Spec.IterM.forIn_mapWithPostcondition 18 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := NW2.pin fun P Q => h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_mapM`, idx 11 (LawfulMonad n): as for the base lemma Std.IterM.forIn_mapM (checks/ItMonadMAHand.lean): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).; the WP monad pins the value
theorem IterM.forIn_mapM.h11 : ¬ drop0% Std.Do.Spec.IterM.forIn_mapM 11 := by
  intro h
  have := W.pin fun P Q => h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_mapM`, idx 16 (WeaklyLawfulMonadAttach n): as for the base lemma Std.IterM.forIn_mapM (checks/ItMonadMAHand.lean): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.; the WP monad pins the value
theorem IterM.forIn_mapM.h16 : ¬ drop0% Std.Do.Spec.IterM.forIn_mapM 16 := by
  intro h
  have := NW.pin fun P Q => h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_mapM`, idx 18 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.forIn_mapM (checks/ItMonadMAHand.lean): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.forIn_mapM.h18 : ¬ drop0% Std.Do.Spec.IterM.forIn_mapM 18 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_mapM`, idx 20 (LawfulMonadLiftT n o): as for the base lemma Std.IterM.forIn_mapM (checks/ItMonadMAHand.lean): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.forIn_mapM.h20 : ¬ drop0% Std.Do.Spec.IterM.forIn_mapM 20 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := NW2.pin fun P Q => h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_map`, idx 8 (LawfulMonad m): as for the base lemma Std.IterM.forIn_map (checks/ItMonadMAHand.lean): m = MB (lawful Nat writer bind/pure, but map adds one), n = NW, lawful lift MB → NW, list iterator [0]: the map combinator maps in m.; the WP monad pins the value
theorem IterM.forIn_map.h8 : ¬ drop0% Std.Do.Spec.IterM.forIn_map 8 := by
  intro h
  have := NW.pin fun P Q => h (m := MB) (n := NW) (it := [0].iterM MB) (f := id) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_map`, idx 13 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.forIn_map (checks/ItMonadMAHand.lean): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.; the WP monad pins the value
theorem IterM.forIn_map.h13 : ¬ drop0% Std.Do.Spec.IterM.forIn_map 13 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := id) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_filterWithPostcondition`, idx 10 (LawfulMonad n): as for the base lemma Std.IterM.forIn_filterWithPostcondition (checks/ItMonadMAHand.lean): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).; the WP monad pins the value
theorem IterM.forIn_filterWithPostcondition.h10 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterWithPostcondition 10 := by
  intro h
  have := W.pin fun P Q => h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_filterWithPostcondition`, idx 15 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.forIn_filterWithPostcondition (checks/ItMonadMAHand.lean): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.forIn_filterWithPostcondition.h15 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterWithPostcondition 15 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_filterWithPostcondition`, idx 17 (LawfulMonadLiftT n o): as for the base lemma Std.IterM.forIn_filterWithPostcondition (checks/ItMonadMAHand.lean): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.forIn_filterWithPostcondition.h17 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterWithPostcondition 17 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := NW2.pin fun P Q => h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun _ => PostconditionT.pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_filterM`, idx 10 (LawfulMonad n): as for the base lemma Std.IterM.forIn_filterM (checks/ItMonadMAHand.lean): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).; the WP monad pins the value
theorem IterM.forIn_filterM.h10 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterM 10 := by
  intro h
  have := W.pin fun P Q => h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_filterM`, idx 15 (WeaklyLawfulMonadAttach n): as for the base lemma Std.IterM.forIn_filterM (checks/ItMonadMAHand.lean): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.; the WP monad pins the value
theorem IterM.forIn_filterM.h15 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterM 15 := by
  intro h
  have := NW.pin fun P Q => h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_filterM`, idx 17 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.forIn_filterM (checks/ItMonadMAHand.lean): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.forIn_filterM.h17 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterM 17 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun _ => pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_filterM`, idx 19 (LawfulMonadLiftT n o): as for the base lemma Std.IterM.forIn_filterM (checks/ItMonadMAHand.lean): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.forIn_filterM.h19 : ¬ drop0% Std.Do.Spec.IterM.forIn_filterM 19 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := NW2.pin fun P Q => h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun _ => pure (.up true)) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.forIn_filter`, idx 12 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.forIn_filter (checks/ItMonadMAHand.lean): m = NW2, n = NW (lawful Nat writers), lift adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop.; the WP monad pins the value
theorem IterM.forIn_filter.h12 : ¬ drop0% Std.Do.Spec.IterM.forIn_filter 12 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (it := [0].iterM NW2) (f := fun _ => true) (init := 0) (g := fun c acc => pure (.yield (acc + c))) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_filterMapWithPostcondition`, idx 14 (LawfulMonad n): as for the base lemma Std.IterM.foldM_filterMapWithPostcondition (checks/ItMonadMAHand.lean): m = Id, n = FM (Bool writer whose map and attach flip the flag: bind/pure lawful, weakly lawful attach, lawful lifts from Id and to o = W), list iterator [0]: the left side binds f's operation (resp. attach) directly, the right side maps it.; the WP monad pins the value
theorem IterM.foldM_filterMapWithPostcondition.h14 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMapWithPostcondition 14 := by
  intro h
  have := W.pin fun P Q => h (m := Id) (n := FM) (o := W) (it := [0].iterM Id) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_filterMapWithPostcondition`, idx 23 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.foldM_filterMapWithPostcondition (checks/ItMonadMAHand.lean): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.foldM_filterMapWithPostcondition.h23 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMapWithPostcondition 23 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_filterMapWithPostcondition`, idx 24 (LawfulMonadLiftT n o): as for the base lemma Std.IterM.foldM_filterMapWithPostcondition (checks/ItMonadMAHand.lean): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.foldM_filterMapWithPostcondition.h24 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMapWithPostcondition 24 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := NW2.pin fun P Q => h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => PostconditionT.pure (some b)) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_filterMapM`, idx 14 (LawfulMonad n): as for the base lemma Std.IterM.foldM_filterMapM (checks/ItMonadMAHand.lean): m = Id, n = FM (Bool writer whose map and attach flip the flag: bind/pure lawful, weakly lawful attach, lawful lifts from Id and to o = W), list iterator [0]: the left side binds f's operation (resp. attach) directly, the right side maps it.; the WP monad pins the value
theorem IterM.foldM_filterMapM.h14 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMapM 14 := by
  intro h
  have := W.pin fun P Q => h (m := Id) (n := FM) (o := W) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_filterMapM`, idx 15 (WeaklyLawfulMonadAttach n): as for the base lemma Std.IterM.foldM_filterMapM (checks/ItMonadMAHand.lean): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.; the WP monad pins the value
theorem IterM.foldM_filterMapM.h15 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMapM 15 := by
  intro h
  have := NW.pin fun P Q => h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_filterMapM`, idx 25 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.foldM_filterMapM (checks/ItMonadMAHand.lean): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.foldM_filterMapM.h25 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMapM 25 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => pure (some b)) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_filterMapM`, idx 26 (LawfulMonadLiftT n o): as for the base lemma Std.IterM.foldM_filterMapM (checks/ItMonadMAHand.lean): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.foldM_filterMapM.h26 : ¬ drop0% Std.Do.Spec.IterM.foldM_filterMapM 26 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := NW2.pin fun P Q => h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => pure (some b)) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_mapWithPostcondition`, idx 14 (LawfulMonad n): as for the base lemma Std.IterM.foldM_mapWithPostcondition (checks/ItMonadMAHand.lean): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).; the WP monad pins the value
theorem IterM.foldM_mapWithPostcondition.h14 : ¬ drop0% Std.Do.Spec.IterM.foldM_mapWithPostcondition 14 := by
  intro h
  have := W.pin fun P Q => h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_mapWithPostcondition`, idx 23 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.foldM_mapWithPostcondition (checks/ItMonadMAHand.lean): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.foldM_mapWithPostcondition.h23 : ¬ drop0% Std.Do.Spec.IterM.foldM_mapWithPostcondition 23 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_mapWithPostcondition`, idx 24 (LawfulMonadLiftT n o): as for the base lemma Std.IterM.foldM_mapWithPostcondition (checks/ItMonadMAHand.lean): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.foldM_mapWithPostcondition.h24 : ¬ drop0% Std.Do.Spec.IterM.foldM_mapWithPostcondition 24 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := NW2.pin fun P Q => h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => PostconditionT.pure b) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_mapM`, idx 14 (LawfulMonad n): as for the base lemma Std.IterM.foldM_mapM (checks/ItMonadMAHand.lean): m = Id, n = SM (Bool writer, lawful bind/pure; map flips the flag iff the target type is a subsingleton, attach iff the value type is, so attach is weakly lawful; lawful lifts from Id and to o = W), list iterator [0]: the combinator maps into a subsingleton subtype (flip), the right side maps into β₂/ULift Bool or not at all (no flip).; the WP monad pins the value
theorem IterM.foldM_mapM.h14 : ¬ drop0% Std.Do.Spec.IterM.foldM_mapM 14 := by
  intro h
  have := W.pin fun P Q => h (m := Id) (n := SM) (o := W) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_mapM`, idx 15 (WeaklyLawfulMonadAttach n): as for the base lemma Std.IterM.foldM_mapM (checks/ItMonadMAHand.lean): m = Id, n = NWb (lawful Nat writer whose attach adds one), o = NW, list iterator [0]: the left side attaches f's result, the right side does not.; the WP monad pins the value
theorem IterM.foldM_mapM.h15 : ¬ drop0% Std.Do.Spec.IterM.foldM_mapM 15 := by
  intro h
  have := NW.pin fun P Q => h (m := Id) (n := NWb) (o := NW) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_mapM`, idx 25 (LawfulMonadLiftT m n): as for the base lemma Std.IterM.foldM_mapM (checks/ItMonadMAHand.lean): m = NW2, n = o = NW (lawful Nat writers), lift NW2 → NW adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.foldM_mapM.h25 : ¬ drop0% Std.Do.Spec.IterM.foldM_mapM 25 := by
  intro h
  letI : MonadLift NW2 NW := tickNW2
  letI : IteratorLoop (ListIterator Nat) NW2 NW := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) NW2 NW := evilLoop_lawful
  have := NW.pin fun P Q => h (m := NW2) (n := NW) (o := NW) (it := [0].iterM NW2) (f := fun b => pure b) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW Nat)) 0 (by ev_simp; simp)
  ev_all; simp

-- `Std.Do.Spec.IterM.foldM_mapM`, idx 26 (LawfulMonadLiftT n o): as for the base lemma Std.IterM.foldM_mapM (checks/ItMonadMAHand.lean): m = Id, n = NW, o = NW2 (lawful Nat writers), lift NW → NW2 adds one (not lawful), list iterator [0]; the base iterator's IteratorLoop α m o is evilLoop (returns init for the non-lawful lift).; the WP monad pins the value
theorem IterM.foldM_mapM.h26 : ¬ drop0% Std.Do.Spec.IterM.foldM_mapM 26 := by
  intro h
  letI : MonadLift NW NW2 := tickNW
  letI : IteratorLoop (ListIterator Nat) Id NW2 := evilLoop
  haveI : LawfulIteratorLoop (ListIterator Nat) Id NW2 := evilLoop_lawful
  have := NW2.pin fun P Q => h (m := Id) (n := NW) (o := NW2) (it := [0].iterM Id) (f := fun b => pure b) (init := 0) (g := fun d c => pure (d + c)) (P := P) (Q := Q)
  clear h; revert this
  ev_unfold
  rw [evilLoop_forIn ?h]
  case h => exact not_lawful_of (γ := Nat) (δ := Nat) (fun _ => (⟨1, 0⟩ : NW2 Nat)) 0 (by ev_simp; simp)
  ev_all; simp

end DoSpecAMA.MA

namespace DoSpecAMA.MA.Rem
open Std Std.Iterators Std.Iterators.Types

universe w w' w''

/-- Universe-polymorphic version of filterMap_step_eq (for the removable proofs). -/
theorem filterMap_step_gen {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad n] [Iterator α m β]
    {lift : ⦃α : Type w⦄ → m α → n α} {f : β → PostconditionT n (Option γ)}
    (it : IterM (α := α) m β) :
    (IterM.InternalCombinators.filterMap lift f it).step = (do
      match (← lift it.step).inflate with
      | .yield it' out h => do
        match ← (f out).operation with
        | ⟨none, h'⟩ => pure (.deflate
            (.skip (IterM.InternalCombinators.filterMap lift f it') (by exact .yieldNone h h')))
        | ⟨some out', h'⟩ => pure (.deflate
            (.yield (IterM.InternalCombinators.filterMap lift f it') out' (by exact .yieldSome h h')))
      | .skip it' h => pure (.deflate
          (.skip (IterM.InternalCombinators.filterMap lift f it') (by exact .skip h)))
      | .done h => pure (.deflate (.done (by exact .done h)))) := by
  apply bind_congr; intro s
  obtain ⟨t, rfl⟩ : ∃ t, s = Shrink.deflate t := ⟨s.inflate, Shrink.deflate_inflate.symm⟩
  rcases t with ⟨_ | _ | _, h⟩ <;> (try simp only [Shrink.inflate_deflate]) <;>
    (try erw [Shrink.inflate_deflate]) <;> (try rfl) <;>
    (apply bind_congr; intro r; rcases r with ⟨_ | _, _⟩ <;> rfl)

-- helper copied from checks/ItMonadMAHand.lean: Std.IterM.forIn_filterMap, idx 7 (LawfulMonad m): removable. The filterMap iterator's step only binds and returns pure values in m; the lawful lift m → n (LawfulMonadLiftT) and LawfulMonad n turn it into the base step followed by pure, so the induction of the library proof goes through in n.
theorem forIn_filterMap.h7 : drop% Std.IterM.forIn_filterMap 7 := by
  intro m n α β β₂ γ _ _ _ _ _ _ _ _ _ it f init g
  induction it using IterM.inductSteps generalizing init with | step it ihy ihs
  rw [IterM.forIn_eq_match_step, IterM.forIn_eq_match_step]
  rw [show (it.filterMap f).step = _ from filterMap_step_gen (m := m) (n := m) it]
  simp only [liftM]
  erw [monadLift_bind]; rw [bind_assoc]
  apply bind_congr; intro s
  cases s.inflate using PlausibleIterStep.casesOn
  · rename_i it' out h
    simp only [PostconditionT.operation_pure]
    erw [monadLift_bind]; rw [monadLift_pure, pure_bind]
    split
    · rename_i hfo
      have hn : f out = none := congrArg Subtype.val hfo
      erw [monadLift_pure, pure_bind]
      erw [Shrink.inflate_deflate]
      simp only [hn, pure_bind]
      exact ihy h
    · rename_i out' _ hfo
      have hs : f out = some out' := congrArg Subtype.val hfo
      erw [monadLift_pure, pure_bind]
      erw [Shrink.inflate_deflate]
      simp only [hs]
      apply bind_congr; intro r
      cases r
      · rfl
      · exact ihy h
  · rename_i it' h
    erw [monadLift_pure, pure_bind]
    erw [Shrink.inflate_deflate]
    exact ihs h
  · erw [monadLift_pure, pure_bind]
    erw [Shrink.inflate_deflate]

-- helper copied from checks/ItMonadMAHand.lean: Std.IterM.forIn_filter, idx 6 (LawfulMonad m): removable; filter is filterMap with an if-then-else, so it follows from the proof for forIn_filterMap above.
theorem forIn_filter.h6 : drop% Std.IterM.forIn_filter 6 := by
  intro m n α β γ _ _ _ _ _ _ _ _ _ it f init g
  refine (forIn_filterMap.h7 (it := it) (f := fun b => if f b then some b else none)
    (init := init) (g := g)).trans ?_
  congr 1; funext out acc; cases f out <;> rfl

end DoSpecAMA.MA.Rem

namespace DoSpecAMA.MA
open Std Std.Do Std.Iterators

-- `Std.Do.Spec.IterM.forIn_filterMap` (idx 8): removable; the base equation Std.IterM.forIn_filterMap holds without LawfulMonad m (proof above, copied from the hand8 pass), and the spec follows by rewriting with it.
theorem Spec.IterM.forIn_filterMap.h8 : drop% Std.Do.Spec.IterM.forIn_filterMap 8 := by
  intros; rw [Rem.forIn_filterMap.h7]; assumption

-- `Std.Do.Spec.IterM.forIn_filter` (idx 7): removable; as for forIn_filterMap, via the law-free base equation for forIn_filter.
theorem Spec.IterM.forIn_filter.h7 : drop% Std.Do.Spec.IterM.forIn_filter 7 := by
  intros; rw [Rem.forIn_filter.h6]; assumption

end DoSpecAMA.MA
