import Lean.Elab.Command
-- add the library modules your rows need here (e.g. `import Init`, `import Std.Sat.AIG.CNF`); avoid `import Lean`/`import Std` (1.5 GB)
import Init

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

set_option linter.deprecated false

/-!
Hand pass `PRangeIt` (hand22): private theorems of `Init.Data.Range.Polymorphic.Lemmas`
(`R??.Internal.forIn'_eq_forIn'_iter`, `toList/toArray_eq_…_iter`) and
`Init.Data.Range.Polymorphic.RangeIterator` (`Rxc/Rxo/Rxi.Iterator.instIteratorLoop.loop_eq_wf`,
`loopWf_eq`, `List.length_filter_strict_mono`).

103 verdicts: 90 necessary, 13 removable. Removable: the finiteness instance of the six
`forIn'_eq_forIn'_iter` lemmas that also assume `LawfulUpwardEnumerableLE/LT` (`rxc_of_lawful`,
`rxo_of_lawful`); `wf` of the Rxc/Rxo `loop_eq_wf`/`loopWf_eq` (finite iterator, `wellFounded_of_finite`);
`[LawfulMonad n]` of the three `loopWf_eq` (`rmc`, `rmo`, `rmi`: well-founded induction as in
`checks/RangeLoopHand.lean`, with `loop.wf` unfolded by its private `eq_1`).

Reusable models (copied):
* `M0`, `U1`, `U0`, `NLE`, `NLT`, `NLeast`, `NTopC`, `NTopO` with their `¬` lemmas: from
  `checks/RangeDepAHand.lean` (model table there).
* `T2lt`, `T2le`, `T2least`, `UBad`, `nat_not_rxi`, `rxc_of_rxi`, `rxo_of_rxi`: from
  `checks/RangeDepBHand.lean`.
* `rxc_of_lawful`, `rxo_of_lawful` (finiteness from `LawfulUpwardEnumerable` + `LawfulUpwardEnumerableLE/LT`):
  from `checks/RangeFiniteHand.lean`.

Built here (reusable for the range-loop lemmas):
* `rxcWfF`, `rxoWfF`, `rxiWfF`: `IteratorLoop.WellFounded` holds for the predicate `fun _ _ _ => False`
  on every range iterator (no yield step is plausible for it, and range iterators never skip). With
  `n := Option` and `f := fun … => none` this supplies the loop arguments of any model.
* `liftId`/`liftIdLawful`: the lawful lift `Id → n` (`fun _ _ g x => g x.run`); `liftNone`: the
  unlawful lift `fun _ _ _ _ => none` into `Option`.
* `nat_rxi_not_wf`: on `Nat`, `IteratorLoop.WellFounded (Rxi.Iterator Nat) Id (fun _ _ _ => True)` fails.
-/

namespace PRangeItHand
open Std Std.PRange Std.Iterators

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

-- Rxo finiteness from Rxi finiteness.
theorem rxo_of_rxi {α : Type u} [UpwardEnumerable α] [LT α] [Rxi.IsAlwaysFinite α] :
    Rxo.IsAlwaysFinite α where
  finite init hi := by
    obtain ⟨n, hn⟩ := Rxi.IsAlwaysFinite.finite init; exact ⟨n, by simp [hn]⟩


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

/-- `U0`: one point without successor; every law except `InfinitelyUpwardEnumerable`. -/
inductive U0 | pt deriving DecidableEq
instance : UpwardEnumerable U0 :=
  { succ? := fun _ => none, succMany? := fun n a => if n = 0 then some a else none }
instance : LE U0 := ⟨fun _ _ => True⟩
instance : LT U0 := ⟨fun _ _ => False⟩
instance : DecidableLE U0 := fun _ _ => isTrue trivial
instance : DecidableLT U0 := fun _ _ => isFalse id
instance : Least? U0 := ⟨some .pt⟩
instance : Rxc.HasSize U0 := ⟨fun _ _ => 1⟩
instance : Rxo.HasSize U0 := ⟨fun _ _ => 0⟩
instance : LawfulUpwardEnumerable U0 where
  ne_of_lt _ _ := fun ⟨_, h⟩ => nomatch h
  succMany?_zero _ := rfl
  succMany?_add_one n a := by cases n <;> rfl
instance : LawfulUpwardEnumerableLE U0 := ⟨fun .pt .pt => ⟨fun _ => ⟨0, rfl⟩, fun _ => trivial⟩⟩
instance : LawfulUpwardEnumerableLT U0 := ⟨fun _ _ => ⟨False.elim, fun ⟨_, h⟩ => nomatch h⟩⟩
instance : LawfulUpwardEnumerableLeast? U0 := ⟨fun .pt => ⟨.pt, rfl, 0, rfl⟩⟩
instance : LinearlyUpwardEnumerable U0 := ⟨fun .pt .pt _ => rfl⟩
instance : Rxc.IsAlwaysFinite U0 := ⟨fun _ _ => ⟨1, trivial⟩⟩
instance : Rxo.IsAlwaysFinite U0 := ⟨fun _ _ => ⟨0, id⟩⟩
instance : Rxc.LawfulHasSize U0 := ⟨fun _ _ h => (h trivial).elim, fun _ _ _ _ => rfl, fun _ _ _ _ h => nomatch h⟩
instance : Rxo.LawfulHasSize U0 := ⟨fun _ _ _ => rfl, fun _ _ h => h.elim, fun _ _ _ h => h.elim⟩
theorem U0.not_Inf : ¬ InfinitelyUpwardEnumerable U0 := fun h => nomatch h.isSome_succ? .pt

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

/-- Nat with `≤` always true: `Rxc` ranges never end. -/
def NTopC := Nat
def NTopC.pt (n : Nat) : NTopC := n
instance : UpwardEnumerable NTopC := { succ? := fun (n : Nat) => some (n + 1), succMany? := fun k (n : Nat) => some (n + k) }
instance : LE NTopC := ⟨fun _ _ => True⟩
instance : DecidableLE NTopC := fun _ _ => isTrue trivial
instance : LT NTopC := inferInstanceAs (LT Nat)
instance : DecidableLT NTopC := inferInstanceAs (DecidableLT Nat)
instance : Least? NTopC := ⟨some (NTopC.pt 0)⟩
instance : LawfulUpwardEnumerable NTopC := inferInstanceAs (LawfulUpwardEnumerable Nat)
instance : LawfulUpwardEnumerableLT NTopC := inferInstanceAs (LawfulUpwardEnumerableLT Nat)
instance : LawfulUpwardEnumerableLeast? NTopC := inferInstanceAs (LawfulUpwardEnumerableLeast? Nat)
instance : InfinitelyUpwardEnumerable NTopC := inferInstanceAs (InfinitelyUpwardEnumerable Nat)
instance : LinearlyUpwardEnumerable NTopC := inferInstanceAs (LinearlyUpwardEnumerable Nat)
instance : Rxo.IsAlwaysFinite NTopC := inferInstanceAs (Rxo.IsAlwaysFinite Nat)
theorem NTopC.not_RxcF : ¬ Rxc.IsAlwaysFinite NTopC := fun h => by
  obtain ⟨n, hn⟩ := h.finite (0 : Nat) (0 : Nat); exact hn trivial

/-- Nat with `<` always true: `Rxo` ranges never end. -/
def NTopO := Nat
def NTopO.pt (n : Nat) : NTopO := n
instance : UpwardEnumerable NTopO := { succ? := fun (n : Nat) => some (n + 1), succMany? := fun k (n : Nat) => some (n + k) }
instance : LE NTopO := inferInstanceAs (LE Nat)
instance : DecidableLE NTopO := inferInstanceAs (DecidableLE Nat)
instance : LT NTopO := ⟨fun _ _ => True⟩
instance : DecidableLT NTopO := fun _ _ => isTrue trivial
instance : Least? NTopO := ⟨some (NTopO.pt 0)⟩
instance : LawfulUpwardEnumerable NTopO := inferInstanceAs (LawfulUpwardEnumerable Nat)
instance : LawfulUpwardEnumerableLE NTopO := inferInstanceAs (LawfulUpwardEnumerableLE Nat)
instance : LawfulUpwardEnumerableLeast? NTopO := inferInstanceAs (LawfulUpwardEnumerableLeast? Nat)
instance : InfinitelyUpwardEnumerable NTopO := inferInstanceAs (InfinitelyUpwardEnumerable Nat)
instance : LinearlyUpwardEnumerable NTopO := inferInstanceAs (LinearlyUpwardEnumerable Nat)
instance : Rxc.IsAlwaysFinite NTopO := inferInstanceAs (Rxc.IsAlwaysFinite Nat)
theorem NTopO.not_RxoF : ¬ Rxo.IsAlwaysFinite NTopO := fun h => by
  obtain ⟨n, hn⟩ := h.finite (0 : Nat) (0 : Nat); exact hn trivial



/-! ### `T2lt`: as `T2`, but `<` is always false (not `LawfulUpwardEnumerableLT`) -/

structure T2lt where
  b : Bool
deriving DecidableEq

instance : UpwardEnumerable T2lt where
  succ? a := if a.b then none else some ⟨true⟩

theorem T2lt.succMany?_add_two (n : Nat) (a : T2lt) : succMany? (n + 2) a = none := by
  induction n with
  | zero => obtain ⟨_ | _⟩ := a <;> rfl
  | succ n ih => show (succMany? (n + 2) a).bind succ? = none; rw [ih]; rfl

theorem T2lt.ueLE_iff' {a b : T2lt} : UpwardEnumerable.LE a b ↔ (a = b ∨ succ? a = some b) := by
  constructor
  · rintro ⟨_ | _ | n, h⟩
    · exact Or.inl (Option.some.inj h)
    · exact Or.inr h
    · rw [T2lt.succMany?_add_two] at h; cases h
  · rintro (h | h)
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, h⟩

theorem T2lt.ueLE_iff {a b : T2lt} : UpwardEnumerable.LE a b ↔ (a.b = false ∨ b.b = true) := by
  rw [T2lt.ueLE_iff']; obtain ⟨_ | _⟩ := a <;> obtain ⟨_ | _⟩ := b <;> decide

theorem T2lt.ueLT_iff' {a b : T2lt} : UpwardEnumerable.LT a b ↔ succ? a = some b := by
  constructor
  · rintro ⟨_ | n, h⟩
    · exact h
    · rw [T2lt.succMany?_add_two] at h; cases h
  · intro h; exact ⟨0, h⟩

theorem T2lt.ueLT_iff {a b : T2lt} : UpwardEnumerable.LT a b ↔ (a.b = false ∧ b.b = true) := by
  rw [T2lt.ueLT_iff']; obtain ⟨_ | _⟩ := a <;> obtain ⟨_ | _⟩ := b <;> decide

instance : LawfulUpwardEnumerable T2lt where
  ne_of_lt a b h := by rw [T2lt.ueLT_iff] at h; intro e; subst e; simp_all
  succMany?_zero _ := rfl
  succMany?_add_one _ _ := rfl

instance : Rxi.IsAlwaysFinite T2lt := ⟨fun a => ⟨2, T2lt.succMany?_add_two 0 a⟩⟩

instance : LinearlyUpwardEnumerable T2lt where
  eq_of_succ?_eq a b h := by
    obtain ⟨_ | _⟩ := a <;> obtain ⟨_ | _⟩ := b <;> first | rfl | cases h

instance : Rxi.HasSize T2lt := ⟨fun a => if a.b then 1 else 2⟩

instance : Rxi.LawfulHasSize T2lt where
  size_eq_one_of_succ?_eq_none lo h := by obtain ⟨_ | _⟩ := lo <;> first | rfl | cases h
  size_eq_succ_of_succ?_eq_some lo lo' h := by
    obtain ⟨_ | _⟩ := lo <;> cases h <;> rfl

theorem T2lt.not_inf : ¬ InfinitelyUpwardEnumerable T2lt := fun h => by
  have := h.isSome_succ? ⟨true⟩; cases this

instance : LE T2lt := ⟨fun a b => a.b = false ∨ b.b = true⟩
instance : LT T2lt := ⟨fun a b => False⟩
instance : DecidableLE T2lt := fun a b => inferInstanceAs (Decidable (a.b = false ∨ b.b = true))
instance : DecidableLT T2lt := fun a b => inferInstanceAs (Decidable (False))
instance : Least? T2lt := ⟨some ⟨false⟩⟩
instance : Rxc.IsAlwaysFinite T2lt := rxc_of_rxi
instance : Rxo.IsAlwaysFinite T2lt := rxo_of_rxi

instance : LawfulUpwardEnumerableLE T2lt := ⟨fun a b => T2lt.ueLE_iff.symm⟩

theorem T2lt.not_llt : ¬ LawfulUpwardEnumerableLT T2lt := fun h => by
  have := (h.lt_iff ⟨false⟩ ⟨true⟩).2 ⟨0, rfl⟩; exact this

instance : LawfulUpwardEnumerableLeast? T2lt := ⟨fun a => ⟨⟨false⟩, rfl, T2lt.ueLE_iff.2 (Or.inl rfl)⟩⟩

/-! ### `T2le`: as `T2`, but `≤` is always false (not `LawfulUpwardEnumerableLE`) -/

structure T2le where
  b : Bool
deriving DecidableEq

instance : UpwardEnumerable T2le where
  succ? a := if a.b then none else some ⟨true⟩

theorem T2le.succMany?_add_two (n : Nat) (a : T2le) : succMany? (n + 2) a = none := by
  induction n with
  | zero => obtain ⟨_ | _⟩ := a <;> rfl
  | succ n ih => show (succMany? (n + 2) a).bind succ? = none; rw [ih]; rfl

theorem T2le.ueLE_iff' {a b : T2le} : UpwardEnumerable.LE a b ↔ (a = b ∨ succ? a = some b) := by
  constructor
  · rintro ⟨_ | _ | n, h⟩
    · exact Or.inl (Option.some.inj h)
    · exact Or.inr h
    · rw [T2le.succMany?_add_two] at h; cases h
  · rintro (h | h)
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, h⟩

theorem T2le.ueLE_iff {a b : T2le} : UpwardEnumerable.LE a b ↔ (a.b = false ∨ b.b = true) := by
  rw [T2le.ueLE_iff']; obtain ⟨_ | _⟩ := a <;> obtain ⟨_ | _⟩ := b <;> decide

theorem T2le.ueLT_iff' {a b : T2le} : UpwardEnumerable.LT a b ↔ succ? a = some b := by
  constructor
  · rintro ⟨_ | n, h⟩
    · exact h
    · rw [T2le.succMany?_add_two] at h; cases h
  · intro h; exact ⟨0, h⟩

theorem T2le.ueLT_iff {a b : T2le} : UpwardEnumerable.LT a b ↔ (a.b = false ∧ b.b = true) := by
  rw [T2le.ueLT_iff']; obtain ⟨_ | _⟩ := a <;> obtain ⟨_ | _⟩ := b <;> decide

instance : LawfulUpwardEnumerable T2le where
  ne_of_lt a b h := by rw [T2le.ueLT_iff] at h; intro e; subst e; simp_all
  succMany?_zero _ := rfl
  succMany?_add_one _ _ := rfl

instance : Rxi.IsAlwaysFinite T2le := ⟨fun a => ⟨2, T2le.succMany?_add_two 0 a⟩⟩

instance : LinearlyUpwardEnumerable T2le where
  eq_of_succ?_eq a b h := by
    obtain ⟨_ | _⟩ := a <;> obtain ⟨_ | _⟩ := b <;> first | rfl | cases h

instance : Rxi.HasSize T2le := ⟨fun a => if a.b then 1 else 2⟩

instance : Rxi.LawfulHasSize T2le where
  size_eq_one_of_succ?_eq_none lo h := by obtain ⟨_ | _⟩ := lo <;> first | rfl | cases h
  size_eq_succ_of_succ?_eq_some lo lo' h := by
    obtain ⟨_ | _⟩ := lo <;> cases h <;> rfl

theorem T2le.not_inf : ¬ InfinitelyUpwardEnumerable T2le := fun h => by
  have := h.isSome_succ? ⟨true⟩; cases this

instance : LE T2le := ⟨fun a b => False⟩
instance : LT T2le := ⟨fun a b => a.b = false ∧ b.b = true⟩
instance : DecidableLE T2le := fun a b => inferInstanceAs (Decidable (False))
instance : DecidableLT T2le := fun a b => inferInstanceAs (Decidable (a.b = false ∧ b.b = true))
instance : Least? T2le := ⟨some ⟨false⟩⟩
instance : Rxc.IsAlwaysFinite T2le := rxc_of_rxi
instance : Rxo.IsAlwaysFinite T2le := rxo_of_rxi

theorem T2le.not_lle : ¬ LawfulUpwardEnumerableLE T2le := fun h => by
  have := (h.le_iff ⟨false⟩ ⟨false⟩).2 ⟨0, rfl⟩; exact this

instance : LawfulUpwardEnumerableLT T2le := ⟨fun a b => T2le.ueLT_iff.symm⟩

instance : LawfulUpwardEnumerableLeast? T2le := ⟨fun a => ⟨⟨false⟩, rfl, T2le.ueLE_iff.2 (Or.inl rfl)⟩⟩

/-! ### `T2least`: as `T2`, but `least? = some ⟨true⟩` (not `LawfulUpwardEnumerableLeast?`) -/

structure T2least where
  b : Bool
deriving DecidableEq

instance : UpwardEnumerable T2least where
  succ? a := if a.b then none else some ⟨true⟩

theorem T2least.succMany?_add_two (n : Nat) (a : T2least) : succMany? (n + 2) a = none := by
  induction n with
  | zero => obtain ⟨_ | _⟩ := a <;> rfl
  | succ n ih => show (succMany? (n + 2) a).bind succ? = none; rw [ih]; rfl

theorem T2least.ueLE_iff' {a b : T2least} : UpwardEnumerable.LE a b ↔ (a = b ∨ succ? a = some b) := by
  constructor
  · rintro ⟨_ | _ | n, h⟩
    · exact Or.inl (Option.some.inj h)
    · exact Or.inr h
    · rw [T2least.succMany?_add_two] at h; cases h
  · rintro (h | h)
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, h⟩

theorem T2least.ueLE_iff {a b : T2least} : UpwardEnumerable.LE a b ↔ (a.b = false ∨ b.b = true) := by
  rw [T2least.ueLE_iff']; obtain ⟨_ | _⟩ := a <;> obtain ⟨_ | _⟩ := b <;> decide

theorem T2least.ueLT_iff' {a b : T2least} : UpwardEnumerable.LT a b ↔ succ? a = some b := by
  constructor
  · rintro ⟨_ | n, h⟩
    · exact h
    · rw [T2least.succMany?_add_two] at h; cases h
  · intro h; exact ⟨0, h⟩

theorem T2least.ueLT_iff {a b : T2least} : UpwardEnumerable.LT a b ↔ (a.b = false ∧ b.b = true) := by
  rw [T2least.ueLT_iff']; obtain ⟨_ | _⟩ := a <;> obtain ⟨_ | _⟩ := b <;> decide

instance : LawfulUpwardEnumerable T2least where
  ne_of_lt a b h := by rw [T2least.ueLT_iff] at h; intro e; subst e; simp_all
  succMany?_zero _ := rfl
  succMany?_add_one _ _ := rfl

instance : Rxi.IsAlwaysFinite T2least := ⟨fun a => ⟨2, T2least.succMany?_add_two 0 a⟩⟩

instance : LinearlyUpwardEnumerable T2least where
  eq_of_succ?_eq a b h := by
    obtain ⟨_ | _⟩ := a <;> obtain ⟨_ | _⟩ := b <;> first | rfl | cases h

instance : Rxi.HasSize T2least := ⟨fun a => if a.b then 1 else 2⟩

instance : Rxi.LawfulHasSize T2least where
  size_eq_one_of_succ?_eq_none lo h := by obtain ⟨_ | _⟩ := lo <;> first | rfl | cases h
  size_eq_succ_of_succ?_eq_some lo lo' h := by
    obtain ⟨_ | _⟩ := lo <;> cases h <;> rfl

theorem T2least.not_inf : ¬ InfinitelyUpwardEnumerable T2least := fun h => by
  have := h.isSome_succ? ⟨true⟩; cases this

instance : LE T2least := ⟨fun a b => a.b = false ∨ b.b = true⟩
instance : LT T2least := ⟨fun a b => a.b = false ∧ b.b = true⟩
instance : DecidableLE T2least := fun a b => inferInstanceAs (Decidable (a.b = false ∨ b.b = true))
instance : DecidableLT T2least := fun a b => inferInstanceAs (Decidable (a.b = false ∧ b.b = true))
instance : Least? T2least := ⟨some ⟨true⟩⟩
instance : Rxc.IsAlwaysFinite T2least := rxc_of_rxi
instance : Rxo.IsAlwaysFinite T2least := rxo_of_rxi

instance : LawfulUpwardEnumerableLE T2least := ⟨fun a b => T2least.ueLE_iff.symm⟩

instance : LawfulUpwardEnumerableLT T2least := ⟨fun a b => T2least.ueLT_iff.symm⟩

theorem T2least.not_lleast : ¬ LawfulUpwardEnumerableLeast? T2least := fun h => by
  obtain ⟨i, hi, hle⟩ := h.least?_le ⟨false⟩
  cases hi; simp [T2least.ueLE_iff] at hle

/-! ### `UBad`: one element, `succ? = none`, but `succMany? 1 a = some a` (not lawful)

Satisfies `Rxi.IsAlwaysFinite`, `LawfulUpwardEnumerableLE/LT/Least?` (with `≤`, `<` always true),
`Rxi.LawfulHasSize`, `LinearlyUpwardEnumerable`; violates `LawfulUpwardEnumerable` and
`InfinitelyUpwardEnumerable`. -/

structure UBad where
deriving DecidableEq

instance : UpwardEnumerable UBad where
  succ? _ := none
  succMany? n _ := if n ≤ 1 then some ⟨⟩ else none

theorem UBad.not_lue : ¬ LawfulUpwardEnumerable UBad := fun h => by
  have := h.succMany?_add_one 0 ⟨⟩; cases this

instance : Rxi.IsAlwaysFinite UBad := ⟨fun _ => ⟨2, rfl⟩⟩
instance : LinearlyUpwardEnumerable UBad := ⟨fun _ _ _ => rfl⟩
instance : LE UBad := ⟨fun _ _ => True⟩
instance : LT UBad := ⟨fun _ _ => True⟩
instance : DecidableLE UBad := fun _ _ => instDecidableTrue
instance : DecidableLT UBad := fun _ _ => instDecidableTrue
instance : Least? UBad := ⟨some ⟨⟩⟩
instance : LawfulUpwardEnumerableLE UBad := ⟨fun _ _ => ⟨fun _ => ⟨0, rfl⟩, fun _ => trivial⟩⟩
instance : LawfulUpwardEnumerableLT UBad := ⟨fun _ _ => ⟨fun _ => ⟨0, rfl⟩, fun _ => trivial⟩⟩
instance : LawfulUpwardEnumerableLeast? UBad := ⟨fun _ => ⟨⟨⟩, rfl, 0, rfl⟩⟩
instance : Rxi.HasSize UBad := ⟨fun _ => 1⟩
instance : Rxi.LawfulHasSize UBad where
  size_eq_one_of_succ?_eq_none _ _ := rfl
  size_eq_succ_of_succ?_eq_some _ _ h := by cases h
instance : Rxc.IsAlwaysFinite UBad := rxc_of_rxi
instance : Rxo.IsAlwaysFinite UBad := rxo_of_rxi

theorem nat_not_rxi : ¬ Rxi.IsAlwaysFinite Nat := fun h => by
  obtain ⟨n, hn⟩ := h.finite 0; cases hn


/-! ## Generic loop helpers -/

theorem rxcWfF {α : Type u} [UpwardEnumerable α] [LE α] [DecidableLE α] {γ : Type v} :
    IteratorLoop.WellFounded (Rxc.Iterator α) Id (γ := γ) (fun _ _ _ => False) :=
  ⟨fun p => ⟨p, fun q hq => by
    exfalso
    rcases hq with ⟨_, _, h⟩ | ⟨h, _⟩
    · exact h
    · rw [Rxc.Iterator.Monadic.isPlausibleStep_iff, Rxc.Iterator.Monadic.step] at h
      split at h
      · cases h
      · split at h <;> cases h⟩⟩

theorem rxoWfF {α : Type u} [UpwardEnumerable α] [LT α] [DecidableLT α] {γ : Type v} :
    IteratorLoop.WellFounded (Rxo.Iterator α) Id (γ := γ) (fun _ _ _ => False) :=
  ⟨fun p => ⟨p, fun q hq => by
    exfalso
    rcases hq with ⟨_, _, h⟩ | ⟨h, _⟩
    · exact h
    · rw [Rxo.Iterator.Monadic.isPlausibleStep_iff, Rxo.Iterator.Monadic.step] at h
      split at h
      · cases h
      · split at h <;> cases h⟩⟩

theorem rxiWfF {α : Type u} [UpwardEnumerable α] {γ : Type v} :
    IteratorLoop.WellFounded (Rxi.Iterator α) Id (γ := γ) (fun _ _ _ => False) :=
  ⟨fun p => ⟨p, fun q hq => by
    exfalso
    rcases hq with ⟨_, _, h⟩ | ⟨h, _⟩
    · exact h
    · rw [Rxi.Iterator.Monadic.isPlausibleStep_iff, Rxi.Iterator.Monadic.step] at h
      split at h <;> cases h⟩⟩

/-- The lawful lift `Id → n`. -/
def liftId {n : Type u → Type w} : (γ δ : Type u) → (γ → n δ) → Id γ → n δ := fun _ _ g x => g x.run

theorem liftIdLawful {n : Type u → Type w} [Monad n] :
    Std.Internal.LawfulMonadLiftBindFunction (m := Id) (n := n) liftId :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

instance : Rxi.IsAlwaysFinite U0 := ⟨fun _ => ⟨1, rfl⟩⟩

/-- An unlawful lift `Id → Option` (always `none`). -/
def liftNone : (γ δ : Type) → (γ → Option δ) → Id γ → Option δ := fun _ _ _ _ => none

theorem nat_rxi_not_wf :
    ¬ IteratorLoop.WellFounded (Rxi.Iterator Nat) Id (γ := Unit) (fun _ _ _ => True) := fun hw => by
  have key : ∀ p, Acc (IteratorLoop.rel (Rxi.Iterator Nat) Id (γ := Unit) (fun _ _ _ => True)) p →
      ∀ k : Nat, p.1 = ⟨⟨some k⟩⟩ → False := by
    intro p hp
    induction hp with
    | intro p _ ih =>
      intro k hk
      refine ih (⟨⟨some (k + 1)⟩⟩, ()) (Or.inl ⟨k, ?_, trivial⟩) (k + 1) rfl
      rw [hk, Rxi.Iterator.Monadic.isPlausibleStep_iff]; rfl
  exact key _ (hw.apply (⟨⟨some 0⟩⟩, ())) 0 rfl


/-! ## Verdicts -/

-- `Std.Rcc.Internal.forIn'_eq_forIn'_iter` (hypothesis 4, inst : Std.PRange.LawfulUpwardEnumerableLE α): necessary; NLE (Nat with a ≤ b + 1; LUE/LLT/LLeast/RxcF/RxoF hold) violates LawfulUpwardEnumerableLE.
theorem v0 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rcc.Internal.forIn'_eq_forIn'_iter 4 :=
  fun H => NLE.not_LLE (H (α := NLE) (r := ⟨NLE.pt 0, NLE.pt 0⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rcc.Internal.forIn'_eq_forIn'_iter` (hypothesis 5, inst : Std.Rxc.IsAlwaysFinite α): removable; derivable: Rxc.IsAlwaysFinite follows from LawfulUpwardEnumerable + LawfulUpwardEnumerableLE (rxc_of_lawful).
theorem v1 : indep% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rcc.Internal.forIn'_eq_forIn'_iter 5 :=
  by intro α; intros; exact rxc_of_lawful (α := α)

-- `Std.Rcc.Internal.forIn'_eq_forIn'_iter` (hypothesis 6, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v2 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rcc.Internal.forIn'_eq_forIn'_iter 6 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt, M0.pt⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rcc.Internal.toArray_eq_toArray_iter` (hypothesis 4, inst : Std.Rxc.IsAlwaysFinite α): necessary; NTopC (Nat with ≤ always true; LUE holds) is not Rxc-finite.
theorem v3 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rcc.Internal.toArray_eq_toArray_iter 4 :=
  fun H => NTopC.not_RxcF (H (α := NTopC) (r := ⟨NTopC.pt 0, NTopC.pt 0⟩))

-- `Std.Rcc.Internal.toArray_eq_toArray_iter` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v4 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rcc.Internal.toArray_eq_toArray_iter 5 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt, M0.pt⟩))

-- `Std.Rcc.Internal.toList_eq_toList_iter` (hypothesis 4, inst : Std.Rxc.IsAlwaysFinite α): necessary; NTopC (Nat with ≤ always true; LUE holds) is not Rxc-finite.
theorem v5 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rcc.Internal.toList_eq_toList_iter 4 :=
  fun H => NTopC.not_RxcF (H (α := NTopC) (r := ⟨NTopC.pt 0, NTopC.pt 0⟩))

-- `Std.Rcc.Internal.toList_eq_toList_iter` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v6 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rcc.Internal.toList_eq_toList_iter 5 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt, M0.pt⟩))

-- `Std.Rci.Internal.forIn'_eq_forIn'_iter` (hypothesis 3, inst : Std.PRange.LawfulUpwardEnumerableLE α): necessary; T2le (false → true, ≤ always false; LUE/RxiF hold) violates LawfulUpwardEnumerableLE.
theorem v7 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rci.Internal.forIn'_eq_forIn'_iter 3 :=
  fun H => T2le.not_lle (H (α := T2le) (r := ⟨(⟨false⟩ : T2le)⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rci.Internal.forIn'_eq_forIn'_iter` (hypothesis 4, inst : Std.Rxi.IsAlwaysFinite α): necessary; Nat with the library instances (all laws) is not Rxi-finite.
theorem v8 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rci.Internal.forIn'_eq_forIn'_iter 4 :=
  fun H => nat_not_rxi (H (α := Nat) (r := ⟨(0 : Nat)⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rci.Internal.forIn'_eq_forIn'_iter` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; UBad (one point, succ? = none, succMany? 1 = some; LLE/LLT/LLeast/RxiF hold) violates LawfulUpwardEnumerable.
theorem v9 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rci.Internal.forIn'_eq_forIn'_iter 5 :=
  fun H => UBad.not_lue (H (α := UBad) (r := ⟨(⟨⟩ : UBad)⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rci.Internal.toArray_eq_toArray_iter` (hypothesis 2, inst : Std.Rxi.IsAlwaysFinite α): necessary; Nat with the library instances (all laws) is not Rxi-finite.
theorem v10 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rci.Internal.toArray_eq_toArray_iter 2 :=
  fun H => nat_not_rxi (H (α := Nat) (r := ⟨(0 : Nat)⟩))

-- `Std.Rci.Internal.toArray_eq_toArray_iter` (hypothesis 3, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; UBad (one point, succ? = none, succMany? 1 = some; LLE/LLT/LLeast/RxiF hold) violates LawfulUpwardEnumerable.
theorem v11 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rci.Internal.toArray_eq_toArray_iter 3 :=
  fun H => UBad.not_lue (H (α := UBad) (r := ⟨(⟨⟩ : UBad)⟩))

-- `Std.Rci.Internal.toList_eq_toList_iter` (hypothesis 2, inst : Std.Rxi.IsAlwaysFinite α): necessary; Nat with the library instances (all laws) is not Rxi-finite.
theorem v12 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rci.Internal.toList_eq_toList_iter 2 :=
  fun H => nat_not_rxi (H (α := Nat) (r := ⟨(0 : Nat)⟩))

-- `Std.Rci.Internal.toList_eq_toList_iter` (hypothesis 3, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; UBad (one point, succ? = none, succMany? 1 = some; LLE/LLT/LLeast/RxiF hold) violates LawfulUpwardEnumerable.
theorem v13 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rci.Internal.toList_eq_toList_iter 3 :=
  fun H => UBad.not_lue (H (α := UBad) (r := ⟨(⟨⟩ : UBad)⟩))

-- `Std.Rco.Internal.forIn'_eq_forIn'_iter` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerableLE α): necessary; NLE (Nat with a ≤ b + 1; LUE/LLT/LLeast/RxcF/RxoF hold) violates LawfulUpwardEnumerableLE.
theorem v14 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rco.Internal.forIn'_eq_forIn'_iter 5 :=
  fun H => NLE.not_LLE (H (α := NLE) (r := ⟨NLE.pt 0, NLE.pt 0⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rco.Internal.forIn'_eq_forIn'_iter` (hypothesis 6, inst : Std.PRange.LawfulUpwardEnumerableLT α): necessary; NLT (Nat with a < b + 1; LUE/LLE/LLeast/RxcF/RxoF hold) violates LawfulUpwardEnumerableLT.
theorem v15 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rco.Internal.forIn'_eq_forIn'_iter 6 :=
  fun H => NLT.not_LLT (H (α := NLT) (r := ⟨NLT.pt 0, NLT.pt 0⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rco.Internal.forIn'_eq_forIn'_iter` (hypothesis 7, inst : Std.Rxo.IsAlwaysFinite α): removable; derivable: Rxo.IsAlwaysFinite follows from LawfulUpwardEnumerable + LawfulUpwardEnumerableLT (rxo_of_lawful).
theorem v16 : indep% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rco.Internal.forIn'_eq_forIn'_iter 7 :=
  by intro α; intros; exact rxo_of_lawful (α := α)

-- `Std.Rco.Internal.forIn'_eq_forIn'_iter` (hypothesis 8, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v17 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rco.Internal.forIn'_eq_forIn'_iter 8 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt, M0.pt⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rco.Internal.toArray_eq_toArray_iter` (hypothesis 4, inst : Std.Rxo.IsAlwaysFinite α): necessary; NTopO (Nat with < always true; LUE holds) is not Rxo-finite.
theorem v18 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rco.Internal.toArray_eq_toArray_iter 4 :=
  fun H => NTopO.not_RxoF (H (α := NTopO) (r := ⟨NTopO.pt 0, NTopO.pt 0⟩))

-- `Std.Rco.Internal.toArray_eq_toArray_iter` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v19 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rco.Internal.toArray_eq_toArray_iter 5 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt, M0.pt⟩))

-- `Std.Rco.Internal.toList_eq_toList_iter` (hypothesis 4, inst : Std.Rxo.IsAlwaysFinite α): necessary; NTopO (Nat with < always true; LUE holds) is not Rxo-finite.
theorem v20 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rco.Internal.toList_eq_toList_iter 4 :=
  fun H => NTopO.not_RxoF (H (α := NTopO) (r := ⟨NTopO.pt 0, NTopO.pt 0⟩))

-- `Std.Rco.Internal.toList_eq_toList_iter` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v21 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rco.Internal.toList_eq_toList_iter 5 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt, M0.pt⟩))

-- `Std.Ric.Internal.forIn'_eq_forIn'_iter` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerableLE α): necessary; NLE (Nat with a ≤ b + 1; LUE/LLT/LLeast/RxcF/RxoF hold) violates LawfulUpwardEnumerableLE.
theorem v22 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Ric.Internal.forIn'_eq_forIn'_iter 5 :=
  fun H => NLE.not_LLE (H (α := NLE) (r := ⟨NLE.pt 0⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Ric.Internal.forIn'_eq_forIn'_iter` (hypothesis 6, inst : Std.PRange.LawfulUpwardEnumerableLeast? α): necessary; NLeast (Nat with least? = some 1; LUE/LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerableLeast?.
theorem v23 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Ric.Internal.forIn'_eq_forIn'_iter 6 :=
  fun H => NLeast.not_LLeast (H (α := NLeast) (r := ⟨NLeast.pt 0⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Ric.Internal.forIn'_eq_forIn'_iter` (hypothesis 7, inst : Std.Rxc.IsAlwaysFinite α): removable; derivable: Rxc.IsAlwaysFinite follows from LawfulUpwardEnumerable + LawfulUpwardEnumerableLE (rxc_of_lawful).
theorem v24 : indep% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Ric.Internal.forIn'_eq_forIn'_iter 7 :=
  by intro α; intros; exact rxc_of_lawful (α := α)

-- `Std.Ric.Internal.forIn'_eq_forIn'_iter` (hypothesis 8, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; U1 (one point, succ? = some, succMany? 1 = none; LLE/LLT/LLeast/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v25 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Ric.Internal.forIn'_eq_forIn'_iter 8 :=
  fun H => U1.not_LUE (H (α := U1) (r := ⟨U1.pt⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Ric.Internal.toArray_eq_toArray_iter` (hypothesis 5, inst : Std.Rxc.IsAlwaysFinite α): necessary; NTopC (Nat with ≤ always true; LUE holds) is not Rxc-finite.
theorem v26 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Ric.Internal.toArray_eq_toArray_iter 5 :=
  fun H => NTopC.not_RxcF (H (α := NTopC) (r := ⟨NTopC.pt 0⟩))

-- `Std.Ric.Internal.toArray_eq_toArray_iter` (hypothesis 6, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v27 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Ric.Internal.toArray_eq_toArray_iter 6 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt⟩))

-- `Std.Ric.Internal.toList_eq_toList_iter` (hypothesis 5, inst : Std.Rxc.IsAlwaysFinite α): necessary; NTopC (Nat with ≤ always true; LUE holds) is not Rxc-finite.
theorem v28 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Ric.Internal.toList_eq_toList_iter 5 :=
  fun H => NTopC.not_RxcF (H (α := NTopC) (r := ⟨NTopC.pt 0⟩))

-- `Std.Ric.Internal.toList_eq_toList_iter` (hypothesis 6, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v29 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Ric.Internal.toList_eq_toList_iter 6 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt⟩))

-- `Std.Rii.Internal.forIn'_eq_forIn'_iter` (hypothesis 3, inst : Std.PRange.LawfulUpwardEnumerableLeast? α): necessary; T2least (false → true, least? = some true; LUE/RxiF hold) violates LawfulUpwardEnumerableLeast?.
theorem v30 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rii.Internal.forIn'_eq_forIn'_iter 3 :=
  fun H => T2least.not_lleast (H (α := T2least) (r := ⟨⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.Internal.forIn'_eq_forIn'_iter` (hypothesis 4, inst : Std.Rxi.IsAlwaysFinite α): necessary; Nat with the library instances (all laws) is not Rxi-finite.
theorem v31 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rii.Internal.forIn'_eq_forIn'_iter 4 :=
  fun H => nat_not_rxi (H (α := Nat) (r := ⟨⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.Internal.forIn'_eq_forIn'_iter` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; UBad (one point, succ? = none, succMany? 1 = some; LLE/LLT/LLeast/RxiF hold) violates LawfulUpwardEnumerable.
theorem v32 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rii.Internal.forIn'_eq_forIn'_iter 5 :=
  fun H => UBad.not_lue (H (α := UBad) (r := ⟨⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.Internal.toArray_eq_toArray_iter` (hypothesis 3, inst : Std.Rxi.IsAlwaysFinite α): necessary; Nat with the library instances (all laws) is not Rxi-finite.
theorem v33 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rii.Internal.toArray_eq_toArray_iter 3 :=
  fun H => nat_not_rxi (H (α := Nat) (r := ⟨⟩))

-- `Std.Rii.Internal.toArray_eq_toArray_iter` (hypothesis 4, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; UBad (one point, succ? = none, succMany? 1 = some; LLE/LLT/LLeast/RxiF hold) violates LawfulUpwardEnumerable.
theorem v34 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rii.Internal.toArray_eq_toArray_iter 4 :=
  fun H => UBad.not_lue (H (α := UBad) (r := ⟨⟩))

-- `Std.Rii.Internal.toList_eq_toList_iter` (hypothesis 3, inst : Std.Rxi.IsAlwaysFinite α): necessary; Nat with the library instances (all laws) is not Rxi-finite.
theorem v35 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rii.Internal.toList_eq_toList_iter 3 :=
  fun H => nat_not_rxi (H (α := Nat) (r := ⟨⟩))

-- `Std.Rii.Internal.toList_eq_toList_iter` (hypothesis 4, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; UBad (one point, succ? = none, succMany? 1 = some; LLE/LLT/LLeast/RxiF hold) violates LawfulUpwardEnumerable.
theorem v36 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rii.Internal.toList_eq_toList_iter 4 :=
  fun H => UBad.not_lue (H (α := UBad) (r := ⟨⟩))

-- `Std.Rio.Internal.forIn'_eq_forIn'_iter` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerableLT α): necessary; NLT (Nat with a < b + 1; LUE/LLE/LLeast/RxcF/RxoF hold) violates LawfulUpwardEnumerableLT.
theorem v37 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rio.Internal.forIn'_eq_forIn'_iter 5 :=
  fun H => NLT.not_LLT (H (α := NLT) (r := ⟨NLT.pt 0⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rio.Internal.forIn'_eq_forIn'_iter` (hypothesis 6, inst : Std.PRange.LawfulUpwardEnumerableLeast? α): necessary; NLeast (Nat with least? = some 1; LUE/LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerableLeast?.
theorem v38 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rio.Internal.forIn'_eq_forIn'_iter 6 :=
  fun H => NLeast.not_LLeast (H (α := NLeast) (r := ⟨NLeast.pt 0⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rio.Internal.forIn'_eq_forIn'_iter` (hypothesis 7, inst : Std.Rxo.IsAlwaysFinite α): removable; derivable: Rxo.IsAlwaysFinite follows from LawfulUpwardEnumerable + LawfulUpwardEnumerableLT (rxo_of_lawful).
theorem v39 : indep% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rio.Internal.forIn'_eq_forIn'_iter 7 :=
  by intro α; intros; exact rxo_of_lawful (α := α)

-- `Std.Rio.Internal.forIn'_eq_forIn'_iter` (hypothesis 8, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; U1 (one point, succ? = some, succMany? 1 = none; LLE/LLT/LLeast/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v40 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rio.Internal.forIn'_eq_forIn'_iter 8 :=
  fun H => U1.not_LUE (H (α := U1) (r := ⟨U1.pt⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rio.Internal.toArray_eq_toArray_iter` (hypothesis 5, inst : Std.Rxo.IsAlwaysFinite α): necessary; NTopO (Nat with < always true; LUE holds) is not Rxo-finite.
theorem v41 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rio.Internal.toArray_eq_toArray_iter 5 :=
  fun H => NTopO.not_RxoF (H (α := NTopO) (r := ⟨NTopO.pt 0⟩))

-- `Std.Rio.Internal.toArray_eq_toArray_iter` (hypothesis 6, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v42 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rio.Internal.toArray_eq_toArray_iter 6 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt⟩))

-- `Std.Rio.Internal.toList_eq_toList_iter` (hypothesis 5, inst : Std.Rxo.IsAlwaysFinite α): necessary; NTopO (Nat with < always true; LUE holds) is not Rxo-finite.
theorem v43 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rio.Internal.toList_eq_toList_iter 5 :=
  fun H => NTopO.not_RxoF (H (α := NTopO) (r := ⟨NTopO.pt 0⟩))

-- `Std.Rio.Internal.toList_eq_toList_iter` (hypothesis 6, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v44 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Rio.Internal.toList_eq_toList_iter 6 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt⟩))

-- `Std.Roc.Internal.forIn'_eq_forIn'_iter` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerableLE α): necessary; NLE (Nat with a ≤ b + 1; LUE/LLT/LLeast/RxcF/RxoF hold) violates LawfulUpwardEnumerableLE.
theorem v45 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roc.Internal.forIn'_eq_forIn'_iter 5 :=
  fun H => NLE.not_LLE (H (α := NLE) (r := ⟨NLE.pt 0, NLE.pt 0⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roc.Internal.forIn'_eq_forIn'_iter` (hypothesis 6, inst : Std.PRange.LawfulUpwardEnumerableLT α): necessary; NLT (Nat with a < b + 1; LUE/LLE/LLeast/RxcF/RxoF hold) violates LawfulUpwardEnumerableLT.
theorem v46 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roc.Internal.forIn'_eq_forIn'_iter 6 :=
  fun H => NLT.not_LLT (H (α := NLT) (r := ⟨NLT.pt 0, NLT.pt 0⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roc.Internal.forIn'_eq_forIn'_iter` (hypothesis 7, inst : Std.Rxc.IsAlwaysFinite α): removable; derivable: Rxc.IsAlwaysFinite follows from LawfulUpwardEnumerable + LawfulUpwardEnumerableLE (rxc_of_lawful).
theorem v47 : indep% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roc.Internal.forIn'_eq_forIn'_iter 7 :=
  by intro α; intros; exact rxc_of_lawful (α := α)

-- `Std.Roc.Internal.forIn'_eq_forIn'_iter` (hypothesis 8, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v48 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roc.Internal.forIn'_eq_forIn'_iter 8 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt, M0.pt⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roc.Internal.toArray_eq_toArray_iter` (hypothesis 4, inst : Std.Rxc.IsAlwaysFinite α): necessary; NTopC (Nat with ≤ always true; LUE holds) is not Rxc-finite.
theorem v49 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roc.Internal.toArray_eq_toArray_iter 4 :=
  fun H => NTopC.not_RxcF (H (α := NTopC) (r := ⟨NTopC.pt 0, NTopC.pt 0⟩))

-- `Std.Roc.Internal.toArray_eq_toArray_iter` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v50 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roc.Internal.toArray_eq_toArray_iter 5 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt, M0.pt⟩))

-- `Std.Roc.Internal.toList_eq_toList_iter` (hypothesis 4, inst : Std.Rxc.IsAlwaysFinite α): necessary; NTopC (Nat with ≤ always true; LUE holds) is not Rxc-finite.
theorem v51 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roc.Internal.toList_eq_toList_iter 4 :=
  fun H => NTopC.not_RxcF (H (α := NTopC) (r := ⟨NTopC.pt 0, NTopC.pt 0⟩))

-- `Std.Roc.Internal.toList_eq_toList_iter` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v52 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roc.Internal.toList_eq_toList_iter 5 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt, M0.pt⟩))

-- `Std.Roi.Internal.forIn'_eq_forIn'_iter` (hypothesis 3, inst : Std.PRange.LawfulUpwardEnumerableLT α): necessary; T2lt (false → true, < always false; LUE/RxiF hold) violates LawfulUpwardEnumerableLT.
theorem v53 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roi.Internal.forIn'_eq_forIn'_iter 3 :=
  fun H => T2lt.not_llt (H (α := T2lt) (r := ⟨(⟨false⟩ : T2lt)⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roi.Internal.forIn'_eq_forIn'_iter` (hypothesis 4, inst : Std.Rxi.IsAlwaysFinite α): necessary; Nat with the library instances (all laws) is not Rxi-finite.
theorem v54 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roi.Internal.forIn'_eq_forIn'_iter 4 :=
  fun H => nat_not_rxi (H (α := Nat) (r := ⟨(0 : Nat)⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roi.Internal.forIn'_eq_forIn'_iter` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; UBad (one point, succ? = none, succMany? 1 = some; LLE/LLT/LLeast/RxiF hold) violates LawfulUpwardEnumerable.
theorem v55 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roi.Internal.forIn'_eq_forIn'_iter 5 :=
  fun H => UBad.not_lue (H (α := UBad) (r := ⟨(⟨⟩ : UBad)⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roi.Internal.toArray_eq_toArray_iter` (hypothesis 2, inst : Std.Rxi.IsAlwaysFinite α): necessary; Nat with the library instances (all laws) is not Rxi-finite.
theorem v56 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roi.Internal.toArray_eq_toArray_iter 2 :=
  fun H => nat_not_rxi (H (α := Nat) (r := ⟨(0 : Nat)⟩))

-- `Std.Roi.Internal.toArray_eq_toArray_iter` (hypothesis 3, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; UBad (one point, succ? = none, succMany? 1 = some; LLE/LLT/LLeast/RxiF hold) violates LawfulUpwardEnumerable.
theorem v57 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roi.Internal.toArray_eq_toArray_iter 3 :=
  fun H => UBad.not_lue (H (α := UBad) (r := ⟨(⟨⟩ : UBad)⟩))

-- `Std.Roi.Internal.toList_eq_toList_iter` (hypothesis 2, inst : Std.Rxi.IsAlwaysFinite α): necessary; Nat with the library instances (all laws) is not Rxi-finite.
theorem v58 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roi.Internal.toList_eq_toList_iter 2 :=
  fun H => nat_not_rxi (H (α := Nat) (r := ⟨(0 : Nat)⟩))

-- `Std.Roi.Internal.toList_eq_toList_iter` (hypothesis 3, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; UBad (one point, succ? = none, succMany? 1 = some; LLE/LLT/LLeast/RxiF hold) violates LawfulUpwardEnumerable.
theorem v59 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roi.Internal.toList_eq_toList_iter 3 :=
  fun H => UBad.not_lue (H (α := UBad) (r := ⟨(⟨⟩ : UBad)⟩))

-- `Std.Roo.Internal.forIn'_eq_forIn'_iter` (hypothesis 4, inst : Std.PRange.LawfulUpwardEnumerableLT α): necessary; NLT (Nat with a < b + 1; LUE/LLE/LLeast/RxcF/RxoF hold) violates LawfulUpwardEnumerableLT.
theorem v60 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roo.Internal.forIn'_eq_forIn'_iter 4 :=
  fun H => NLT.not_LLT (H (α := NLT) (r := ⟨NLT.pt 0, NLT.pt 0⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roo.Internal.forIn'_eq_forIn'_iter` (hypothesis 5, inst : Std.Rxo.IsAlwaysFinite α): removable; derivable: Rxo.IsAlwaysFinite follows from LawfulUpwardEnumerable + LawfulUpwardEnumerableLT (rxo_of_lawful).
theorem v61 : indep% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roo.Internal.forIn'_eq_forIn'_iter 5 :=
  by intro α; intros; exact rxo_of_lawful (α := α)

-- `Std.Roo.Internal.forIn'_eq_forIn'_iter` (hypothesis 6, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v62 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roo.Internal.forIn'_eq_forIn'_iter 6 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt, M0.pt⟩) (γ := Nat) (init := 0) (m := Id) (f := fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roo.Internal.toArray_eq_toArray_iter` (hypothesis 4, inst : Std.Rxo.IsAlwaysFinite α): necessary; NTopO (Nat with < always true; LUE holds) is not Rxo-finite.
theorem v63 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roo.Internal.toArray_eq_toArray_iter 4 :=
  fun H => NTopO.not_RxoF (H (α := NTopO) (r := ⟨NTopO.pt 0, NTopO.pt 0⟩))

-- `Std.Roo.Internal.toArray_eq_toArray_iter` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v64 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roo.Internal.toArray_eq_toArray_iter 5 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt, M0.pt⟩))

-- `Std.Roo.Internal.toList_eq_toList_iter` (hypothesis 4, inst : Std.Rxo.IsAlwaysFinite α): necessary; NTopO (Nat with < always true; LUE holds) is not Rxo-finite.
theorem v65 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roo.Internal.toList_eq_toList_iter 4 :=
  fun H => NTopO.not_RxoF (H (α := NTopO) (r := ⟨NTopO.pt 0, NTopO.pt 0⟩))

-- `Std.Roo.Internal.toList_eq_toList_iter` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable.
theorem v66 : ¬ indep0% _private.Init.Data.Range.Polymorphic.Lemmas.«0».Std.Roo.Internal.toList_eq_toList_iter 5 :=
  fun H => M0.not_LUE (H (α := M0) (r := ⟨M0.pt, M0.pt⟩))

-- `Std.Rxc.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 4, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable; loop arguments: n = Option, Pl = False (rel empty, rxcWfF), f = none.
theorem v67 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loopWf_eq 4 :=
  fun H => M0.not_LUE (H (α := M0) (n := Option) (γ := Unit) (lift := liftId) (instLawfulMonadLiftFunction := liftIdLawful) (Pl := fun _ _ _ => False) (wf := rxcWfF) (LargeEnough := fun _ => True) (hl := fun _ _ _ _ => trivial) (upperBound := M0.pt) (acc := ()) (next := M0.pt) (h := trivial) (f := fun _ _ _ _ => none))

-- `Std.Rxc.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerableLE α): necessary; NLE (Nat with a ≤ b + 1; LUE/LLT/LLeast/RxcF/RxoF hold) violates LawfulUpwardEnumerableLE; loop arguments: n = Option, Pl = False (rel empty, rxcWfF), f = none.
theorem v68 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loopWf_eq 5 :=
  fun H => NLE.not_LLE (H (α := NLE) (n := Option) (γ := Unit) (lift := liftId) (instLawfulMonadLiftFunction := liftIdLawful) (Pl := fun _ _ _ => False) (wf := rxcWfF) (LargeEnough := fun _ => True) (hl := fun _ _ _ _ => trivial) (upperBound := NLE.pt 0) (acc := ()) (next := NLE.pt 0) (h := trivial) (f := fun _ _ _ _ => none))

-- `Std.Rxc.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 13, wf : Std.IteratorLoop.WellFounded (Std.Rxc.Iterator α) Id Pl): removable; derivable: LawfulUpwardEnumerable + LawfulUpwardEnumerableLE give Rxc.IsAlwaysFinite (rxc_of_lawful), hence Finite, hence IteratorLoop.WellFounded for every Pl (wellFounded_of_finite).
theorem v69 : indep% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loopWf_eq 13 :=
  by intro α; intros; haveI := rxc_of_lawful (α := α); exact IteratorLoop.wellFounded_of_finite

-- `Std.Rxc.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 15, hl : ∀ (a b : α), a ≤ b → LargeEnough a → LargeEnough b): necessary; Nat, LargeEnough = (· = 0), next = 0: LargeEnough is not upward closed (0 ≤ 1); Pl = False, f = none.
theorem v70 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loopWf_eq 15 :=
  fun H => absurd (H (α := Nat) (n := Option) (γ := Unit) (lift := liftId) (instLawfulMonadLiftFunction := liftIdLawful) (Pl := fun _ _ _ => False) (wf := rxcWfF) (LargeEnough := fun x => x = 0) (upperBound := (0 : Nat)) (acc := ()) (next := (0 : Nat)) (h := rfl) (f := fun _ _ _ _ => none) 0 1 (Nat.zero_le 1) rfl) (by decide)

-- `Std.Rxc.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 19, h : LargeEnough next): necessary; LargeEnough = False (upward closed), so LargeEnough next fails; Nat, Pl = False, f = none.
theorem v71 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loopWf_eq 19 :=
  fun H => H (α := Nat) (n := Option) (γ := Unit) (lift := liftId) (instLawfulMonadLiftFunction := liftIdLawful) (Pl := fun _ _ _ => False) (wf := rxcWfF) (LargeEnough := fun _ => False) (hl := fun _ _ _ h => h) (upperBound := (0 : Nat)) (acc := ()) (next := (0 : Nat)) (f := fun _ _ _ _ => none)

-- `Std.Rxc.Iterator.instIteratorLoop.loop_eq_wf` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable; loop arguments: n = Option, Pl = False (rel empty, rxcWfF), f = none.
theorem v72 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loop_eq_wf 5 :=
  fun H => M0.not_LUE (H (α := M0) (n := Option) (γ := Unit) (Pl := fun _ _ _ => False) (wf := rxcWfF) (LargeEnough := fun _ => True) (hl := fun _ _ _ _ => trivial) (upperBound := M0.pt) (acc := ()) (next := M0.pt) (hn := trivial) (f := fun _ _ _ _ => none))

-- `Std.Rxc.Iterator.instIteratorLoop.loop_eq_wf` (hypothesis 6, inst : Std.PRange.LawfulUpwardEnumerableLE α): necessary; NLE (Nat with a ≤ b + 1; LUE/LLT/LLeast/RxcF/RxoF hold) violates LawfulUpwardEnumerableLE; loop arguments: n = Option, Pl = False (rel empty, rxcWfF), f = none.
theorem v73 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loop_eq_wf 6 :=
  fun H => NLE.not_LLE (H (α := NLE) (n := Option) (γ := Unit) (Pl := fun _ _ _ => False) (wf := rxcWfF) (LargeEnough := fun _ => True) (hl := fun _ _ _ _ => trivial) (upperBound := NLE.pt 0) (acc := ()) (next := NLE.pt 0) (hn := trivial) (f := fun _ _ _ _ => none))

-- `Std.Rxc.Iterator.instIteratorLoop.loop_eq_wf` (hypothesis 11, hl : ∀ (a b : α), a ≤ b → LargeEnough a → LargeEnough b): necessary; Nat, LargeEnough = (· = 0), next = 0: LargeEnough is not upward closed (0 ≤ 1); Pl = False, f = none.
theorem v74 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loop_eq_wf 11 :=
  fun H => absurd (H (α := Nat) (n := Option) (γ := Unit) (Pl := fun _ _ _ => False) (wf := rxcWfF) (LargeEnough := fun x => x = 0) (upperBound := (0 : Nat)) (acc := ()) (next := (0 : Nat)) (hn := rfl) (f := fun _ _ _ _ => none) 0 1 (Nat.zero_le 1) rfl) (by decide)

-- `Std.Rxc.Iterator.instIteratorLoop.loop_eq_wf` (hypothesis 14, hn : LargeEnough next): necessary; LargeEnough = False (upward closed), so LargeEnough next fails; Nat, Pl = False, f = none.
theorem v75 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loop_eq_wf 14 :=
  fun H => H (α := Nat) (n := Option) (γ := Unit) (Pl := fun _ _ _ => False) (wf := rxcWfF) (LargeEnough := fun _ => False) (hl := fun _ _ _ h => h) (upperBound := (0 : Nat)) (acc := ()) (next := (0 : Nat)) (f := fun _ _ _ _ => none)

-- `Std.Rxc.Iterator.instIteratorLoop.loop_eq_wf` (hypothesis 17, wf : Std.IteratorLoop.WellFounded (Std.Rxc.Iterator α) Id Pl): removable; derivable: LawfulUpwardEnumerable + LawfulUpwardEnumerableLE give Rxc.IsAlwaysFinite (rxc_of_lawful), hence Finite, hence IteratorLoop.WellFounded for every Pl (wellFounded_of_finite).
theorem v76 : indep% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loop_eq_wf 17 :=
  by intro α; intros; haveI := rxc_of_lawful (α := α); exact IteratorLoop.wellFounded_of_finite

-- `Std.Rxc.List.length_filter_strict_mono` (hypothesis 5, h : ∀ (a : α), P a = true → Q a = true): necessary; l = [0, 1], P = (· == 1), Q = (· == 0), a = 0: P does not imply Q, both filters have length 1.
theorem v77 : ¬ drop0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.List.length_filter_strict_mono 5 :=
  fun H => absurd (H (α := Nat) (l := [0, 1]) (P := fun x => x == 1) (Q := fun x => x == 0) (a := 0) (by decide) (by decide) (by decide)) (by decide)

-- `Std.Rxi.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 2, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable; loop arguments: n = Option, Pl = False (rel empty, rxiWfF), f = none.
theorem v78 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxi.Iterator.instIteratorLoop.loopWf_eq 2 :=
  fun H => M0.not_LUE (H (α := M0) (n := Option) (γ := Unit) (lift := liftId) (instLawfulMonadLiftFunction := liftIdLawful) (Pl := fun _ _ _ => False) (wf := rxiWfF) (LargeEnough := fun _ => True) (hl := fun _ _ _ _ => trivial) (acc := ()) (next := M0.pt) (h := trivial) (f := fun _ _ _ => none))

-- `Std.Rxi.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 10, wf : Std.IteratorLoop.WellFounded (Std.Rxi.Iterator α) Id Pl): necessary; Nat with Pl = True: the Rxi iterator yields 0, 1, 2, … forever, so IteratorLoop.rel is not well-founded (nat_rxi_not_wf).
theorem v79 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxi.Iterator.instIteratorLoop.loopWf_eq 10 :=
  fun H => nat_rxi_not_wf (H (α := Nat) (n := Option) (γ := Unit) (lift := liftId) (instLawfulMonadLiftFunction := liftIdLawful) (Pl := fun _ _ _ => True) (LargeEnough := fun _ => True) (hl := fun _ _ _ _ => trivial) (acc := ()) (next := (0 : Nat)) (h := trivial) (f := fun _ _ c => some ⟨.done c, trivial⟩))

-- `Std.Rxi.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 12, hl : ∀ (a b : α), Std.PRange.UpwardEnumerable.LE a b → LargeEnough a → LargeEnough b): necessary; Nat, LargeEnough = (· = 0), next = 0: LargeEnough is not upward closed (0 ≤ 1); Pl = False, f = none.
theorem v80 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxi.Iterator.instIteratorLoop.loopWf_eq 12 :=
  fun H => absurd (H (α := Nat) (n := Option) (γ := Unit) (lift := liftId) (instLawfulMonadLiftFunction := liftIdLawful) (Pl := fun _ _ _ => False) (wf := rxiWfF) (LargeEnough := fun x => x = 0) (acc := ()) (next := (0 : Nat)) (h := rfl) (f := fun _ _ _ => none) 0 1 ⟨1, rfl⟩ rfl) (by decide)

-- `Std.Rxi.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 15, h : LargeEnough next): necessary; LargeEnough = False (upward closed), so LargeEnough next fails; Nat, Pl = False, f = none.
theorem v81 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxi.Iterator.instIteratorLoop.loopWf_eq 15 :=
  fun H => H (α := Nat) (n := Option) (γ := Unit) (lift := liftId) (instLawfulMonadLiftFunction := liftIdLawful) (Pl := fun _ _ _ => False) (wf := rxiWfF) (LargeEnough := fun _ => False) (hl := fun _ _ _ h => h) (acc := ()) (next := (0 : Nat)) (f := fun _ _ _ => none)

-- `Std.Rxi.Iterator.instIteratorLoop.loop_eq_wf` (hypothesis 3, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable; loop arguments: n = Option, Pl = False (rel empty, rxiWfF), f = none.
theorem v82 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxi.Iterator.instIteratorLoop.loop_eq_wf 3 :=
  fun H => M0.not_LUE (H (α := M0) (n := Option) (γ := Unit) (Pl := fun _ _ _ => False) (wf := rxiWfF) (LargeEnough := fun _ => True) (hl := fun _ _ _ _ => trivial) (acc := ()) (next := M0.pt) (hn := trivial) (f := fun _ _ _ => none))

-- `Std.Rxi.Iterator.instIteratorLoop.loop_eq_wf` (hypothesis 8, hl : ∀ (a b : α), Std.PRange.UpwardEnumerable.LE a b → LargeEnough a → LargeEnough b): necessary; Nat, LargeEnough = (· = 0), next = 0: LargeEnough is not upward closed (0 ≤ 1); Pl = False, f = none.
theorem v83 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxi.Iterator.instIteratorLoop.loop_eq_wf 8 :=
  fun H => absurd (H (α := Nat) (n := Option) (γ := Unit) (Pl := fun _ _ _ => False) (wf := rxiWfF) (LargeEnough := fun x => x = 0) (acc := ()) (next := (0 : Nat)) (hn := rfl) (f := fun _ _ _ => none) 0 1 ⟨1, rfl⟩ rfl) (by decide)

-- `Std.Rxi.Iterator.instIteratorLoop.loop_eq_wf` (hypothesis 10, hn : LargeEnough next): necessary; LargeEnough = False (upward closed), so LargeEnough next fails; Nat, Pl = False, f = none.
theorem v84 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxi.Iterator.instIteratorLoop.loop_eq_wf 10 :=
  fun H => H (α := Nat) (n := Option) (γ := Unit) (Pl := fun _ _ _ => False) (wf := rxiWfF) (LargeEnough := fun _ => False) (hl := fun _ _ _ h => h) (acc := ()) (next := (0 : Nat)) (f := fun _ _ _ => none)

-- `Std.Rxi.Iterator.instIteratorLoop.loop_eq_wf` (hypothesis 13, wf : Std.IteratorLoop.WellFounded (Std.Rxi.Iterator α) Id Pl): necessary; Nat with Pl = True: the Rxi iterator yields 0, 1, 2, … forever, so IteratorLoop.rel is not well-founded (nat_rxi_not_wf).
theorem v85 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxi.Iterator.instIteratorLoop.loop_eq_wf 13 :=
  fun H => nat_rxi_not_wf (H (α := Nat) (n := Option) (γ := Unit) (Pl := fun _ _ _ => True) (LargeEnough := fun _ => True) (hl := fun _ _ _ _ => trivial) (acc := ()) (next := (0 : Nat)) (hn := trivial) (f := fun _ _ c => some ⟨.done c, trivial⟩))

-- `Std.Rxo.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 4, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable; loop arguments: n = Option, Pl = False (rel empty, rxoWfF), f = none.
theorem v86 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loopWf_eq 4 :=
  fun H => M0.not_LUE (H (α := M0) (n := Option) (γ := Unit) (lift := liftId) (instLawfulMonadLiftFunction := liftIdLawful) (Pl := fun _ _ _ => False) (wf := rxoWfF) (LargeEnough := fun _ => True) (hl := fun _ _ _ _ => trivial) (upperBound := M0.pt) (acc := ()) (next := M0.pt) (h := trivial) (f := fun _ _ _ _ => none))

-- `Std.Rxo.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerableLT α): necessary; NLT (Nat with a < b + 1; LUE/LLE/LLeast/RxcF/RxoF hold) violates LawfulUpwardEnumerableLT; loop arguments: n = Option, Pl = False (rel empty, rxoWfF), f = none.
theorem v87 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loopWf_eq 5 :=
  fun H => NLT.not_LLT (H (α := NLT) (n := Option) (γ := Unit) (lift := liftId) (instLawfulMonadLiftFunction := liftIdLawful) (Pl := fun _ _ _ => False) (wf := rxoWfF) (LargeEnough := fun _ => True) (hl := fun _ _ _ _ => trivial) (upperBound := NLT.pt 0) (acc := ()) (next := NLT.pt 0) (h := trivial) (f := fun _ _ _ _ => none))

-- `Std.Rxo.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 13, wf : Std.IteratorLoop.WellFounded (Std.Rxo.Iterator α) Id Pl): removable; derivable: LawfulUpwardEnumerable + LawfulUpwardEnumerableLT give Rxo.IsAlwaysFinite (rxo_of_lawful), hence Finite, hence IteratorLoop.WellFounded for every Pl (wellFounded_of_finite).
theorem v88 : indep% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loopWf_eq 13 :=
  by intro α; intros; haveI := rxo_of_lawful (α := α); exact IteratorLoop.wellFounded_of_finite

-- `Std.Rxo.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 15, hl : ∀ (a b : α), Std.PRange.UpwardEnumerable.LE a b → LargeEnough a → LargeEnough b): necessary; Nat, LargeEnough = (· = 0), next = 0: LargeEnough is not upward closed (0 ≤ 1); Pl = False, f = none.
theorem v89 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loopWf_eq 15 :=
  fun H => absurd (H (α := Nat) (n := Option) (γ := Unit) (lift := liftId) (instLawfulMonadLiftFunction := liftIdLawful) (Pl := fun _ _ _ => False) (wf := rxoWfF) (LargeEnough := fun x => x = 0) (upperBound := (0 : Nat)) (acc := ()) (next := (0 : Nat)) (h := rfl) (f := fun _ _ _ _ => none) 0 1 ⟨1, rfl⟩ rfl) (by decide)

-- `Std.Rxo.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 19, h : LargeEnough next): necessary; LargeEnough = False (upward closed), so LargeEnough next fails; Nat, Pl = False, f = none.
theorem v90 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loopWf_eq 19 :=
  fun H => H (α := Nat) (n := Option) (γ := Unit) (lift := liftId) (instLawfulMonadLiftFunction := liftIdLawful) (Pl := fun _ _ _ => False) (wf := rxoWfF) (LargeEnough := fun _ => False) (hl := fun _ _ _ h => h) (upperBound := (0 : Nat)) (acc := ()) (next := (0 : Nat)) (f := fun _ _ _ _ => none)

-- `Std.Rxo.Iterator.instIteratorLoop.loop_eq_wf` (hypothesis 5, inst : Std.PRange.LawfulUpwardEnumerable α): necessary; M0 (one point, succMany? 0 a = none; LE/LT empty, LLE/LLT/RxcF/RxoF hold) violates LawfulUpwardEnumerable; loop arguments: n = Option, Pl = False (rel empty, rxoWfF), f = none.
theorem v91 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loop_eq_wf 5 :=
  fun H => M0.not_LUE (H (α := M0) (n := Option) (γ := Unit) (Pl := fun _ _ _ => False) (wf := rxoWfF) (LargeEnough := fun _ => True) (hl := fun _ _ _ _ => trivial) (upperBound := M0.pt) (acc := ()) (next := M0.pt) (hn := trivial) (f := fun _ _ _ _ => none))

-- `Std.Rxo.Iterator.instIteratorLoop.loop_eq_wf` (hypothesis 6, inst : Std.PRange.LawfulUpwardEnumerableLT α): necessary; NLT (Nat with a < b + 1; LUE/LLE/LLeast/RxcF/RxoF hold) violates LawfulUpwardEnumerableLT; loop arguments: n = Option, Pl = False (rel empty, rxoWfF), f = none.
theorem v92 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loop_eq_wf 6 :=
  fun H => NLT.not_LLT (H (α := NLT) (n := Option) (γ := Unit) (Pl := fun _ _ _ => False) (wf := rxoWfF) (LargeEnough := fun _ => True) (hl := fun _ _ _ _ => trivial) (upperBound := NLT.pt 0) (acc := ()) (next := NLT.pt 0) (hn := trivial) (f := fun _ _ _ _ => none))

-- `Std.Rxo.Iterator.instIteratorLoop.loop_eq_wf` (hypothesis 11, hl : ∀ (a b : α), Std.PRange.UpwardEnumerable.LE a b → LargeEnough a → LargeEnough b): necessary; Nat, LargeEnough = (· = 0), next = 0: LargeEnough is not upward closed (0 ≤ 1); Pl = False, f = none.
theorem v93 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loop_eq_wf 11 :=
  fun H => absurd (H (α := Nat) (n := Option) (γ := Unit) (Pl := fun _ _ _ => False) (wf := rxoWfF) (LargeEnough := fun x => x = 0) (upperBound := (0 : Nat)) (acc := ()) (next := (0 : Nat)) (hn := rfl) (f := fun _ _ _ _ => none) 0 1 ⟨1, rfl⟩ rfl) (by decide)

-- `Std.Rxo.Iterator.instIteratorLoop.loop_eq_wf` (hypothesis 14, hn : LargeEnough next): necessary; LargeEnough = False (upward closed), so LargeEnough next fails; Nat, Pl = False, f = none.
theorem v94 : ¬ indep0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loop_eq_wf 14 :=
  fun H => H (α := Nat) (n := Option) (γ := Unit) (Pl := fun _ _ _ => False) (wf := rxoWfF) (LargeEnough := fun _ => False) (hl := fun _ _ _ h => h) (upperBound := (0 : Nat)) (acc := ()) (next := (0 : Nat)) (f := fun _ _ _ _ => none)

-- `Std.Rxo.Iterator.instIteratorLoop.loop_eq_wf` (hypothesis 17, wf : Std.IteratorLoop.WellFounded (Std.Rxo.Iterator α) Id Pl): removable; derivable: LawfulUpwardEnumerable + LawfulUpwardEnumerableLT give Rxo.IsAlwaysFinite (rxo_of_lawful), hence Finite, hence IteratorLoop.WellFounded for every Pl (wellFounded_of_finite).
theorem v95 : indep% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loop_eq_wf 17 :=
  by intro α; intros; haveI := rxo_of_lawful (α := α); exact IteratorLoop.wellFounded_of_finite

-- `Std.Rxo.List.length_filter_strict_mono` (hypothesis 5, h : ∀ (a : α), P a = true → Q a = true): necessary; l = [0, 1], P = (· == 1), Q = (· == 0), a = 0: P does not imply Q, both filters have length 1.
theorem v96 : ¬ drop0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.List.length_filter_strict_mono 5 :=
  fun H => absurd (H (α := Nat) (l := [0, 1]) (P := fun x => x == 1) (Q := fun x => x == 0) (a := 0) (by decide) (by decide) (by decide)) (by decide)

-- `Std.Rxc.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 8, inst : LawfulMonad n): removable; removable: loop.wf and IterM.DefaultConsumers.forIn' unfold to the same bind (f x ...) (match ...) at every step; proved by well-founded induction on IteratorLoop.rel (wf), using only the eq_1 equation of loop.wf, extrinsicFix₃_eq_apply and liftBind_pure, no monad laws.
theorem rmc : drop% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loopWf_eq 8 := by
  intro α _ _ _ _ _ n _ γ lift hlift Pl wf LE' hl ub acc next h f
  have none_case : ∀ (P : α → Prop) (g : (b : α) → P b → (c : γ) → n (Subtype (Pl b c)))
      (it : IterM (α := Rxc.Iterator α) Id α) (acc : γ)
      (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b), it.internalState.next = none →
      IterM.DefaultConsumers.forIn' lift γ Pl it acc P hP g = pure acc := by
    intro P g it acc hP hn
    haveI : Nonempty γ := ⟨acc⟩
    rcases it with ⟨⟨nx, ub⟩⟩
    cases hn
    rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
    rw [IterM.step_mk, Rxc.Iterator.Monadic.step_eq_step]
    dsimp only
    rw [hlift.liftBind_pure, Shrink.inflate_deflate]
    simp only [Rxc.Iterator.Monadic.step]
  have key : ∀ (P : α → Prop) (g : (b : α) → P b → (c : γ) → n (Subtype (Pl b c)))
      (hFg : ∀ a h1 h2 c (p : P a), f a h1 h2 c = g a p c)
      (q : IterM (α := Rxc.Iterator α) Id α × γ) (x : α)
      (hq : q.1 = (⟨⟨some x, ub⟩⟩ : IterM (α := Rxc.Iterator α) Id α)) (h : LE' x)
      (hP : ∀ b, q.1.IsPlausibleIndirectOutput b → P b),
      (priv% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loop.wf)
          γ Pl wf LE' hl ub q.2 x h f =
        IterM.DefaultConsumers.forIn' lift γ Pl q.1 q.2 P hP g := by
    intro P g hFg q
    induction q using WellFounded.induction wf with
    | _ q ih => ?_
    intro x hq h hP
    rcases q with ⟨it1, acc⟩
    dsimp only at hq hP ih ⊢
    subst hq
    haveI : Nonempty γ := ⟨acc⟩
    rw [priv% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loop.wf.eq_1]
    rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
    rw [IterM.step_mk, Rxc.Iterator.Monadic.step_eq_step]
    dsimp only
    rw [hlift.liftBind_pure, Shrink.inflate_deflate]
    by_cases hu : x ≤ ub
    · rw [dif_pos hu]
      simp only [Rxc.Iterator.Monadic.step, if_pos hu]
      congr 1
      · apply hFg
      · funext r
        rcases r with ⟨r, hr⟩
        cases r with
        | done c => rfl
        | yield c =>
          dsimp only
          split
          · next next' hs =>
            refine ih (⟨⟨succ? x, ub⟩⟩, c) ?_ next' (by simp [hs]) _ _
            refine Or.inl ⟨x, ?_, hr⟩
            simp [Rxc.Iterator.Monadic.isPlausibleStep_iff, Rxc.Iterator.Monadic.step, hu]
          · next hs =>
            exact (none_case P g ⟨⟨succ? x, ub⟩⟩ c _ hs).symm
    · rw [dif_neg hu]
      simp only [Rxc.Iterator.Monadic.step, if_neg hu]
  rw [priv% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loop.wf.eq_1]
  by_cases hu : next ≤ ub
  · rw [dif_pos hu, dif_pos hu]
    congr 1
    funext r
    rcases r with ⟨r, hr⟩
    cases r with
    | done c => rfl
    | yield c =>
      dsimp only
      split
      · next next' hs =>
        exact key _ _ (fun _ _ _ _ _ => rfl) (⟨⟨succ? next, ub⟩⟩, c) next' (by simp [hs]) _ _
      · next hs =>
        exact (none_case _ _ ⟨⟨succ? next, ub⟩⟩ c _ hs).symm
  · rw [dif_neg hu, dif_neg hu]

-- `Std.Rxo.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 8, inst : LawfulMonad n): removable; removable: loop.wf and IterM.DefaultConsumers.forIn' unfold to the same bind (f x ...) (match ...) at every step; proved by well-founded induction on IteratorLoop.rel (wf), using only the eq_1 equation of loop.wf, extrinsicFix₃_eq_apply and liftBind_pure, no monad laws.
theorem rmo : drop% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loopWf_eq 8 := by
  intro α _ _ _ _ _ n _ γ lift hlift Pl wf LE' hl ub acc next h f
  have none_case : ∀ (P : α → Prop) (g : (b : α) → P b → (c : γ) → n (Subtype (Pl b c)))
      (it : IterM (α := Rxo.Iterator α) Id α) (acc : γ)
      (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b), it.internalState.next = none →
      IterM.DefaultConsumers.forIn' lift γ Pl it acc P hP g = pure acc := by
    intro P g it acc hP hn
    haveI : Nonempty γ := ⟨acc⟩
    rcases it with ⟨⟨nx, ub⟩⟩
    cases hn
    rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
    rw [IterM.step_mk, Rxo.Iterator.Monadic.step_eq_step]
    dsimp only
    rw [hlift.liftBind_pure, Shrink.inflate_deflate]
    simp only [Rxo.Iterator.Monadic.step]
  have key : ∀ (P : α → Prop) (g : (b : α) → P b → (c : γ) → n (Subtype (Pl b c)))
      (hFg : ∀ a h1 h2 c (p : P a), f a h1 h2 c = g a p c)
      (q : IterM (α := Rxo.Iterator α) Id α × γ) (x : α)
      (hq : q.1 = (⟨⟨some x, ub⟩⟩ : IterM (α := Rxo.Iterator α) Id α)) (h : LE' x)
      (hP : ∀ b, q.1.IsPlausibleIndirectOutput b → P b),
      (priv% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loop.wf)
          γ Pl wf LE' hl ub q.2 x h f =
        IterM.DefaultConsumers.forIn' lift γ Pl q.1 q.2 P hP g := by
    intro P g hFg q
    induction q using WellFounded.induction wf with
    | _ q ih => ?_
    intro x hq h hP
    rcases q with ⟨it1, acc⟩
    dsimp only at hq hP ih ⊢
    subst hq
    haveI : Nonempty γ := ⟨acc⟩
    rw [priv% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loop.wf.eq_1]
    rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
    rw [IterM.step_mk, Rxo.Iterator.Monadic.step_eq_step]
    dsimp only
    rw [hlift.liftBind_pure, Shrink.inflate_deflate]
    by_cases hu : x < ub
    · rw [dif_pos hu]
      simp only [Rxo.Iterator.Monadic.step, if_pos hu]
      congr 1
      · apply hFg
      · funext r
        rcases r with ⟨r, hr⟩
        cases r with
        | done c => rfl
        | yield c =>
          dsimp only
          split
          · next next' hs =>
            refine ih (⟨⟨succ? x, ub⟩⟩, c) ?_ next' (by simp [hs]) _ _
            refine Or.inl ⟨x, ?_, hr⟩
            simp [Rxo.Iterator.Monadic.isPlausibleStep_iff, Rxo.Iterator.Monadic.step, hu]
          · next hs =>
            exact (none_case P g ⟨⟨succ? x, ub⟩⟩ c _ hs).symm
    · rw [dif_neg hu]
      simp only [Rxo.Iterator.Monadic.step, if_neg hu]
  rw [priv% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loop.wf.eq_1]
  by_cases hu : next < ub
  · rw [dif_pos hu, dif_pos hu]
    congr 1
    funext r
    rcases r with ⟨r, hr⟩
    cases r with
    | done c => rfl
    | yield c =>
      dsimp only
      split
      · next next' hs =>
        exact key _ _ (fun _ _ _ _ _ => rfl) (⟨⟨succ? next, ub⟩⟩, c) next' (by simp [hs]) _ _
      · next hs =>
        exact (none_case _ _ ⟨⟨succ? next, ub⟩⟩ c _ hs).symm
  · rw [dif_neg hu, dif_neg hu]

-- `Std.Rxi.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 5, inst : LawfulMonad n): removable; removable: loop.wf and IterM.DefaultConsumers.forIn' unfold to the same bind (f x ...) (match ...) at every step; proved by well-founded induction on IteratorLoop.rel (wf), using only the eq_1 equation of loop.wf, extrinsicFix₃_eq_apply and liftBind_pure, no monad laws.
theorem rmi : drop% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxi.Iterator.instIteratorLoop.loopWf_eq 5 := by
  intro α _ _ n _ γ lift hlift Pl wf LE' hl acc next h f
  have none_case : ∀ (P : α → Prop) (g : (b : α) → P b → (c : γ) → n (Subtype (Pl b c)))
      (it : IterM (α := Rxi.Iterator α) Id α) (acc : γ)
      (hP : ∀ b, it.IsPlausibleIndirectOutput b → P b), it.internalState.next = none →
      IterM.DefaultConsumers.forIn' lift γ Pl it acc P hP g = pure acc := by
    intro P g it acc hP hn
    haveI : Nonempty γ := ⟨acc⟩
    rcases it with ⟨⟨nx⟩⟩
    cases hn
    rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
    rw [Rxi.Iterator.Monadic.step_eq_step]
    dsimp only
    rw [hlift.liftBind_pure, Shrink.inflate_deflate]
    simp only [Rxi.Iterator.Monadic.step]
  have key : ∀ (P : α → Prop) (g : (b : α) → P b → (c : γ) → n (Subtype (Pl b c)))
      (hFg : ∀ a h1 c (p : P a), f a h1 c = g a p c)
      (q : IterM (α := Rxi.Iterator α) Id α × γ) (x : α)
      (hq : q.1 = (⟨⟨some x⟩⟩ : IterM (α := Rxi.Iterator α) Id α)) (h : LE' x)
      (hP : ∀ b, q.1.IsPlausibleIndirectOutput b → P b),
      (priv% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxi.Iterator.instIteratorLoop.loop.wf)
          γ Pl wf LE' hl q.2 x h f =
        IterM.DefaultConsumers.forIn' lift γ Pl q.1 q.2 P hP g := by
    intro P g hFg q
    induction q using WellFounded.induction wf with
    | _ q ih => ?_
    intro x hq h hP
    rcases q with ⟨it1, acc⟩
    dsimp only at hq hP ih ⊢
    subst hq
    haveI : Nonempty γ := ⟨acc⟩
    rw [priv% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxi.Iterator.instIteratorLoop.loop.wf.eq_1]
    rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
    rw [Rxi.Iterator.Monadic.step_eq_step]
    dsimp only
    rw [hlift.liftBind_pure, Shrink.inflate_deflate]
    simp only [Rxi.Iterator.Monadic.step]
    congr 1
    · apply hFg
    · funext r
      rcases r with ⟨r, hr⟩
      cases r with
      | done c => rfl
      | yield c =>
        dsimp only
        split
        · next next' hs =>
          refine ih (⟨⟨succ? x⟩⟩, c) ?_ next' (by simp [hs]) _ _
          refine Or.inl ⟨x, ?_, hr⟩
          simp [Rxi.Iterator.Monadic.isPlausibleStep_iff, Rxi.Iterator.Monadic.step]
        · next hs =>
          exact (none_case P g ⟨⟨succ? x⟩⟩ c _ hs).symm
  rw [priv% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxi.Iterator.instIteratorLoop.loop.wf.eq_1]
  congr 1
  funext r
  rcases r with ⟨r, hr⟩
  cases r with
  | done c => rfl
  | yield c =>
    dsimp only
    split
    · next next' hs =>
      refine key _ _ ?_ (⟨⟨succ? next⟩⟩, c) next' (by simp [hs]) _ _
      intros; rfl
    · next hs =>
      exact (none_case _ _ ⟨⟨succ? next⟩⟩ c _ hs).symm

-- `Std.Rxc.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 11, instLawfulMonadLiftFunction : Std.Internal.LawfulMonadLiftBindFunction lift): necessary; U0 (one point, succ? = none, all laws), n = Option, lift = fun _ _ _ _ => none (liftBind_pure fails), Pl = True, f yields: LHS = some (), RHS = none.
theorem lc : ¬ drop0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loopWf_eq 11 := fun H => by
  have e := H (α := U0) (n := Option) (γ := Unit) (lift := liftNone) (Pl := fun _ _ _ => True)
    (wf := IteratorLoop.wellFounded_of_finite) (LargeEnough := fun _ => True) (hl := fun _ _ _ _ => trivial)
    (upperBound := .pt) (acc := ()) (next := .pt) (h := trivial) (f := fun _ _ _ c => some ⟨.yield c, trivial⟩)
  rw [priv% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxc.Iterator.instIteratorLoop.loop.wf.eq_1] at e
  haveI : Nonempty Unit := ⟨()⟩
  simp only [dif_pos (show U0.pt ≤ U0.pt from trivial)] at e
  simp only [Option.bind_eq_bind, Option.bind_some] at e
  rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ IteratorLoop.wellFounded_of_finite)] at e
  simp [liftNone] at e

-- `Std.Rxo.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 11, instLawfulMonadLiftFunction : Std.Internal.LawfulMonadLiftBindFunction lift): necessary; Nat, next = 0, upperBound = 1, n = Option, lift = fun _ _ _ _ => none (liftBind_pure fails), Pl = True, f yields: LHS = some () (loop.wf stops at 1), RHS = none.
theorem lo : ¬ drop0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loopWf_eq 11 := fun H => by
  have e := H (α := Nat) (n := Option) (γ := Unit) (lift := liftNone) (Pl := fun _ _ _ => True)
    (wf := IteratorLoop.wellFounded_of_finite) (LargeEnough := fun _ => True) (hl := fun _ _ _ _ => trivial)
    (upperBound := 1) (acc := ()) (next := 0) (h := trivial) (f := fun _ _ _ c => some ⟨.yield c, trivial⟩)
  rw [priv% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loop.wf.eq_1] at e
  haveI : Nonempty Unit := ⟨()⟩
  simp only [dif_pos (show (0 : Nat) < 1 by decide)] at e
  simp only [Option.bind_eq_bind, Option.bind_some] at e
  split at e
  · next next' hs =>
    obtain rfl : 1 = next' := Option.some.inj hs
    rw [priv% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxo.Iterator.instIteratorLoop.loop.wf.eq_1] at e
    simp only [dif_neg (show ¬ (1 : Nat) < 1 by decide)] at e
    rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ IteratorLoop.wellFounded_of_finite)] at e
    simp [liftNone] at e
  · next hs => exact absurd hs (by decide)

-- `Std.Rxi.Iterator.instIteratorLoop.loopWf_eq` (hypothesis 8, instLawfulMonadLiftFunction : Std.Internal.LawfulMonadLiftBindFunction lift): necessary; U0 (one point, succ? = none, all laws, Rxi-finite), n = Option, lift = fun _ _ _ _ => none (liftBind_pure fails), Pl = True, f yields: LHS = some (), RHS = none.
theorem li : ¬ drop0% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxi.Iterator.instIteratorLoop.loopWf_eq 8 := fun H => by
  have e := H (α := U0) (n := Option) (γ := Unit) (lift := liftNone) (Pl := fun _ _ _ => True)
    (wf := IteratorLoop.wellFounded_of_finite) (LargeEnough := fun _ => True) (hl := fun _ _ _ _ => trivial)
    (acc := ()) (next := .pt) (h := trivial) (f := fun _ _ c => some ⟨.yield c, trivial⟩)
  rw [priv% _private.Init.Data.Range.Polymorphic.RangeIterator.«0».Std.Rxi.Iterator.instIteratorLoop.loop.wf.eq_1] at e
  haveI : Nonempty Unit := ⟨()⟩
  simp only [Option.bind_eq_bind, Option.bind_some] at e
  rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ IteratorLoop.wellFounded_of_finite)] at e
  simp [liftNone] at e




end PRangeItHand
