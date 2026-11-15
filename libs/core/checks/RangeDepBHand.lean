import Lean

/-!
Hand pass `RangeDepB` (hand8): 289 dependent hypotheses of the Range theorems for the upward-unbounded
ranges (`Std.Rci/Roi/Rii.*`), the `Std.PRange.*` lemmas of `UpwardEnumerable`/`Lemmas`, and the
`*_of_isSome_succ?` lemmas. All are dependent (`toList`/`toArray`/… take the instance, or the
statement uses the proof), so each verdict is `¬ ∀ indep, Hᵢ` (necessary, `¬ indep0% T i`) or
`∀ indep, Hᵢ` (removable, `indep% T i`).

283 necessary: each refutation instantiates `∀ indep, Hᵢ` at one model of the model table below, with
all the other independent hypotheses supplied as arguments, and applies that model's `¬` lemma.
6 removable: `Rxi.IsAlwaysFinite` follows from `LawfulUpwardEnumerable` + `Rxi.LawfulHasSize`
(`rxi_of_hasSize`).

The first part (derivations and model table, up to "Verdicts") is self-contained and meant to be
copied by the follow-up Range clusters.

Run with the lean4 repo's stage1 binary: `lean checks/RangeDepBHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false

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
/-- `indep0% T i`: like `indep% T i`, with all universes of `T` set to `0` (for `¬` verdicts). -/
elab "indep0% " T:ident i:num : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us := ci.levelParams.map fun _ => levelZero
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

namespace RangeDepBHand
open Std Std.PRange

/-!
# Model table (reusable)

| model      | LUE | Rxi | Inf | Lin | LLE | LLT | LLeast | LHS | Rxc/Rxo |
|------------|-----|-----|-----|-----|-----|-----|--------|-----|---------|
| `T2`       | ✓   | ✓   | ✗   | ✓   | ✓   | ✓   | ✓      | ✓   | ✓       |
| `T2lt`     | ✓   | ✓   | ✗   | ✓   | ✓   | ✗   | ✓      | ✓   | ✓       |
| `T2le`     | ✓   | ✓   | ✗   | ✓   | ✗   | ✓   | ✓      | ✓   | ✓       |
| `T2least`  | ✓   | ✓   | ✗   | ✓   | ✓   | ✓   | ✗      | ✓   | ✓       |
| `UBad`     | ✗   | ✓   | ✗ (no lemma) | ✓   | ✓   | ✓   | ✓      | ✓   | ✓       |
| `NoneMany` | ✗   | ✓   | ✓   | ✓   | ✓   | ✓   | –      | –   | ✓       |
| `Nat`      | ✓   | ✗   | ✓   | ✓   | ✓   | ✓   | ✓      | –   | ✓       |
| `EmptyM`   | –   | –   | –   | –   | –   | –   | ✓      | –   | –       |  (empty: violates `Nonempty`)

LUE = `LawfulUpwardEnumerable`, Rxi = `Rxi.IsAlwaysFinite`, Inf/Lin = `Infinitely/LinearlyUpwardEnumerable`,
LLE/LLT/LLeast = `LawfulUpwardEnumerableLE/LT/Least?`, LHS = `Rxi.LawfulHasSize` (with `Rxi.HasSize`).
✓ = instance in this file (or the library's, for `Nat`), ✗ = `¬` lemma (`M.not_lue`, `nat_not_rxi`,
`M.not_inf`, `M.not_lle`, `M.not_llt`, `M.not_lleast`, `EmptyM.not_nonempty`), – = not provided.
`EmptyM` violates `Nonempty α` (`EmptyM.not_nonempty`).
All models have `LE`, `LT` (+ decidability) and `Least?` except `NoneMany` (no `Least?`) and `EmptyM`
(only `UpwardEnumerable`, `Least?`). The `T2*` models also have `Rxi.HasSize`; `UBad` too.
`InfinitelyUpwardEnumerable` + `Rxi.IsAlwaysFinite` + `LawfulUpwardEnumerable` only hold on empty
types, so no nonempty model has all three (`NoneMany` drops LUE, `Nat` drops Rxi).
The `tl` tactic evaluates `toList`/`toArray` of `T2` ranges with the library's unfolding lemmas.
-/

/-!
## Derivations (generic)

Helper lemmas, no verdicts.
-/

-- Rxc finiteness from Rxi finiteness (as in runs/explore3/Deriv.lean).
theorem rxc_of_rxi {α : Type u} [UpwardEnumerable α] [LE α] [Rxi.IsAlwaysFinite α] :
    Rxc.IsAlwaysFinite α where
  finite init hi := by
    obtain ⟨n, hn⟩ := Rxi.IsAlwaysFinite.finite init; exact ⟨n, by simp [hn]⟩

-- Rxo finiteness from Rxi finiteness.
theorem rxo_of_rxi {α : Type u} [UpwardEnumerable α] [LT α] [Rxi.IsAlwaysFinite α] :
    Rxo.IsAlwaysFinite α where
  finite init hi := by
    obtain ⟨n, hn⟩ := Rxi.IsAlwaysFinite.finite init; exact ⟨n, by simp [hn]⟩

-- Rxi finiteness from a lawful size function: the size drops by one along each successor step.
theorem rxi_of_hasSize {α : Type u} [UpwardEnumerable α] [Rxi.HasSize α]
    [LawfulUpwardEnumerable α] [Rxi.LawfulHasSize α] : Rxi.IsAlwaysFinite α where
  finite init := by
    induction h : Rxi.HasSize.size init generalizing init with
    | zero => have := Rxi.size_pos (lo := init); omega
    | succ k ih =>
      cases hs : succ? init with
      | none => exact ⟨1, by rw [UpwardEnumerable.succMany?_one, hs]⟩
      | some x =>
        have := Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some init x hs
        obtain ⟨n, hn⟩ := ih x (by omega)
        exact ⟨n + 1, by
          rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs]; simpa using hn⟩


/-! ### `T2`: two elements `⟨false⟩ → ⟨true⟩`, all lawful except `InfinitelyUpwardEnumerable` -/

structure T2 where
  b : Bool
deriving DecidableEq

instance : UpwardEnumerable T2 where
  succ? a := if a.b then none else some ⟨true⟩

theorem T2.succMany?_add_two (n : Nat) (a : T2) : succMany? (n + 2) a = none := by
  induction n with
  | zero => obtain ⟨_ | _⟩ := a <;> rfl
  | succ n ih => show (succMany? (n + 2) a).bind succ? = none; rw [ih]; rfl

theorem T2.ueLE_iff' {a b : T2} : UpwardEnumerable.LE a b ↔ (a = b ∨ succ? a = some b) := by
  constructor
  · rintro ⟨_ | _ | n, h⟩
    · exact Or.inl (Option.some.inj h)
    · exact Or.inr h
    · rw [T2.succMany?_add_two] at h; cases h
  · rintro (h | h)
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, h⟩

theorem T2.ueLE_iff {a b : T2} : UpwardEnumerable.LE a b ↔ (a.b = false ∨ b.b = true) := by
  rw [T2.ueLE_iff']; obtain ⟨_ | _⟩ := a <;> obtain ⟨_ | _⟩ := b <;> decide

theorem T2.ueLT_iff' {a b : T2} : UpwardEnumerable.LT a b ↔ succ? a = some b := by
  constructor
  · rintro ⟨_ | n, h⟩
    · exact h
    · rw [T2.succMany?_add_two] at h; cases h
  · intro h; exact ⟨0, h⟩

theorem T2.ueLT_iff {a b : T2} : UpwardEnumerable.LT a b ↔ (a.b = false ∧ b.b = true) := by
  rw [T2.ueLT_iff']; obtain ⟨_ | _⟩ := a <;> obtain ⟨_ | _⟩ := b <;> decide

instance : LawfulUpwardEnumerable T2 where
  ne_of_lt a b h := by rw [T2.ueLT_iff] at h; intro e; subst e; simp_all
  succMany?_zero _ := rfl
  succMany?_add_one _ _ := rfl

instance : Rxi.IsAlwaysFinite T2 := ⟨fun a => ⟨2, T2.succMany?_add_two 0 a⟩⟩

instance : LinearlyUpwardEnumerable T2 where
  eq_of_succ?_eq a b h := by
    obtain ⟨_ | _⟩ := a <;> obtain ⟨_ | _⟩ := b <;> first | rfl | cases h

instance : Rxi.HasSize T2 := ⟨fun a => if a.b then 1 else 2⟩

instance : Rxi.LawfulHasSize T2 where
  size_eq_one_of_succ?_eq_none lo h := by obtain ⟨_ | _⟩ := lo <;> first | rfl | cases h
  size_eq_succ_of_succ?_eq_some lo lo' h := by
    obtain ⟨_ | _⟩ := lo <;> cases h <;> rfl

theorem T2.not_inf : ¬ InfinitelyUpwardEnumerable T2 := fun h => by
  have := h.isSome_succ? ⟨true⟩; cases this

instance : LE T2 := ⟨fun a b => a.b = false ∨ b.b = true⟩
instance : LT T2 := ⟨fun a b => a.b = false ∧ b.b = true⟩
instance : DecidableLE T2 := fun a b => inferInstanceAs (Decidable (a.b = false ∨ b.b = true))
instance : DecidableLT T2 := fun a b => inferInstanceAs (Decidable (a.b = false ∧ b.b = true))
instance : Least? T2 := ⟨some ⟨false⟩⟩
instance : Rxc.IsAlwaysFinite T2 := rxc_of_rxi
instance : Rxo.IsAlwaysFinite T2 := rxo_of_rxi

instance : LawfulUpwardEnumerableLE T2 := ⟨fun a b => T2.ueLE_iff.symm⟩

instance : LawfulUpwardEnumerableLT T2 := ⟨fun a b => T2.ueLT_iff.symm⟩

instance : LawfulUpwardEnumerableLeast? T2 := ⟨fun a => ⟨⟨false⟩, rfl, T2.ueLE_iff.2 (Or.inl rfl)⟩⟩

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

/-! ### `NoneMany`: `succ? n = some (n + 1)`, but `succMany? = none` (not lawful)

Satisfies `InfinitelyUpwardEnumerable`, `LinearlyUpwardEnumerable`, `Rxi.IsAlwaysFinite` (at `0`
steps), `LawfulUpwardEnumerableLE/LT` (with `≤`, `<` always false), `Rxc/Rxo.IsAlwaysFinite`;
violates `LawfulUpwardEnumerable` (`succMany? 0 a ≠ some a`). -/

structure NoneMany where
  n : Nat
deriving DecidableEq

instance : UpwardEnumerable NoneMany where
  succ? a := some ⟨a.n + 1⟩
  succMany? _ _ := none

theorem NoneMany.not_lue : ¬ LawfulUpwardEnumerable NoneMany := fun h => by
  have := h.succMany?_zero ⟨0⟩; cases this

instance : InfinitelyUpwardEnumerable NoneMany := ⟨fun _ => rfl⟩
instance : LinearlyUpwardEnumerable NoneMany where
  eq_of_succ?_eq a b h := by
    cases a; cases b; simp only [succ?, Option.some.injEq, NoneMany.mk.injEq] at h ⊢; omega
instance : Rxi.IsAlwaysFinite NoneMany := ⟨fun _ => ⟨0, rfl⟩⟩
instance : LE NoneMany := ⟨fun _ _ => False⟩
instance : LT NoneMany := ⟨fun _ _ => False⟩
instance : DecidableLE NoneMany := fun _ _ => instDecidableFalse
instance : DecidableLT NoneMany := fun _ _ => instDecidableFalse
instance : LawfulUpwardEnumerableLE NoneMany :=
  ⟨fun _ _ => ⟨False.elim, fun ⟨_, h⟩ => by cases h⟩⟩
instance : LawfulUpwardEnumerableLT NoneMany :=
  ⟨fun _ _ => ⟨False.elim, fun ⟨_, h⟩ => by cases h⟩⟩
instance : Rxc.IsAlwaysFinite NoneMany := rxc_of_rxi
instance : Rxo.IsAlwaysFinite NoneMany := rxo_of_rxi

/-! ### `EmptyM`: an empty type with `least? = none`

All lawfulness classes hold vacuously; violates `Nonempty`. -/

structure EmptyM where
  e : Empty

instance : UpwardEnumerable EmptyM := ⟨fun a => a.e.elim, fun _ a => a.e.elim⟩
instance : Least? EmptyM := ⟨none⟩
instance : LawfulUpwardEnumerableLeast? EmptyM := ⟨fun a => a.e.elim⟩
theorem EmptyM.not_nonempty : ¬ Nonempty EmptyM := fun ⟨a⟩ => a.e.elim

/-! ### `Nat`: the library's instances (lawful, infinite)

Satisfies `LawfulUpwardEnumerable`, `LawfulUpwardEnumerableLE/LT/Least?`,
`InfinitelyUpwardEnumerable`, `LinearlyUpwardEnumerable`, `Rxc/Rxo.IsAlwaysFinite`; violates
`Rxi.IsAlwaysFinite`. -/

theorem nat_not_rxi : ¬ Rxi.IsAlwaysFinite Nat := fun h => by
  obtain ⟨n, hn⟩ := h.finite 0; cases hn

/-! ### Evaluating `toList`/`toArray` of the `T2` ranges (via the library's unfolding lemmas) -/

macro "tl" : tactic => `(tactic| simp +decide [← Rci.toArray_toList, ← Roi.toArray_toList,
  ← Rii.toArray_toList, Rci.toList_eq_toList_roi, Roi.toList_eq_match, Rii.toList_eq_match_rci,
  UpwardEnumerable.succ?, Least?.least?])

/-! ## Verdicts -/

-- `Std.PRange.UpwardEnumerable.exists_of_succ_le` (hypothesis 3, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d0 : ¬ indep0% Std.PRange.UpwardEnumerable.exists_of_succ_le 3 := fun h => T2.not_inf (@h T2 _ _ ⟨false⟩ ⟨true⟩)

-- `Std.PRange.UpwardEnumerable.exists_of_succ_lt` (hypothesis 3, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d1 : ¬ indep0% Std.PRange.UpwardEnumerable.exists_of_succ_lt 3 := fun h => T2.not_inf (@h T2 _ _ ⟨false⟩ ⟨true⟩)

-- `Std.Rci.forIn'_congr` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerableLE α`): T2le (T2 with ≤ always false) satisfies the other hypotheses, ¬ false ≤ false.
theorem d2 : ¬ indep0% Std.Rci.forIn'_congr 3 := fun h => T2le.not_lle (@h T2le _ _ _ _ Id _ Nat 0 0 ⟨⟨true⟩⟩ ⟨⟨true⟩⟩ (fun _ _ b => pure (ForInStep.done b)) (fun _ _ b => pure (ForInStep.done b)) rfl rfl (fun _ _ _ => rfl))

-- `Std.Rci.forIn'_congr` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d3 : ¬ indep0% Std.Rci.forIn'_congr 4 := fun h => nat_not_rxi (@h Nat _ _ _ _ Id _ Nat 0 0 ⟨0⟩ ⟨0⟩ (fun _ _ b => pure (ForInStep.done b)) (fun _ _ b => pure (ForInStep.done b)) rfl rfl (fun _ _ _ => rfl))

-- `Std.Rci.forIn'_congr` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d4 : ¬ indep0% Std.Rci.forIn'_congr 5 := fun h => UBad.not_lue (@h UBad _ _ _ _ Id _ Nat 0 0 ⟨⟨⟩⟩ ⟨⟨⟩⟩ (fun _ _ b => pure (ForInStep.done b)) (fun _ _ b => pure (ForInStep.done b)) rfl rfl (fun _ _ _ => rfl))

-- `Std.Rci.forIn'_congr` (hypothesis 15, dependent: `r = r'`): T2, r = true...* resp. true<...*, r' = false...* resp. false<...*.
theorem d5 : ¬ indep0% Std.Rci.forIn'_congr 15 := fun h => by have := @h T2 _ _ _ _ _ Id _ Nat 0 0 ⟨⟨true⟩⟩ ⟨⟨false⟩⟩ (fun _ _ b => pure (ForInStep.done b)) (fun _ _ b => pure (ForInStep.done b)) rfl; revert this; tl

-- `Std.Roi.forIn'_congr` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d6 : ¬ indep0% Std.Roi.forIn'_congr 3 := fun h => T2lt.not_llt (@h T2lt _ _ _ _ Id _ Nat 0 0 ⟨⟨false⟩⟩ ⟨⟨false⟩⟩ (fun _ _ b => pure (ForInStep.done b)) (fun _ _ b => pure (ForInStep.done b)) rfl rfl (fun _ _ _ => rfl))

-- `Std.Roi.forIn'_congr` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d7 : ¬ indep0% Std.Roi.forIn'_congr 4 := fun h => nat_not_rxi (@h Nat _ _ _ _ Id _ Nat 0 0 ⟨0⟩ ⟨0⟩ (fun _ _ b => pure (ForInStep.done b)) (fun _ _ b => pure (ForInStep.done b)) rfl rfl (fun _ _ _ => rfl))

-- `Std.Roi.forIn'_congr` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d8 : ¬ indep0% Std.Roi.forIn'_congr 5 := fun h => UBad.not_lue (@h UBad _ _ _ _ Id _ Nat 0 0 ⟨⟨⟩⟩ ⟨⟨⟩⟩ (fun _ _ b => pure (ForInStep.done b)) (fun _ _ b => pure (ForInStep.done b)) rfl rfl (fun _ _ _ => rfl))

-- `Std.Roi.forIn'_congr` (hypothesis 15, dependent: `r = r'`): T2, r = true...* resp. true<...*, r' = false...* resp. false<...*.
theorem d9 : ¬ indep0% Std.Roi.forIn'_congr 15 := fun h => by have := @h T2 _ _ _ _ _ Id _ Nat 0 0 ⟨⟨false⟩⟩ ⟨⟨true⟩⟩ (fun _ _ b => pure (ForInStep.done b)) (fun _ _ b => pure (ForInStep.done b)) rfl; revert this; tl

-- `Std.Rii.forIn'_congr` (hypothesis 3, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d10 : ¬ indep0% Std.Rii.forIn'_congr 3 := fun h => nat_not_rxi (@h Nat _ _ _ _ Id _ Nat 0 0 ⟨⟩ ⟨⟩ (fun _ _ b => pure (ForInStep.done b)) (fun _ _ b => pure (ForInStep.done b)) rfl rfl (fun _ _ _ => rfl))

-- `Std.Rii.forIn'_congr` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d11 : ¬ indep0% Std.Rii.forIn'_congr 4 := fun h => UBad.not_lue (@h UBad _ _ _ _ Id _ Nat 0 0 ⟨⟩ ⟨⟩ (fun _ _ b => pure (ForInStep.done b)) (fun _ _ b => pure (ForInStep.done b)) rfl rfl (fun _ _ _ => rfl))

-- `Std.Rii.forIn'_congr` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerableLeast? α`): T2least (T2 with least? = some true) satisfies the other hypotheses, false is not above true.
theorem d12 : ¬ indep0% Std.Rii.forIn'_congr 5 := fun h => T2least.not_lleast (@h T2least _ _ _ _ Id _ Nat 0 0 ⟨⟩ ⟨⟩ (fun _ _ b => pure (ForInStep.done b)) (fun _ _ b => pure (ForInStep.done b)) rfl rfl (fun _ _ _ => rfl))

-- `Std.Rci.toList_eq_toList_roi` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d13 : ¬ indep0% Std.Rci.toList_eq_toList_roi 3 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _)

-- `Std.Rci.toList_eq_toList_roi` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d14 : ¬ indep0% Std.Rci.toList_eq_toList_roi 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _)

-- `Std.Rci.toArray_eq_toArray_roi` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d15 : ¬ indep0% Std.Rci.toArray_eq_toArray_roi 3 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _)

-- `Std.Rci.toArray_eq_toArray_roi` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d16 : ¬ indep0% Std.Rci.toArray_eq_toArray_roi 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _)

-- `Std.Rci.toArray_toList` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d17 : ¬ indep0% Std.Rci.toArray_toList 3 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _)

-- `Std.Rci.toArray_toList` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d18 : ¬ indep0% Std.Rci.toArray_toList 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _)

-- `Std.Rci.toList_toArray` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d19 : ¬ indep0% Std.Rci.toList_toArray 3 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _)

-- `Std.Rci.toList_toArray` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d20 : ¬ indep0% Std.Rci.toList_toArray 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _)

-- `Std.Rci.toList_ne_nil` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d21 : ¬ indep0% Std.Rci.toList_ne_nil 3 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _)

-- `Std.Rci.toList_ne_nil` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d22 : ¬ indep0% Std.Rci.toList_ne_nil 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _)

-- `Std.Rci.toArray_ne_nil` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d23 : ¬ indep0% Std.Rci.toArray_ne_nil 3 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _)

-- `Std.Rci.toArray_ne_nil` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d24 : ¬ indep0% Std.Rci.toArray_ne_nil 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _)

-- `Std.Rci.mem_toList_iff_mem` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d25 : ¬ indep0% Std.Rci.mem_toList_iff_mem 4 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ ⟨⟩)

-- `Std.Rci.mem_toList_iff_mem` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d26 : ¬ indep0% Std.Rci.mem_toList_iff_mem 6 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ 0)

-- `Std.Rci.mem_toArray_iff_mem` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d27 : ¬ indep0% Std.Rci.mem_toArray_iff_mem 4 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ ⟨⟩)

-- `Std.Rci.mem_toArray_iff_mem` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d28 : ¬ indep0% Std.Rci.mem_toArray_iff_mem 6 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ 0)

-- `Std.Rci.pairwise_toList_upwardEnumerableLt` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d29 : ¬ indep0% Std.Rci.pairwise_toList_upwardEnumerableLt 4 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _)

-- `Std.Rci.pairwise_toList_upwardEnumerableLt` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d30 : ¬ indep0% Std.Rci.pairwise_toList_upwardEnumerableLt 5 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _)

-- `Std.Rci.nodup_toList` (hypothesis 2, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d31 : ¬ indep0% Std.Rci.nodup_toList 2 := fun h => nat_not_rxi (@h Nat _ _ 0)

-- `Std.Rci.nodup_toList` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d32 : ¬ indep0% Std.Rci.nodup_toList 3 := fun h => UBad.not_lue (@h UBad _ _ ⟨⟩)

-- `Std.Rci.pairwise_toList_ne` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d33 : ¬ indep0% Std.Rci.pairwise_toList_ne 4 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _)

-- `Std.Rci.pairwise_toList_ne` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d34 : ¬ indep0% Std.Rci.pairwise_toList_ne 5 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _)

-- `Std.Rci.pairwise_toList_lt` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d35 : ¬ indep0% Std.Rci.pairwise_toList_lt 5 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _)

-- `Std.Rci.pairwise_toList_lt` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d36 : ¬ indep0% Std.Rci.pairwise_toList_lt 7 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _)

-- `Std.Rci.pairwise_toList_le` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d37 : ¬ indep0% Std.Rci.pairwise_toList_le 4 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _)

-- `Std.Rci.pairwise_toList_le` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d38 : ¬ indep0% Std.Rci.pairwise_toList_le 6 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _)

-- `Std.Rci.mem_succ_iff` (hypothesis 5, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d39 : ¬ indep0% Std.Rci.mem_succ_iff 5 := fun h => T2.not_inf (@h T2 _ _ _ _ _ _ ⟨false⟩ ⟨false⟩)

-- `Std.Rci.succ_mem_succ_succ_iff` (hypothesis 5, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d40 : ¬ indep0% Std.Rci.succ_mem_succ_succ_iff 5 := fun h => T2.not_inf (@h T2 _ _ _ _ _ _ ⟨false⟩ ⟨false⟩)

-- `Std.Rci.toList_succ_succ_eq_map` (hypothesis 6, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d41 : ¬ indep0% Std.Rci.toList_succ_succ_eq_map 6 := fun h => T2.not_inf (@h T2 _ _ _ _ _ _ _ ⟨false⟩)

-- `Std.Rci.toList_succ_succ_eq_map` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d42 : ¬ indep0% Std.Rci.toList_succ_succ_eq_map 7 := fun h => nat_not_rxi (@h Nat _ _ _ _ _ _ _ 0)

-- `Std.Rci.toList_succ_succ_eq_map` (hypothesis 8, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d43 : ¬ indep0% Std.Rci.toList_succ_succ_eq_map 8 := fun h => NoneMany.not_lue (@h NoneMany _ _ _ _ _ _ _ ⟨0⟩)

-- `Std.Rci.toArray_succ_succ_eq_map` (hypothesis 6, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d44 : ¬ indep0% Std.Rci.toArray_succ_succ_eq_map 6 := fun h => T2.not_inf (@h T2 _ _ _ _ _ _ _ ⟨false⟩)

-- `Std.Rci.toArray_succ_succ_eq_map` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d45 : ¬ indep0% Std.Rci.toArray_succ_succ_eq_map 7 := fun h => nat_not_rxi (@h Nat _ _ _ _ _ _ _ 0)

-- `Std.Rci.toArray_succ_succ_eq_map` (hypothesis 8, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d46 : ¬ indep0% Std.Rci.toArray_succ_succ_eq_map 8 := fun h => NoneMany.not_lue (@h NoneMany _ _ _ _ _ _ _ ⟨0⟩)

-- `Std.Rci.forIn'_eq_forIn'_toList` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerableLE α`): T2le (T2 with ≤ always false) satisfies the other hypotheses, ¬ false ≤ false.
theorem d47 : ¬ indep0% Std.Rci.forIn'_eq_forIn'_toList 4 := fun h => T2le.not_lle (@h T2le ⟨⟨true⟩⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rci.forIn'_eq_forIn'_toList` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d48 : ¬ indep0% Std.Rci.forIn'_eq_forIn'_toList 5 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rci.forIn'_eq_forIn'_toList` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d49 : ¬ indep0% Std.Rci.forIn'_eq_forIn'_toList 6 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rci.forIn'_eq_forIn'_toArray` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerableLE α`): T2le (T2 with ≤ always false) satisfies the other hypotheses, ¬ false ≤ false.
theorem d50 : ¬ indep0% Std.Rci.forIn'_eq_forIn'_toArray 4 := fun h => T2le.not_lle (@h T2le ⟨⟨true⟩⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rci.forIn'_eq_forIn'_toArray` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d51 : ¬ indep0% Std.Rci.forIn'_eq_forIn'_toArray 5 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rci.forIn'_eq_forIn'_toArray` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d52 : ¬ indep0% Std.Rci.forIn'_eq_forIn'_toArray 6 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rci.forIn'_toList_eq_forIn'` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerableLE α`): T2le (T2 with ≤ always false) satisfies the other hypotheses, ¬ false ≤ false.
theorem d53 : ¬ indep0% Std.Rci.forIn'_toList_eq_forIn' 4 := fun h => T2le.not_lle (@h T2le ⟨⟨true⟩⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rci.forIn'_toList_eq_forIn'` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d54 : ¬ indep0% Std.Rci.forIn'_toList_eq_forIn' 5 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ Nat 0 Id _ _)

-- `Std.Rci.forIn'_toList_eq_forIn'` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d55 : ¬ indep0% Std.Rci.forIn'_toList_eq_forIn' 6 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ Nat 0 Id _ _)

-- `Std.Rci.forIn'_toArray_eq_forIn'` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerableLE α`): T2le (T2 with ≤ always false) satisfies the other hypotheses, ¬ false ≤ false.
theorem d56 : ¬ indep0% Std.Rci.forIn'_toArray_eq_forIn' 4 := fun h => T2le.not_lle (@h T2le ⟨⟨true⟩⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rci.forIn'_toArray_eq_forIn'` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d57 : ¬ indep0% Std.Rci.forIn'_toArray_eq_forIn' 5 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ Nat 0 Id _ _)

-- `Std.Rci.forIn'_toArray_eq_forIn'` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d58 : ¬ indep0% Std.Rci.forIn'_toArray_eq_forIn' 6 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ Nat 0 Id _ _)

-- `Std.Rci.forIn'_eq_match` (hypothesis 7, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d59 : ¬ indep0% Std.Rci.forIn'_eq_match 7 := fun h => T2lt.not_llt (@h T2lt ⟨⟨true⟩⟩ _ _ _ _ _ _ _ _ Id _ _ Nat 0 (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rci.forIn'_eq_match` (hypothesis 8, dependent: `Std.PRange.LawfulUpwardEnumerableLE α`): T2le (T2 with ≤ always false) satisfies the other hypotheses, ¬ false ≤ false.
theorem d60 : ¬ indep0% Std.Rci.forIn'_eq_match 8 := fun h => T2le.not_lle (@h T2le ⟨⟨true⟩⟩ _ _ _ _ _ _ _ _ Id _ _ Nat 0 (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rci.forIn'_eq_match` (hypothesis 9, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d61 : ¬ indep0% Std.Rci.forIn'_eq_match 9 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ _ _ _ Id _ _ Nat 0 (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rci.forIn'_eq_match` (hypothesis 10, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d62 : ¬ indep0% Std.Rci.forIn'_eq_match 10 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ _ _ _ Id _ _ Nat 0 (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roi.toArray_toList` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d63 : ¬ indep0% Std.Roi.toArray_toList 3 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _)

-- `Std.Roi.toArray_toList` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d64 : ¬ indep0% Std.Roi.toArray_toList 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _)

-- `Std.Roi.toList_toArray` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d65 : ¬ indep0% Std.Roi.toList_toArray 3 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _)

-- `Std.Roi.toList_toArray` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d66 : ¬ indep0% Std.Roi.toList_toArray 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _)

-- `Std.Roi.toList_eq_match` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d67 : ¬ indep0% Std.Roi.toList_eq_match 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _)

-- `Std.Roi.toArray_eq_match` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d68 : ¬ indep0% Std.Roi.toArray_eq_match 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _)

-- `Std.Roi.toArray_eq_match_rci` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d69 : ¬ indep0% Std.Roi.toArray_eq_match_rci 3 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _)

-- `Std.Roi.toArray_eq_match_rci` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d70 : ¬ indep0% Std.Roi.toArray_eq_match_rci 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _)

-- `Std.Roi.toList_eq_match_rci` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d71 : ¬ indep0% Std.Roi.toList_eq_match_rci 3 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _)

-- `Std.Roi.toList_eq_match_rci` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d72 : ¬ indep0% Std.Roi.toList_eq_match_rci 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _)

-- `Std.Roi.toList_eq_nil_iff` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d73 : ¬ indep0% Std.Roi.toList_eq_nil_iff 3 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _)

-- `Std.Roi.toList_eq_nil_iff` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d74 : ¬ indep0% Std.Roi.toList_eq_nil_iff 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _)

-- `Std.Roi.toArray_eq_empty_iff` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d75 : ¬ indep0% Std.Roi.toArray_eq_empty_iff 3 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _)

-- `Std.Roi.toArray_eq_empty_iff` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d76 : ¬ indep0% Std.Roi.toArray_eq_empty_iff 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _)

-- `Std.Roi.mem_toList_iff_mem` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d77 : ¬ indep0% Std.Roi.mem_toList_iff_mem 4 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ ⟨⟩)

-- `Std.Roi.mem_toList_iff_mem` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d78 : ¬ indep0% Std.Roi.mem_toList_iff_mem 5 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ 0)

-- `Std.Roi.mem_toArray_iff_mem` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d79 : ¬ indep0% Std.Roi.mem_toArray_iff_mem 4 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ ⟨⟩)

-- `Std.Roi.mem_toArray_iff_mem` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d80 : ¬ indep0% Std.Roi.mem_toArray_iff_mem 5 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ 0)

-- `Std.Roi.pairwise_toList_upwardEnumerableLt` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d81 : ¬ indep0% Std.Roi.pairwise_toList_upwardEnumerableLt 3 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _)

-- `Std.Roi.pairwise_toList_upwardEnumerableLt` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d82 : ¬ indep0% Std.Roi.pairwise_toList_upwardEnumerableLt 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _)

-- `Std.Roi.nodup_toList` (hypothesis 2, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d83 : ¬ indep0% Std.Roi.nodup_toList 2 := fun h => nat_not_rxi (@h Nat _ _ 0)

-- `Std.Roi.nodup_toList` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d84 : ¬ indep0% Std.Roi.nodup_toList 3 := fun h => UBad.not_lue (@h UBad _ _ ⟨⟩)

-- `Std.Roi.pairwise_toList_ne` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d85 : ¬ indep0% Std.Roi.pairwise_toList_ne 3 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _)

-- `Std.Roi.pairwise_toList_ne` (hypothesis 4, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d86 : ¬ indep0% Std.Roi.pairwise_toList_ne 4 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _)

-- `Std.Roi.pairwise_toList_lt` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d87 : ¬ indep0% Std.Roi.pairwise_toList_lt 4 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _)

-- `Std.Roi.pairwise_toList_lt` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d88 : ¬ indep0% Std.Roi.pairwise_toList_lt 6 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _)

-- `Std.Roi.pairwise_toList_le` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d89 : ¬ indep0% Std.Roi.pairwise_toList_le 4 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _)

-- `Std.Roi.pairwise_toList_le` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d90 : ¬ indep0% Std.Roi.pairwise_toList_le 6 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _)

-- `Std.Roi.mem_succ_iff` (hypothesis 5, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d91 : ¬ indep0% Std.Roi.mem_succ_iff 5 := fun h => T2.not_inf (@h T2 _ _ _ _ _ _ ⟨false⟩ ⟨false⟩)

-- `Std.Roi.succ_mem_succ_succ_iff` (hypothesis 5, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d92 : ¬ indep0% Std.Roi.succ_mem_succ_succ_iff 5 := fun h => T2.not_inf (@h T2 _ _ _ _ _ _ ⟨false⟩ ⟨false⟩)

-- `Std.Roi.toList_succ_succ_eq_map` (hypothesis 5, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d93 : ¬ indep0% Std.Roi.toList_succ_succ_eq_map 5 := fun h => T2.not_inf (@h T2 _ _ _ _ _ _ _ ⟨false⟩)

-- `Std.Roi.toList_succ_succ_eq_map` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d94 : ¬ indep0% Std.Roi.toList_succ_succ_eq_map 6 := fun h => nat_not_rxi (@h Nat _ _ _ _ _ _ _ 0)

-- `Std.Roi.toList_succ_succ_eq_map` (hypothesis 7, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d95 : ¬ indep0% Std.Roi.toList_succ_succ_eq_map 7 := fun h => NoneMany.not_lue (@h NoneMany _ _ _ _ _ _ _ ⟨0⟩)

-- `Std.Roi.toArray_succ_succ_eq_map` (hypothesis 5, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d96 : ¬ indep0% Std.Roi.toArray_succ_succ_eq_map 5 := fun h => T2.not_inf (@h T2 _ _ _ _ _ _ _ ⟨false⟩)

-- `Std.Roi.toArray_succ_succ_eq_map` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d97 : ¬ indep0% Std.Roi.toArray_succ_succ_eq_map 6 := fun h => nat_not_rxi (@h Nat _ _ _ _ _ _ _ 0)

-- `Std.Roi.toArray_succ_succ_eq_map` (hypothesis 7, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d98 : ¬ indep0% Std.Roi.toArray_succ_succ_eq_map 7 := fun h => NoneMany.not_lue (@h NoneMany _ _ _ _ _ _ _ ⟨0⟩)

-- `Std.Roi.forIn'_eq_forIn'_toList` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d99 : ¬ indep0% Std.Roi.forIn'_eq_forIn'_toList 4 := fun h => T2lt.not_llt (@h T2lt ⟨⟨false⟩⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roi.forIn'_eq_forIn'_toList` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d100 : ¬ indep0% Std.Roi.forIn'_eq_forIn'_toList 5 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roi.forIn'_eq_forIn'_toList` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d101 : ¬ indep0% Std.Roi.forIn'_eq_forIn'_toList 6 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roi.forIn'_eq_forIn'_toArray` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d102 : ¬ indep0% Std.Roi.forIn'_eq_forIn'_toArray 4 := fun h => T2lt.not_llt (@h T2lt ⟨⟨false⟩⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roi.forIn'_eq_forIn'_toArray` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d103 : ¬ indep0% Std.Roi.forIn'_eq_forIn'_toArray 5 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roi.forIn'_eq_forIn'_toArray` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d104 : ¬ indep0% Std.Roi.forIn'_eq_forIn'_toArray 6 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roi.forIn'_toList_eq_forIn'` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d105 : ¬ indep0% Std.Roi.forIn'_toList_eq_forIn' 5 := fun h => T2lt.not_llt (@h T2lt ⟨⟨false⟩⟩ _ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roi.forIn'_toList_eq_forIn'` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d106 : ¬ indep0% Std.Roi.forIn'_toList_eq_forIn' 6 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ Nat 0 Id _ _)

-- `Std.Roi.forIn'_toList_eq_forIn'` (hypothesis 7, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d107 : ¬ indep0% Std.Roi.forIn'_toList_eq_forIn' 7 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ Nat 0 Id _ _)

-- `Std.Roi.forIn'_toArray_eq_forIn'` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d108 : ¬ indep0% Std.Roi.forIn'_toArray_eq_forIn' 5 := fun h => T2lt.not_llt (@h T2lt ⟨⟨false⟩⟩ _ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roi.forIn'_toArray_eq_forIn'` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d109 : ¬ indep0% Std.Roi.forIn'_toArray_eq_forIn' 6 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ Nat 0 Id _ _)

-- `Std.Roi.forIn'_toArray_eq_forIn'` (hypothesis 7, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d110 : ¬ indep0% Std.Roi.forIn'_toArray_eq_forIn' 7 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ Nat 0 Id _ _)

-- `Std.Roi.forIn'_eq_match` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d111 : ¬ indep0% Std.Roi.forIn'_eq_match 5 := fun h => T2lt.not_llt (@h T2lt ⟨⟨false⟩⟩ _ _ _ _ _ Id _ _ Nat 0 (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roi.forIn'_eq_match` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d112 : ¬ indep0% Std.Roi.forIn'_eq_match 6 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ Id _ _ Nat 0 (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Roi.forIn'_eq_match` (hypothesis 7, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d113 : ¬ indep0% Std.Roi.forIn'_eq_match 7 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ Id _ _ Nat 0 (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.toArray_toList` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d114 : ¬ indep0% Std.Rii.toArray_toList 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _)

-- `Std.Rii.toArray_toList` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d115 : ¬ indep0% Std.Rii.toArray_toList 5 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _)

-- `Std.Rii.toList_toArray` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d116 : ¬ indep0% Std.Rii.toList_toArray 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _)

-- `Std.Rii.toList_toArray` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d117 : ¬ indep0% Std.Rii.toList_toArray 5 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _)

-- `Std.Rii.toList_eq_match_rci` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d118 : ¬ indep0% Std.Rii.toList_eq_match_rci 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _)

-- `Std.Rii.toList_eq_match_rci` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d119 : ¬ indep0% Std.Rii.toList_eq_match_rci 5 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _)

-- `Std.Rii.toArray_eq_match_rci` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d120 : ¬ indep0% Std.Rii.toArray_eq_match_rci 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _)

-- `Std.Rii.toArray_eq_match_rci` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d121 : ¬ indep0% Std.Rii.toArray_eq_match_rci 6 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _)

-- `Std.Rii.toList_eq_match_roi` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d122 : ¬ indep0% Std.Rii.toList_eq_match_roi 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _)

-- `Std.Rii.toList_eq_match_roi` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d123 : ¬ indep0% Std.Rii.toList_eq_match_roi 5 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _)

-- `Std.Rii.toArray_eq_match_roi` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d124 : ¬ indep0% Std.Rii.toArray_eq_match_roi 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _)

-- `Std.Rii.toArray_eq_match_roi` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d125 : ¬ indep0% Std.Rii.toArray_eq_match_roi 6 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _)

-- `Std.Rii.toList_eq_nil_iff` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d126 : ¬ indep0% Std.Rii.toList_eq_nil_iff 6 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ _ _ _)

-- `Std.Rii.toList_eq_nil_iff` (hypothesis 9, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d127 : ¬ indep0% Std.Rii.toList_eq_nil_iff 9 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ _ _ _)

-- `Std.Rii.toArray_eq_empty_iff` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d128 : ¬ indep0% Std.Rii.toArray_eq_empty_iff 6 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ _ _ _)

-- `Std.Rii.toArray_eq_empty_iff` (hypothesis 9, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d129 : ¬ indep0% Std.Rii.toArray_eq_empty_iff 9 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ _ _ _)

-- `Std.Rii.mem_iff_mem_rci` (hypothesis 7, dependent: `Std.PRange.LawfulUpwardEnumerableLeast? α`): T2least (T2 with least? = some true) satisfies the other hypotheses, false is not above true.
theorem d130 : ¬ indep0% Std.Rii.mem_iff_mem_rci 7 := fun h => T2least.not_lleast (@h T2least ⟨⟩ _ _ _ _ _ _ ⟨false⟩)

-- `Std.Rii.mem_toList` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d131 : ¬ indep0% Std.Rii.mem_toList 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ ⟨⟩)

-- `Std.Rii.mem_toList` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d132 : ¬ indep0% Std.Rii.mem_toList 6 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ 0)

-- `Std.Rii.mem_toArray` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d133 : ¬ indep0% Std.Rii.mem_toArray 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ ⟨⟩)

-- `Std.Rii.mem_toArray` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d134 : ¬ indep0% Std.Rii.mem_toArray 6 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ 0)

-- `Std.Rii.pairwise_toList_upwardEnumerableLt` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d135 : ¬ indep0% Std.Rii.pairwise_toList_upwardEnumerableLt 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _)

-- `Std.Rii.pairwise_toList_upwardEnumerableLt` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d136 : ¬ indep0% Std.Rii.pairwise_toList_upwardEnumerableLt 6 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _)

-- `Std.Rii.nodup_toList` (hypothesis 3, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d137 : ¬ indep0% Std.Rii.nodup_toList 3 := fun h => nat_not_rxi (@h Nat _ _ _)

-- `Std.Rii.nodup_toList` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d138 : ¬ indep0% Std.Rii.nodup_toList 4 := fun h => UBad.not_lue (@h UBad _ _ _)

-- `Std.Rii.pairwise_toList_ne` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d139 : ¬ indep0% Std.Rii.pairwise_toList_ne 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _)

-- `Std.Rii.pairwise_toList_ne` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d140 : ¬ indep0% Std.Rii.pairwise_toList_ne 6 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _)

-- `Std.Rii.pairwise_toList_lt` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d141 : ¬ indep0% Std.Rii.pairwise_toList_lt 5 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ _ _)

-- `Std.Rii.pairwise_toList_lt` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d142 : ¬ indep0% Std.Rii.pairwise_toList_lt 7 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ _ _)

-- `Std.Rii.pairwise_toList_le` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d143 : ¬ indep0% Std.Rii.pairwise_toList_le 5 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ _ _)

-- `Std.Rii.pairwise_toList_le` (hypothesis 8, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d144 : ¬ indep0% Std.Rii.pairwise_toList_le 8 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ _ _)

-- `Std.Rii.forIn'_eq_forIn'_toList` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerableLeast? α`): T2least (T2 with least? = some true) satisfies the other hypotheses, false is not above true.
theorem d145 : ¬ indep0% Std.Rii.forIn'_eq_forIn'_toList 4 := fun h => T2least.not_lleast (@h T2least ⟨⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.forIn'_eq_forIn'_toList` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d146 : ¬ indep0% Std.Rii.forIn'_eq_forIn'_toList 5 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.forIn'_eq_forIn'_toList` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d147 : ¬ indep0% Std.Rii.forIn'_eq_forIn'_toList 6 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.forIn'_eq_forIn'_toArray` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerableLeast? α`): T2least (T2 with least? = some true) satisfies the other hypotheses, false is not above true.
theorem d148 : ¬ indep0% Std.Rii.forIn'_eq_forIn'_toArray 4 := fun h => T2least.not_lleast (@h T2least ⟨⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.forIn'_eq_forIn'_toArray` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d149 : ¬ indep0% Std.Rii.forIn'_eq_forIn'_toArray 5 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.forIn'_eq_forIn'_toArray` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d150 : ¬ indep0% Std.Rii.forIn'_eq_forIn'_toArray 6 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.forIn'_toList_eq_forIn'` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerableLeast? α`): T2least (T2 with least? = some true) satisfies the other hypotheses, false is not above true.
theorem d151 : ¬ indep0% Std.Rii.forIn'_toList_eq_forIn' 6 := fun h => T2least.not_lleast (@h T2least ⟨⟩ _ _ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.forIn'_toList_eq_forIn'` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d152 : ¬ indep0% Std.Rii.forIn'_toList_eq_forIn' 7 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ _ _ Nat 0 Id _ _)

-- `Std.Rii.forIn'_toList_eq_forIn'` (hypothesis 8, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d153 : ¬ indep0% Std.Rii.forIn'_toList_eq_forIn' 8 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ _ _ Nat 0 Id _ _)

-- `Std.Rii.forIn'_toArray_eq_forIn'` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerableLeast? α`): T2least (T2 with least? = some true) satisfies the other hypotheses, false is not above true.
theorem d154 : ¬ indep0% Std.Rii.forIn'_toArray_eq_forIn' 6 := fun h => T2least.not_lleast (@h T2least ⟨⟩ _ _ _ _ _ _ Nat 0 Id _ _ (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.forIn'_toArray_eq_forIn'` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d155 : ¬ indep0% Std.Rii.forIn'_toArray_eq_forIn' 7 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ _ _ Nat 0 Id _ _)

-- `Std.Rii.forIn'_toArray_eq_forIn'` (hypothesis 8, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d156 : ¬ indep0% Std.Rii.forIn'_toArray_eq_forIn' 8 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ _ _ Nat 0 Id _ _)

-- `Std.Rii.forIn'_eq_match_rci` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerableLE α`): T2le (T2 with ≤ always false) satisfies the other hypotheses, ¬ false ≤ false.
theorem d157 : ¬ indep0% Std.Rii.forIn'_eq_match_rci 5 := fun h => T2le.not_lle (@h T2le ⟨⟩ _ _ _ _ _ _ Id _ _ Nat 0 (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.forIn'_eq_match_rci` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerableLeast? α`): T2least (T2 with least? = some true) satisfies the other hypotheses, false is not above true.
theorem d158 : ¬ indep0% Std.Rii.forIn'_eq_match_rci 6 := fun h => T2least.not_lleast (@h T2least ⟨⟩ _ _ _ _ _ _ Id _ _ Nat 0 (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.forIn'_eq_match_rci` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d159 : ¬ indep0% Std.Rii.forIn'_eq_match_rci 7 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ _ _ Id _ _ Nat 0 (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.forIn'_eq_match_rci` (hypothesis 8, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d160 : ¬ indep0% Std.Rii.forIn'_eq_match_rci 8 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ _ _ Id _ _ Nat 0 (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.forIn'_eq_match_roi` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d161 : ¬ indep0% Std.Rii.forIn'_eq_match_roi 6 := fun h => T2lt.not_llt (@h T2lt ⟨⟩ trivial _ _ _ _ _ _ Id _ _ Nat 0 (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.forIn'_eq_match_roi` (hypothesis 7, dependent: `Std.PRange.LawfulUpwardEnumerableLeast? α`): T2least (T2 with least? = some true) satisfies the other hypotheses, false is not above true.
theorem d162 : ¬ indep0% Std.Rii.forIn'_eq_match_roi 7 := fun h => T2least.not_lleast (@h T2least ⟨⟩ trivial _ _ _ _ _ _ Id _ _ Nat 0 (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.forIn'_eq_match_roi` (hypothesis 8, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d163 : ¬ indep0% Std.Rii.forIn'_eq_match_roi 8 := fun h => nat_not_rxi (@h Nat ⟨⟩ trivial _ _ _ _ _ _ Id _ _ Nat 0 (fun _ _ b => pure (ForInStep.done b)))

-- `Std.Rii.forIn'_eq_match_roi` (hypothesis 9, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d164 : ¬ indep0% Std.Rii.forIn'_eq_match_roi 9 := fun h => UBad.not_lue (@h UBad ⟨⟩ trivial _ _ _ _ _ _ Id _ _ Nat 0 (fun _ _ b => pure (ForInStep.done b)))

-- `Std.toList_roc_eq_toList_rcc_of_isSome_succ?` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d165 : ¬ indep0% Std.toList_roc_eq_toList_rcc_of_isSome_succ? 4 := fun h => NoneMany.not_lue (@h NoneMany _ _ _ _ _ ⟨0⟩ ⟨0⟩ rfl)

-- `Std.toList_roc_eq_toList_rcc_of_isSome_succ?` (hypothesis 9, dependent: `(Std.PRange.succ? lo).isSome = true`): T2, lo = true: succ? true = none.
theorem d166 : ¬ indep0% Std.toList_roc_eq_toList_rcc_of_isSome_succ? 9 := fun h => by have := @h T2 _ _ _ _ _ _ ⟨true⟩ ⟨false⟩; revert this; tl

-- `Std.toList_roo_eq_toList_rco_of_isSome_succ?` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d167 : ¬ indep0% Std.toList_roo_eq_toList_rco_of_isSome_succ? 4 := fun h => NoneMany.not_lue (@h NoneMany _ _ _ _ _ ⟨0⟩ ⟨0⟩ rfl)

-- `Std.toList_roo_eq_toList_rco_of_isSome_succ?` (hypothesis 9, dependent: `(Std.PRange.succ? lo).isSome = true`): T2, lo = true: succ? true = none.
theorem d168 : ¬ indep0% Std.toList_roo_eq_toList_rco_of_isSome_succ? 9 := fun h => by have := @h T2 _ _ _ _ _ _ ⟨true⟩ ⟨false⟩; revert this; tl

-- `Std.toList_roi_eq_toList_rci_of_isSome_succ?` (hypothesis 2, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d169 : ¬ indep0% Std.toList_roi_eq_toList_rci_of_isSome_succ? 2 := fun h => NoneMany.not_lue (@h NoneMany _ _ ⟨0⟩ rfl)

-- `Std.toList_roi_eq_toList_rci_of_isSome_succ?` (hypothesis 3, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d170 : ¬ indep0% Std.toList_roi_eq_toList_rci_of_isSome_succ? 3 := fun h => nat_not_rxi (@h Nat _ _ 0 rfl)

-- `Std.toList_roi_eq_toList_rci_of_isSome_succ?` (hypothesis 5, dependent: `(Std.PRange.succ? lo).isSome = true`): T2, lo = true: succ? true = none.
theorem d171 : ¬ indep0% Std.toList_roi_eq_toList_rci_of_isSome_succ? 5 := fun h => by have := @h T2 _ _ _ ⟨true⟩; revert this; tl

-- `Std.Rci.length_toList` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d172 : ¬ indep0% Std.Rci.length_toList 4 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _)

-- `Std.Rci.length_toList` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): derivable from `LawfulUpwardEnumerable` + `Rxi.LawfulHasSize` (rxi_of_hasSize).
theorem d173 : indep% Std.Rci.length_toList 5 := by intros; exact rxi_of_hasSize

-- `Std.Rci.size_toArray` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d174 : ¬ indep0% Std.Rci.size_toArray 4 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _)

-- `Std.Rci.size_toArray` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): derivable from `LawfulUpwardEnumerable` + `Rxi.LawfulHasSize` (rxi_of_hasSize).
theorem d175 : indep% Std.Rci.size_toArray 5 := by intros; exact rxi_of_hasSize

-- `Std.Rci.getElem?_toList_eq` (hypothesis 2, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d176 : ¬ indep0% Std.Rci.getElem?_toList_eq 2 := fun h => UBad.not_lue (@h UBad _ _ ⟨⟨⟩⟩ 0)

-- `Std.Rci.getElem?_toList_eq` (hypothesis 3, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d177 : ¬ indep0% Std.Rci.getElem?_toList_eq 3 := fun h => nat_not_rxi (@h Nat _ _ ⟨0⟩ 0)

-- `Std.Rci.getElem?_toArray_eq` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d178 : ¬ indep0% Std.Rci.getElem?_toArray_eq 5 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ 0)

-- `Std.Rci.getElem?_toArray_eq` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d179 : ¬ indep0% Std.Rci.getElem?_toArray_eq 7 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ 0)

-- `Std.Rci.isSome_succMany?_of_lt_length_toList` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d180 : ¬ indep0% Std.Rci.isSome_succMany?_of_lt_length_toList 5 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ 0)

-- `Std.Rci.isSome_succMany?_of_lt_length_toList` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d181 : ¬ indep0% Std.Rci.isSome_succMany?_of_lt_length_toList 7 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ 0)

-- `Std.Rci.isSome_succMany?_of_lt_size_toArray` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d182 : ¬ indep0% Std.Rci.isSome_succMany?_of_lt_size_toArray 5 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ 0)

-- `Std.Rci.isSome_succMany?_of_lt_size_toArray` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d183 : ¬ indep0% Std.Rci.isSome_succMany?_of_lt_size_toArray 7 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ 0)

-- `Std.Rci.getElem_toList_eq` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d184 : ¬ indep0% Std.Rci.getElem_toList_eq 5 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ 0)

-- `Std.Rci.getElem_toList_eq` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d185 : ¬ indep0% Std.Rci.getElem_toList_eq 6 := fun h => T2lt.not_llt (@h T2lt ⟨⟨true⟩⟩ _ _ _ _ _ 0 (by tl))

-- `Std.Rci.getElem_toList_eq` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d186 : ¬ indep0% Std.Rci.getElem_toList_eq 7 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ 0)

-- `Std.Rci.getElem_toList_eq` (hypothesis 9, dependent: `i < r.toList.length`): T2, r with toList = [true] (Rci/Roi) resp. [false, true] (Rii), i = 2.
theorem d187 : ¬ indep0% Std.Rci.getElem_toList_eq 9 := fun h => by have := @h T2 ⟨⟨true⟩⟩ _ _ _ _ _ _ 2; revert this; tl

-- `Std.Rci.getElem_toArray_eq` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d188 : ¬ indep0% Std.Rci.getElem_toArray_eq 5 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ 0)

-- `Std.Rci.getElem_toArray_eq` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d189 : ¬ indep0% Std.Rci.getElem_toArray_eq 6 := fun h => T2lt.not_llt (@h T2lt ⟨⟨true⟩⟩ _ _ _ _ _ 0 (by tl))

-- `Std.Rci.getElem_toArray_eq` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d190 : ¬ indep0% Std.Rci.getElem_toArray_eq 7 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ 0)

-- `Std.Rci.getElem_toArray_eq` (hypothesis 9, dependent: `i < r.toArray.size`): T2, r with toList = [true] (Rci/Roi) resp. [false, true] (Rii), i = 2.
theorem d191 : ¬ indep0% Std.Rci.getElem_toArray_eq 9 := fun h => by have := @h T2 ⟨⟨true⟩⟩ _ _ _ _ _ _ 2; revert this; tl

-- `Std.Rci.eq_succMany?_of_toList_eq_append_cons` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d192 : ¬ indep0% Std.Rci.eq_succMany?_of_toList_eq_append_cons 5 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ [] [] ⟨⟩)

-- `Std.Rci.eq_succMany?_of_toList_eq_append_cons` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d193 : ¬ indep0% Std.Rci.eq_succMany?_of_toList_eq_append_cons 6 := fun h => T2lt.not_llt (@h T2lt ⟨⟨true⟩⟩ _ _ _ _ _ [] [] ⟨true⟩ (by tl))

-- `Std.Rci.eq_succMany?_of_toList_eq_append_cons` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d194 : ¬ indep0% Std.Rci.eq_succMany?_of_toList_eq_append_cons 7 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ [] [] 0)

-- `Std.Rci.eq_succMany?_of_toList_eq_append_cons` (hypothesis 11, dependent: `r.toList = pref ++ cur :: suff`): T2, r with toList = [true] (Rci/Roi) resp. [false, true] (Rii), pref = suff = [], cur = false.
theorem d195 : ¬ indep0% Std.Rci.eq_succMany?_of_toList_eq_append_cons 11 := fun h => by have := @h T2 ⟨⟨true⟩⟩ _ _ _ _ _ _ [] [] ⟨false⟩; revert this; tl

-- `Std.Rci.eq_succMany?_of_toArray_eq_append_append` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d196 : ¬ indep0% Std.Rci.eq_succMany?_of_toArray_eq_append_append 5 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ #[] #[] ⟨⟩)

-- `Std.Rci.eq_succMany?_of_toArray_eq_append_append` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d197 : ¬ indep0% Std.Rci.eq_succMany?_of_toArray_eq_append_append 6 := fun h => T2lt.not_llt (@h T2lt ⟨⟨true⟩⟩ _ _ _ _ _ #[] #[] ⟨true⟩ (by tl))

-- `Std.Rci.eq_succMany?_of_toArray_eq_append_append` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d198 : ¬ indep0% Std.Rci.eq_succMany?_of_toArray_eq_append_append 7 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ #[] #[] 0)

-- `Std.Rci.eq_succMany?_of_toArray_eq_append_append` (hypothesis 11, dependent: `r.toArray = pref ++ #[cur] ++ suff`): T2, r with toList = [true] (Rci/Roi) resp. [false, true] (Rii), pref = suff = [], cur = false.
theorem d199 : ¬ indep0% Std.Rci.eq_succMany?_of_toArray_eq_append_append 11 := fun h => by have := @h T2 ⟨⟨true⟩⟩ _ _ _ _ _ _ #[] #[] ⟨false⟩; revert this; tl

-- `Std.Roi.length_toList` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d200 : ¬ indep0% Std.Roi.length_toList 4 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _)

-- `Std.Roi.length_toList` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): derivable from `LawfulUpwardEnumerable` + `Rxi.LawfulHasSize` (rxi_of_hasSize).
theorem d201 : indep% Std.Roi.length_toList 5 := by intros; exact rxi_of_hasSize

-- `Std.Roi.size_toArray` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d202 : ¬ indep0% Std.Roi.size_toArray 4 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _)

-- `Std.Roi.size_toArray` (hypothesis 5, dependent: `Std.Rxi.IsAlwaysFinite α`): derivable from `LawfulUpwardEnumerable` + `Rxi.LawfulHasSize` (rxi_of_hasSize).
theorem d203 : indep% Std.Roi.size_toArray 5 := by intros; exact rxi_of_hasSize

-- `Std.Roi.getElem?_toList_eq` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d204 : ¬ indep0% Std.Roi.getElem?_toList_eq 5 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ 0)

-- `Std.Roi.getElem?_toList_eq` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d205 : ¬ indep0% Std.Roi.getElem?_toList_eq 7 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ 0)

-- `Std.Roi.getElem?_toArray_eq` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d206 : ¬ indep0% Std.Roi.getElem?_toArray_eq 5 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ 0)

-- `Std.Roi.getElem?_toArray_eq` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d207 : ¬ indep0% Std.Roi.getElem?_toArray_eq 7 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ 0)

-- `Std.Roi.isSome_succMany?_of_lt_length_toList` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d208 : ¬ indep0% Std.Roi.isSome_succMany?_of_lt_length_toList 5 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ 0)

-- `Std.Roi.isSome_succMany?_of_lt_length_toList` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d209 : ¬ indep0% Std.Roi.isSome_succMany?_of_lt_length_toList 7 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ 0)

-- `Std.Roi.isSome_succMany?_of_lt_size_toArray` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d210 : ¬ indep0% Std.Roi.isSome_succMany?_of_lt_size_toArray 5 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ 0)

-- `Std.Roi.isSome_succMany?_of_lt_size_toArray` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d211 : ¬ indep0% Std.Roi.isSome_succMany?_of_lt_size_toArray 7 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ 0)

-- `Std.Roi.getElem_toList_eq` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d212 : ¬ indep0% Std.Roi.getElem_toList_eq 5 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ 0)

-- `Std.Roi.getElem_toList_eq` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d213 : ¬ indep0% Std.Roi.getElem_toList_eq 6 := fun h => T2lt.not_llt (@h T2lt ⟨⟨false⟩⟩ _ _ _ _ _ 0 (by tl))

-- `Std.Roi.getElem_toList_eq` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d214 : ¬ indep0% Std.Roi.getElem_toList_eq 7 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ 0)

-- `Std.Roi.getElem_toList_eq` (hypothesis 9, dependent: `i < r.toList.length`): T2, r with toList = [true] (Rci/Roi) resp. [false, true] (Rii), i = 2.
theorem d215 : ¬ indep0% Std.Roi.getElem_toList_eq 9 := fun h => by have := @h T2 ⟨⟨false⟩⟩ _ _ _ _ _ _ 2; revert this; tl

-- `Std.Roi.getElem_toArray_eq` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d216 : ¬ indep0% Std.Roi.getElem_toArray_eq 4 := fun h => UBad.not_lue (@h UBad _ _ _ _ _ ⟨⟨⟩⟩ 0)

-- `Std.Roi.getElem_toArray_eq` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d217 : ¬ indep0% Std.Roi.getElem_toArray_eq 5 := fun h => T2lt.not_llt (@h T2lt _ _ _ _ _ ⟨⟨false⟩⟩ 0 (by tl))

-- `Std.Roi.getElem_toArray_eq` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d218 : ¬ indep0% Std.Roi.getElem_toArray_eq 6 := fun h => nat_not_rxi (@h Nat _ _ _ _ _ ⟨0⟩ 0)

-- `Std.Roi.getElem_toArray_eq` (hypothesis 9, dependent: `i < r.toArray.size`): T2, r with toList = [true] (Rci/Roi) resp. [false, true] (Rii), i = 2.
theorem d219 : ¬ indep0% Std.Roi.getElem_toArray_eq 9 := fun h => by have := @h T2 _ _ _ _ _ _ ⟨⟨false⟩⟩ 2; revert this; tl

-- `Std.Roi.eq_succMany?_of_toList_eq_append_cons` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d220 : ¬ indep0% Std.Roi.eq_succMany?_of_toList_eq_append_cons 5 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ [] [] ⟨⟩)

-- `Std.Roi.eq_succMany?_of_toList_eq_append_cons` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d221 : ¬ indep0% Std.Roi.eq_succMany?_of_toList_eq_append_cons 6 := fun h => T2lt.not_llt (@h T2lt ⟨⟨false⟩⟩ _ _ _ _ _ [] [] ⟨true⟩ (by tl))

-- `Std.Roi.eq_succMany?_of_toList_eq_append_cons` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d222 : ¬ indep0% Std.Roi.eq_succMany?_of_toList_eq_append_cons 7 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ [] [] 0)

-- `Std.Roi.eq_succMany?_of_toList_eq_append_cons` (hypothesis 11, dependent: `r.toList = pref ++ cur :: suff`): T2, r with toList = [true] (Rci/Roi) resp. [false, true] (Rii), pref = suff = [], cur = false.
theorem d223 : ¬ indep0% Std.Roi.eq_succMany?_of_toList_eq_append_cons 11 := fun h => by have := @h T2 ⟨⟨false⟩⟩ _ _ _ _ _ _ [] [] ⟨false⟩; revert this; tl

-- `Std.Roi.eq_succMany?_of_toArray_eq_append_append` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d224 : ¬ indep0% Std.Roi.eq_succMany?_of_toArray_eq_append_append 5 := fun h => UBad.not_lue (@h UBad ⟨⟨⟩⟩ _ _ _ _ _ #[] #[] ⟨⟩)

-- `Std.Roi.eq_succMany?_of_toArray_eq_append_append` (hypothesis 6, dependent: `Std.PRange.LawfulUpwardEnumerableLT α`): T2lt (T2 with < always false) satisfies the other hypotheses, ¬ false < true.
theorem d225 : ¬ indep0% Std.Roi.eq_succMany?_of_toArray_eq_append_append 6 := fun h => T2lt.not_llt (@h T2lt ⟨⟨false⟩⟩ _ _ _ _ _ #[] #[] ⟨true⟩ (by tl))

-- `Std.Roi.eq_succMany?_of_toArray_eq_append_append` (hypothesis 7, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d226 : ¬ indep0% Std.Roi.eq_succMany?_of_toArray_eq_append_append 7 := fun h => nat_not_rxi (@h Nat ⟨0⟩ _ _ _ _ _ #[] #[] 0)

-- `Std.Roi.eq_succMany?_of_toArray_eq_append_append` (hypothesis 11, dependent: `r.toArray = pref ++ #[cur] ++ suff`): T2, r with toList = [true] (Rci/Roi) resp. [false, true] (Rii), pref = suff = [], cur = false.
theorem d227 : ¬ indep0% Std.Roi.eq_succMany?_of_toArray_eq_append_append 11 := fun h => by have := @h T2 ⟨⟨false⟩⟩ _ _ _ _ _ _ #[] #[] ⟨false⟩; revert this; tl

-- `Std.Rii.length_toList` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d228 : ¬ indep0% Std.Rii.length_toList 5 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ _)

-- `Std.Rii.length_toList` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): derivable from `LawfulUpwardEnumerable` + `Rxi.LawfulHasSize` (rxi_of_hasSize).
theorem d229 : indep% Std.Rii.length_toList 6 := by intros; exact rxi_of_hasSize

-- `Std.Rii.size_toArray` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d230 : ¬ indep0% Std.Rii.size_toArray 5 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ _)

-- `Std.Rii.size_toArray` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): derivable from `LawfulUpwardEnumerable` + `Rxi.LawfulHasSize` (rxi_of_hasSize).
theorem d231 : indep% Std.Rii.size_toArray 6 := by intros; exact rxi_of_hasSize

-- `Std.Rii.getElem?_toList_eq` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d232 : ¬ indep0% Std.Rii.getElem?_toList_eq 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ 0)

-- `Std.Rii.getElem?_toList_eq` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d233 : ¬ indep0% Std.Rii.getElem?_toList_eq 6 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ 0)

-- `Std.Rii.getElem?_toArray_eq` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d234 : ¬ indep0% Std.Rii.getElem?_toArray_eq 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ 0)

-- `Std.Rii.getElem?_toArray_eq` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d235 : ¬ indep0% Std.Rii.getElem?_toArray_eq 6 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ 0)

-- `Std.Rii.isSome_succMany?_of_lt_length_toList` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d236 : ¬ indep0% Std.Rii.isSome_succMany?_of_lt_length_toList 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ 0)

-- `Std.Rii.isSome_succMany?_of_lt_length_toList` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d237 : ¬ indep0% Std.Rii.isSome_succMany?_of_lt_length_toList 6 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ 0)

-- `Std.Rii.isSome_succMany?_of_lt_size_toArray` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d238 : ¬ indep0% Std.Rii.isSome_succMany?_of_lt_size_toArray 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ 0)

-- `Std.Rii.isSome_succMany?_of_lt_size_toArray` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d239 : ¬ indep0% Std.Rii.isSome_succMany?_of_lt_size_toArray 6 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ 0)

-- `Std.Rii.getElem_toList_eq` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d240 : ¬ indep0% Std.Rii.getElem_toList_eq 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ 0)

-- `Std.Rii.getElem_toList_eq` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerableLeast? α`): T2least (T2 with least? = some true) satisfies the other hypotheses, false is not above true.
theorem d241 : ¬ indep0% Std.Rii.getElem_toList_eq 5 := fun h => T2least.not_lleast (@h T2least ⟨⟩ _ _ _ _ 0 (by tl))

-- `Std.Rii.getElem_toList_eq` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d242 : ¬ indep0% Std.Rii.getElem_toList_eq 6 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ 0)

-- `Std.Rii.getElem_toList_eq` (hypothesis 8, dependent: `i < r.toList.length`): T2, r with toList = [true] (Rci/Roi) resp. [false, true] (Rii), i = 2.
theorem d243 : ¬ indep0% Std.Rii.getElem_toList_eq 8 := fun h => by have := @h T2 ⟨⟩ _ _ _ _ _ 2; revert this; tl

-- `Std.Rii.getElem_toArray_eq` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d244 : ¬ indep0% Std.Rii.getElem_toArray_eq 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ 0)

-- `Std.Rii.getElem_toArray_eq` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerableLeast? α`): T2least (T2 with least? = some true) satisfies the other hypotheses, false is not above true.
theorem d245 : ¬ indep0% Std.Rii.getElem_toArray_eq 5 := fun h => T2least.not_lleast (@h T2least ⟨⟩ _ _ _ _ 0 (by tl))

-- `Std.Rii.getElem_toArray_eq` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d246 : ¬ indep0% Std.Rii.getElem_toArray_eq 6 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ 0)

-- `Std.Rii.getElem_toArray_eq` (hypothesis 8, dependent: `i < r.toArray.size`): T2, r with toList = [true] (Rci/Roi) resp. [false, true] (Rii), i = 2.
theorem d247 : ¬ indep0% Std.Rii.getElem_toArray_eq 8 := fun h => by have := @h T2 ⟨⟩ _ _ _ _ _ 2; revert this; tl

-- `Std.Rii.eq_succMany?_of_toList_eq_append_cons` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d248 : ¬ indep0% Std.Rii.eq_succMany?_of_toList_eq_append_cons 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ [] [] ⟨⟩)

-- `Std.Rii.eq_succMany?_of_toList_eq_append_cons` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerableLeast? α`): T2least (T2 with least? = some true) satisfies the other hypotheses, false is not above true.
theorem d249 : ¬ indep0% Std.Rii.eq_succMany?_of_toList_eq_append_cons 5 := fun h => T2least.not_lleast (@h T2least ⟨⟩ _ _ _ _ [] [] ⟨true⟩ (by tl))

-- `Std.Rii.eq_succMany?_of_toList_eq_append_cons` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d250 : ¬ indep0% Std.Rii.eq_succMany?_of_toList_eq_append_cons 6 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ [] [] 0)

-- `Std.Rii.eq_succMany?_of_toList_eq_append_cons` (hypothesis 10, dependent: `r.toList = pref ++ cur :: suff`): T2, r with toList = [true] (Rci/Roi) resp. [false, true] (Rii), pref = suff = [], cur = false.
theorem d251 : ¬ indep0% Std.Rii.eq_succMany?_of_toList_eq_append_cons 10 := fun h => by have := @h T2 ⟨⟩ _ _ _ _ _ [] [] ⟨false⟩; revert this; tl

-- `Std.Rii.eq_succMany?_of_toArray_eq_append_append` (hypothesis 4, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d252 : ¬ indep0% Std.Rii.eq_succMany?_of_toArray_eq_append_append 4 := fun h => UBad.not_lue (@h UBad ⟨⟩ _ _ _ _ #[] #[] ⟨⟩)

-- `Std.Rii.eq_succMany?_of_toArray_eq_append_append` (hypothesis 5, dependent: `Std.PRange.LawfulUpwardEnumerableLeast? α`): T2least (T2 with least? = some true) satisfies the other hypotheses, false is not above true.
theorem d253 : ¬ indep0% Std.Rii.eq_succMany?_of_toArray_eq_append_append 5 := fun h => T2least.not_lleast (@h T2least ⟨⟩ _ _ _ _ #[] #[] ⟨true⟩ (by tl))

-- `Std.Rii.eq_succMany?_of_toArray_eq_append_append` (hypothesis 6, dependent: `Std.Rxi.IsAlwaysFinite α`): Nat with the library instances satisfies the other hypotheses but is not Rxi-finite.
theorem d254 : ¬ indep0% Std.Rii.eq_succMany?_of_toArray_eq_append_append 6 := fun h => nat_not_rxi (@h Nat ⟨⟩ _ _ _ _ #[] #[] 0)

-- `Std.Rii.eq_succMany?_of_toArray_eq_append_append` (hypothesis 10, dependent: `r.toArray = pref ++ #[cur] ++ suff`): T2, r with toList = [true] (Rci/Roi) resp. [false, true] (Rii), pref = suff = [], cur = false.
theorem d255 : ¬ indep0% Std.Rii.eq_succMany?_of_toArray_eq_append_append 10 := fun h => by have := @h T2 ⟨⟩ _ _ _ _ _ #[] #[] ⟨false⟩; revert this; tl

-- `Std.Rxi.Iterator.instLawfulIteratorLoop` (hypothesis 2, dependent: `Std.PRange.LawfulUpwardEnumerable α`): UBad (one element, succ? = none, succMany? 1 a = some a) satisfies the other hypotheses, succMany?_add_one fails.
theorem d256 : ¬ indep0% Std.Rxi.Iterator.instLawfulIteratorLoop 2 := fun h => UBad.not_lue (@h UBad _ Id _ _)

-- `Std.PRange.UpwardEnumerable.succ_eq_get` (hypothesis 2, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d257 : ¬ indep0% Std.PRange.UpwardEnumerable.succ_eq_get 2 := fun h => T2.not_inf (@h T2 _ ⟨false⟩)

-- `Std.PRange.UpwardEnumerable.succ?_eq_some` (hypothesis 2, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d258 : ¬ indep0% Std.PRange.UpwardEnumerable.succ?_eq_some 2 := fun h => T2.not_inf (@h T2 _ ⟨false⟩)

-- `Std.PRange.UpwardEnumerable.succ_inj` (hypothesis 2, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d259 : ¬ indep0% Std.PRange.UpwardEnumerable.succ_inj 2 := fun h => T2.not_inf (@h T2 _ _ ⟨false⟩ ⟨true⟩)

-- `Std.PRange.UpwardEnumerable.succ_eq_succ_iff` (hypothesis 2, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d260 : ¬ indep0% Std.PRange.UpwardEnumerable.succ_eq_succ_iff 2 := fun h => T2.not_inf (@h T2 _ _ ⟨false⟩ ⟨true⟩)

-- `Std.PRange.UpwardEnumerable.succMany_eq_get` (hypothesis 2, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d261 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany_eq_get 2 := fun h => NoneMany.not_lue (@h NoneMany _ _ 0 ⟨0⟩)

-- `Std.PRange.UpwardEnumerable.succMany_eq_get` (hypothesis 3, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d262 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany_eq_get 3 := fun h => T2.not_inf (@h T2 _ _ 0 ⟨false⟩)

-- `Std.PRange.UpwardEnumerable.succMany?_eq_some` (hypothesis 2, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d263 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany?_eq_some 2 := fun h => NoneMany.not_lue (@h NoneMany _ _ 0 ⟨0⟩)

-- `Std.PRange.UpwardEnumerable.succMany?_eq_some` (hypothesis 3, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d264 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany?_eq_some 3 := fun h => T2.not_inf (@h T2 _ _ 0 ⟨false⟩)

-- `Std.PRange.UpwardEnumerable.succMany?_eq_some_iff_succMany` (hypothesis 2, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d265 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany?_eq_some_iff_succMany 2 := fun h => NoneMany.not_lue (@h NoneMany _ _ 0 ⟨0⟩ ⟨0⟩)

-- `Std.PRange.UpwardEnumerable.succMany?_eq_some_iff_succMany` (hypothesis 3, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d266 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany?_eq_some_iff_succMany 3 := fun h => T2.not_inf (@h T2 _ _ 0 ⟨false⟩ ⟨true⟩)

-- `Std.PRange.UpwardEnumerable.succMany_zero` (hypothesis 2, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d267 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany_zero 2 := fun h => NoneMany.not_lue (@h NoneMany _ _ ⟨0⟩)

-- `Std.PRange.UpwardEnumerable.succMany_zero` (hypothesis 3, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d268 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany_zero 3 := fun h => T2.not_inf (@h T2 _ _ ⟨false⟩)

-- `Std.PRange.UpwardEnumerable.succMany_one` (hypothesis 2, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d269 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany_one 2 := fun h => NoneMany.not_lue (@h NoneMany _ _ ⟨0⟩)

-- `Std.PRange.UpwardEnumerable.succMany_one` (hypothesis 3, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d270 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany_one 3 := fun h => T2.not_inf (@h T2 _ _ ⟨false⟩)

-- `Std.PRange.UpwardEnumerable.succMany_succ` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d271 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany_succ 3 := fun h => NoneMany.not_lue (@h 0 NoneMany _ _ ⟨0⟩)

-- `Std.PRange.UpwardEnumerable.succMany_succ` (hypothesis 4, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d272 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany_succ 4 := fun h => T2.not_inf (@h 0 T2 _ _ ⟨false⟩)

-- `Std.PRange.UpwardEnumerable.succMany_add_one_eq_succMany_succ` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d273 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany_add_one_eq_succMany_succ 3 := fun h => NoneMany.not_lue (@h 0 NoneMany _ _ ⟨0⟩)

-- `Std.PRange.UpwardEnumerable.succMany_add_one_eq_succMany_succ` (hypothesis 4, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d274 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany_add_one_eq_succMany_succ 4 := fun h => T2.not_inf (@h 0 T2 _ _ ⟨false⟩)

-- `Std.PRange.UpwardEnumerable.succMany_succ_eq_succ_succMany` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d275 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany_succ_eq_succ_succMany 3 := fun h => NoneMany.not_lue (@h 0 NoneMany _ _ ⟨0⟩)

-- `Std.PRange.UpwardEnumerable.succMany_succ_eq_succ_succMany` (hypothesis 4, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d276 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany_succ_eq_succ_succMany 4 := fun h => T2.not_inf (@h 0 T2 _ _ ⟨false⟩)

-- `Std.PRange.UpwardEnumerable.succMany_add` (hypothesis 2, dependent: `Std.PRange.LawfulUpwardEnumerable α`): NoneMany (succ? n = some (n+1), succMany? = none) satisfies the other hypotheses, succMany? 0 a = none.
theorem d277 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany_add 2 := fun h => NoneMany.not_lue (@h NoneMany _ _ 0 0 ⟨0⟩)

-- `Std.PRange.UpwardEnumerable.succMany_add` (hypothesis 3, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d278 : ¬ indep0% Std.PRange.UpwardEnumerable.succMany_add 3 := fun h => T2.not_inf (@h T2 _ _ 0 0 ⟨false⟩)

-- `Std.PRange.UpwardEnumerable.lt_succ` (hypothesis 3, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d279 : ¬ indep0% Std.PRange.UpwardEnumerable.lt_succ 3 := fun h => T2.not_inf (@h T2 _ _ ⟨false⟩)

-- `Std.PRange.UpwardEnumerable.succ_le_succ` (hypothesis 3, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d280 : ¬ indep0% Std.PRange.UpwardEnumerable.succ_le_succ 3 := fun h => T2.not_inf (@h T2 _ _ ⟨false⟩ ⟨true⟩ ⟨1, rfl⟩)

-- `Std.PRange.UpwardEnumerable.succ_le_succ_iff` (hypothesis 3, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d281 : ¬ indep0% Std.PRange.UpwardEnumerable.succ_le_succ_iff 3 := fun h => T2.not_inf (@h T2 _ _ _ ⟨false⟩ ⟨true⟩)

-- `Std.PRange.UpwardEnumerable.succ_lt_succ` (hypothesis 3, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d282 : ¬ indep0% Std.PRange.UpwardEnumerable.succ_lt_succ 3 := fun h => T2.not_inf (@h T2 _ _ ⟨false⟩ ⟨true⟩ ⟨0, rfl⟩)

-- `Std.PRange.UpwardEnumerable.succ_lt_succ_iff` (hypothesis 3, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d283 : ¬ indep0% Std.PRange.UpwardEnumerable.succ_lt_succ_iff 3 := fun h => T2.not_inf (@h T2 _ _ _ ⟨false⟩ ⟨true⟩)

-- `Std.PRange.UpwardEnumerable.succ_le_iff` (hypothesis 3, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d284 : ¬ indep0% Std.PRange.UpwardEnumerable.succ_le_iff 3 := fun h => T2.not_inf (@h T2 _ _ ⟨false⟩ ⟨true⟩)

-- `Std.PRange.UpwardEnumerable.lt_succ_iff` (hypothesis 3, dependent: `Std.PRange.InfinitelyUpwardEnumerable α`): T2 (two elements false → true, all lawful) satisfies the other hypotheses, succ? true = none.
theorem d285 : ¬ indep0% Std.PRange.UpwardEnumerable.lt_succ_iff 3 := fun h => T2.not_inf (@h T2 _ _ _ ⟨false⟩ ⟨true⟩)

-- `Std.PRange.UpwardEnumerable.least_le` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerableLeast? α`): T2least (T2 with least? = some true) satisfies the other hypotheses, false is not above true.
theorem d286 : ¬ indep0% Std.PRange.UpwardEnumerable.least_le 3 := fun h => T2least.not_lleast (@h T2least _ _ ⟨false⟩)

-- `Std.PRange.UpwardEnumerable.least?_eq_some` (hypothesis 3, dependent: `Std.PRange.LawfulUpwardEnumerableLeast? α`): T2least (T2 with least? = some true) satisfies the other hypotheses, false is not above true.
theorem d287 : ¬ indep0% Std.PRange.UpwardEnumerable.least?_eq_some 3 := fun h => T2least.not_lleast (@h T2least _ _ ⟨⟨false⟩⟩)

-- `Std.PRange.UpwardEnumerable.least?_eq_some` (hypothesis 4, dependent: `Nonempty α`): EmptyM (empty, least? = none) satisfies LawfulUpwardEnumerableLeast? vacuously.
theorem d288 : ¬ indep0% Std.PRange.UpwardEnumerable.least?_eq_some 4 := fun h => EmptyM.not_nonempty (@h EmptyM _ _ _)

end RangeDepBHand
