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

/-!
Hand pass `Grind` (hand22): 115 unresolved hypotheses of private theorems in `Init.Grind.Ordered.Field` (55),
`Init.Data.Int.Linear` (32), `Init.Grind.Ordered.Linarith` (7), `Init.Grind.Ring.FieldSolver` (7),
`Init.Grind.Module.Envelope` (5), `Init.Grind.Ring.Envelope` (5), `Init.Grind.Order` (3) and
`Init.Grind.Ring.Kronecker` (1).

107 necessary, 8 removable, 0 independent, 0 left unresolved.

Private theorems are named in full (`_private.M.«0».x`) with the elaborators of `runs/hand22/Header.lean`.
Necessary verdicts prove `¬ drop0% T i` (or `¬ indep0% T i` for the dependent `IsLinearOrder`/`IsPreorder`
binders) by applying the hypothetical statement to a model and evaluating with `decide +kernel`; removable
verdicts prove `drop% T i` (or `indep% T i`).

Reusable models (namespace `GrindPrivHand`):
* Copied from `checks/GrindOrdHand.lean`: Int models `IPle`, `ILTpos`, `ILTodd`, `ILTall`, `ILTnn`, `ILT01`,
  `IRev`, `IRevLT`, `IGt` (`IGt.not_preorder`), `IL2`; `NSucc`, `F2T`; Rat fields `RLTge1`, `RLTne`, `RRev`, `RLh`.
* New: `RLTle` (`Rat`, usual `≤`, `<` is `≤`: an `OrderedRing` with `0 < 0`, needed for the `<`-only Field
  lemmas, where `c = 0` counts as positive); `RS` (`Rat`, `≤` and `<` both strict: lawful `<`,
  `RS.not_linear`).
* `F2field` (`Field (Fin 2)`, `2⁻¹ = 0`) and `decInvVarsOk`, copied from `checks/SolverHand.lean`; `NL`
  (`Nat` with `<` always false), copied from `checks/GrindMiscHand.lean`.
* `decOrOver`: `Decidable (Int.Internal.Linear.OrOver n p)`, so the Cooper lemmas evaluate with `decide +kernel`.

Removable (8):
* `k > 0` of `poly_eq_zero_eq_false`: `p.denote = (p.div k).denote * k + cmod c k` holds for every `k`, and
  `cmod c k < 0` forces `p.denote ≠ 0` also for `k = 0` and `k < 0`.
* `d > 0` of `cooper_unsat'_helper`, `d > 1` of `ex_of_dvd` and `d > 1` of `cooper_unsat'`: `%`, `∣` and
  `cdiv · d * d` ignore the sign of `d`, and `d = 0`, `d = ±1` are direct (helpers `cooper_unsat'_helper_all`,
  `ex_of_dvd_all`).
* Dependent, derivable: `Equivalence (r α)` of `rel_rfl` and `helper` in both envelopes (`r_rfl`, `r_sym`,
  `r_trans` hold for every `NatModule`/`Semiring`).

Note: the brief's output name `checks/GrindHand.lean` is taken by an older hand file, so this file is
`checks/GrindPrivHand.lean`. Run with `runs/hand22/lean.sh checks/GrindPrivHand.lean`; generators in
`runs/hand22/scratch_Grind/` (`search.py` for the Field witnesses, `unsat.py` for `cooper_unsat'`).
-/

set_option linter.deprecated false

open Lean.Grind Std
attribute [local instance] Semiring.natCast Ring.intCast

namespace GrindPrivHand

/-! ### Int models -/

/-- `Int` with `≤` = equality plus `1 ≤ 0`; lawful `<`: a preorder, no `OrderedAdd`. -/
def IPle := Int
abbrev IPle.le (a b : Int) : Prop := a = b ∨ (a = 1 ∧ b = 0)
abbrev IPle.lt (a b : Int) : Prop := a = 1 ∧ b = 0
instance : DecidableEq IPle := inferInstanceAs (DecidableEq Int)
instance : CommRing IPle := inferInstanceAs (CommRing Int)
instance : LE IPle := ⟨IPle.le⟩
instance : LT IPle := ⟨IPle.lt⟩
instance : DecidableLE IPle := fun (a b : Int) => inferInstanceAs (Decidable (IPle.le a b))
instance : DecidableLT IPle := fun (a b : Int) => inferInstanceAs (Decidable (IPle.lt a b))
instance : IsPreorder IPle where
  le_refl a := Or.inl rfl
  le_trans a b c (h₁ : IPle.le a b) (h₂ : IPle.le b c) := (by unfold IPle.le at *; omega : IPle.le a c)
instance : LawfulOrderLT IPle where
  lt_iff a b := (by unfold IPle.lt IPle.le; omega : IPle.lt a b ↔ IPle.le a b ∧ ¬ IPle.le b a)

/-- `Int`, usual `≤`, `a < b := a < b ∧ 0 < b`: ordered ring, `<` not lawful. -/
def ILTpos := Int
abbrev ILTpos.lt (a b : Int) : Prop := a < b ∧ 0 < b
instance : DecidableEq ILTpos := inferInstanceAs (DecidableEq Int)
instance : CommRing ILTpos := inferInstanceAs (CommRing Int)
instance : LE ILTpos := inferInstanceAs (LE Int)
instance : LT ILTpos := ⟨ILTpos.lt⟩
instance : DecidableLE ILTpos := inferInstanceAs (DecidableLE Int)
instance : DecidableLT ILTpos := fun (a b : Int) => inferInstanceAs (Decidable (ILTpos.lt a b))
instance : IsLinearOrder ILTpos := inferInstanceAs (IsLinearOrder Int)
instance : OrderedAdd ILTpos := inferInstanceAs (OrderedAdd Int)
instance : OrderedRing ILTpos where
  zero_lt_one := (by decide : ILTpos.lt 0 1)
  mul_lt_mul_of_pos_left {a b c} (h : ILTpos.lt a b) (hc : ILTpos.lt 0 c) :=
    (⟨Int.mul_lt_mul_of_pos_left h.1 hc.1, Int.mul_pos hc.1 h.2⟩ : ILTpos.lt ((c : Int) * a) (c * b))
  mul_lt_mul_of_pos_right {a b c} (h : ILTpos.lt a b) (hc : ILTpos.lt 0 c) :=
    (⟨Int.mul_lt_mul_of_pos_right h.1 hc.1, Int.mul_pos h.2 hc.1⟩ : ILTpos.lt ((a : Int) * c) (b * c))

/-- `Int`, usual `≤`, `a < b := a < b ∧ b - a odd`: ordered ring, `<` not lawful. -/
def ILTodd := Int
abbrev ILTodd.lt (a b : Int) : Prop := a < b ∧ (b - a) % 2 = 1
instance : DecidableEq ILTodd := inferInstanceAs (DecidableEq Int)
instance : CommRing ILTodd := inferInstanceAs (CommRing Int)
instance : LE ILTodd := inferInstanceAs (LE Int)
instance : LT ILTodd := ⟨ILTodd.lt⟩
instance : DecidableLE ILTodd := inferInstanceAs (DecidableLE Int)
instance : DecidableLT ILTodd := fun (a b : Int) => inferInstanceAs (Decidable (ILTodd.lt a b))
instance : IsLinearOrder ILTodd := inferInstanceAs (IsLinearOrder Int)
instance : OrderedAdd ILTodd := inferInstanceAs (OrderedAdd Int)
theorem ILTodd.odd_mul {c d : Int} (hc : c % 2 = 1) (hd : d % 2 = 1) : (c * d) % 2 = 1 := by
  rw [Int.mul_emod, hc, hd]; rfl
theorem ILTodd.mul_left {a b c : Int} (h : ILTodd.lt a b) (hc : ILTodd.lt 0 c) : ILTodd.lt (c * a) (c * b) :=
  ⟨Int.mul_lt_mul_of_pos_left h.1 hc.1,
    by rw [← Int.mul_sub]; exact ILTodd.odd_mul (by have := hc.2; rwa [Int.sub_zero] at this) h.2⟩
theorem ILTodd.mul_right {a b c : Int} (h : ILTodd.lt a b) (hc : ILTodd.lt 0 c) : ILTodd.lt (a * c) (b * c) :=
  ⟨Int.mul_lt_mul_of_pos_right h.1 hc.1,
    by rw [← Int.sub_mul]; exact ILTodd.odd_mul h.2 (by have := hc.2; rwa [Int.sub_zero] at this)⟩
instance : OrderedRing ILTodd where
  zero_lt_one := (by decide : ILTodd.lt 0 1)
  mul_lt_mul_of_pos_left := ILTodd.mul_left
  mul_lt_mul_of_pos_right := ILTodd.mul_right

/-- `Int`, usual `≤`, `<` always true: ordered ring, `<` not lawful. -/
def ILTall := Int
instance : DecidableEq ILTall := inferInstanceAs (DecidableEq Int)
instance : CommRing ILTall := inferInstanceAs (CommRing Int)
instance : LE ILTall := inferInstanceAs (LE Int)
instance : LT ILTall := ⟨fun _ _ => True⟩
instance : DecidableLE ILTall := inferInstanceAs (DecidableLE Int)
instance : DecidableLT ILTall := fun _ _ => instDecidableTrue
instance : IsLinearOrder ILTall := inferInstanceAs (IsLinearOrder Int)
instance : OrderedAdd ILTall := inferInstanceAs (OrderedAdd Int)
instance : OrderedRing ILTall where
  zero_lt_one := trivial
  mul_lt_mul_of_pos_left _ _ := trivial
  mul_lt_mul_of_pos_right _ _ := trivial

/-- `Int`, usual `≤`, `a < b := a < b ∧ 0 ≤ b`: ordered ring, `<` not lawful (`-1 < 0` holds,
`-2 < -1` does not). -/
def ILTnn := Int
abbrev ILTnn.lt (a b : Int) : Prop := a < b ∧ 0 ≤ b
instance : DecidableEq ILTnn := inferInstanceAs (DecidableEq Int)
instance : CommRing ILTnn := inferInstanceAs (CommRing Int)
instance : LE ILTnn := inferInstanceAs (LE Int)
instance : LT ILTnn := ⟨ILTnn.lt⟩
instance : DecidableLE ILTnn := inferInstanceAs (DecidableLE Int)
instance : DecidableLT ILTnn := fun (a b : Int) => inferInstanceAs (Decidable (ILTnn.lt a b))
instance : IsLinearOrder ILTnn := inferInstanceAs (IsLinearOrder Int)
instance : OrderedAdd ILTnn := inferInstanceAs (OrderedAdd Int)
instance : OrderedRing ILTnn where
  zero_lt_one := (by decide : ILTnn.lt 0 1)
  mul_lt_mul_of_pos_left {a b c} (h : ILTnn.lt a b) (hc : ILTnn.lt 0 c) :=
    (⟨Int.mul_lt_mul_of_pos_left h.1 hc.1, Int.mul_nonneg (Int.le_of_lt hc.1) h.2⟩ : ILTnn.lt ((c : Int) * a) (c * b))
  mul_lt_mul_of_pos_right {a b c} (h : ILTnn.lt a b) (hc : ILTnn.lt 0 c) :=
    (⟨Int.mul_lt_mul_of_pos_right h.1 hc.1, Int.mul_nonneg h.2 (Int.le_of_lt hc.1)⟩ : ILTnn.lt ((a : Int) * c) (b * c))

/-- `Int`, usual `≤`, `a < b := a < b ∧ (a = 0 → b = 1)`: the only positive element is `1`, so the
multiplication laws of `OrderedRing` are trivial; `<` not lawful (`-2 < 0` holds, `0 < 4` does not). -/
def ILT01 := Int
abbrev ILT01.lt (a b : Int) : Prop := a < b ∧ (a = 0 → b = 1)
instance : DecidableEq ILT01 := inferInstanceAs (DecidableEq Int)
instance : CommRing ILT01 := inferInstanceAs (CommRing Int)
instance : LE ILT01 := inferInstanceAs (LE Int)
instance : LT ILT01 := ⟨ILT01.lt⟩
instance : DecidableLE ILT01 := inferInstanceAs (DecidableLE Int)
instance : DecidableLT ILT01 := fun (a b : Int) => inferInstanceAs (Decidable (ILT01.lt a b))
instance : IsLinearOrder ILT01 := inferInstanceAs (IsLinearOrder Int)
instance : OrderedAdd ILT01 := inferInstanceAs (OrderedAdd Int)
theorem ILT01.mul_left {a b c : Int} (h : ILT01.lt a b) (hc : ILT01.lt 0 c) : ILT01.lt (c * a) (c * b) := by
  have : c = 1 := hc.2 rfl
  subst this; rw [Int.one_mul, Int.one_mul]; exact h
theorem ILT01.mul_right {a b c : Int} (h : ILT01.lt a b) (hc : ILT01.lt 0 c) : ILT01.lt (a * c) (b * c) := by
  have : c = 1 := hc.2 rfl
  subst this; rw [Int.mul_one, Int.mul_one]; exact h
instance : OrderedRing ILT01 where
  zero_lt_one := (by decide : ILT01.lt 0 1)
  mul_lt_mul_of_pos_left {a b c} (h : ILT01.lt a b) (hc : ILT01.lt 0 c) := ILT01.mul_left h hc
  mul_lt_mul_of_pos_right {a b c} (h : ILT01.lt a b) (hc : ILT01.lt 0 c) := ILT01.mul_right h hc

theorem IRev.add_iff (a b c : Int) : b ≤ a ↔ b + c ≤ a + c := by omega

/-- `Int` with the reversed order (`a ≤ b := b ≤ a`, lawful `<`): linear order, `OrderedAdd`,
no `OrderedRing` (`0 < 1` fails). -/
def IRev := Int
instance : DecidableEq IRev := inferInstanceAs (DecidableEq Int)
instance : CommRing IRev := inferInstanceAs (CommRing Int)
instance : LE IRev := ⟨fun (a b : Int) => b ≤ a⟩
instance : LT IRev := ⟨fun (a b : Int) => b < a⟩
instance : DecidableLE IRev := fun (a b : Int) => inferInstanceAs (Decidable (b ≤ a))
instance : DecidableLT IRev := fun (a b : Int) => inferInstanceAs (Decidable (b < a))
instance : IsLinearOrder IRev where
  le_refl (a : Int) := Int.le_refl a
  le_trans (a b c : Int) h₁ h₂ := Int.le_trans h₂ h₁
  le_antisymm (a b : Int) h₁ h₂ := Int.le_antisymm h₂ h₁
  le_total (a b : Int) := Int.le_total b a
instance : LawfulOrderLT IRev where
  lt_iff (a b : Int) := (by omega : b < a ↔ b ≤ a ∧ ¬ a ≤ b)
instance : OrderedAdd IRev where
  add_le_left_iff {a b} c := IRev.add_iff a b c

/-- `Int` with the reversed `≤` and the usual `<`: linear order, `OrderedRing`, `<` not lawful. -/
def IRevLT := Int
instance : DecidableEq IRevLT := inferInstanceAs (DecidableEq Int)
instance : CommRing IRevLT := inferInstanceAs (CommRing Int)
instance : LE IRevLT := ⟨fun (a b : Int) => b ≤ a⟩
instance : LT IRevLT := ⟨fun (a b : Int) => a < b⟩
instance : DecidableLE IRevLT := fun (a b : Int) => inferInstanceAs (Decidable (b ≤ a))
instance : DecidableLT IRevLT := fun (a b : Int) => inferInstanceAs (Decidable (a < b))
instance : IsLinearOrder IRevLT where
  le_refl (a : Int) := Int.le_refl a
  le_trans (a b c : Int) h₁ h₂ := Int.le_trans h₂ h₁
  le_antisymm (a b : Int) h₁ h₂ := Int.le_antisymm h₂ h₁
  le_total (a b : Int) := Int.le_total b a
instance : OrderedRing IRevLT where
  add_le_left_iff {a b} c := IRev.add_iff a b c
  zero_lt_one := (by decide : (0 : Int) < 1)
  mul_lt_mul_of_pos_left {a b c : Int} (h : a < b) (hc : 0 < c) := (Int.mul_lt_mul_of_pos_left h hc : c * a < c * b)
  mul_lt_mul_of_pos_right {a b c : Int} (h : a < b) (hc : 0 < c) := (Int.mul_lt_mul_of_pos_right h hc : a * c < b * c)

/-- `Int` with `≤` and `<` both `>`: lawful `<`, `≤` not reflexive (no `IsPreorder`). -/
def IGt := Int
instance : DecidableEq IGt := inferInstanceAs (DecidableEq Int)
instance : CommRing IGt := inferInstanceAs (CommRing Int)
instance : LE IGt := ⟨fun (a b : Int) => b < a⟩
instance : LT IGt := ⟨fun (a b : Int) => b < a⟩
instance : DecidableLE IGt := fun (a b : Int) => inferInstanceAs (Decidable (b < a))
instance : DecidableLT IGt := fun (a b : Int) => inferInstanceAs (Decidable (b < a))
instance : LawfulOrderLT IGt where
  lt_iff (a b : Int) := (by omega : b < a ↔ b < a ∧ ¬ a < b)
theorem IGt.not_preorder : ¬ IsPreorder IGt := fun h => Int.lt_irrefl (0 : Int) (h.le_refl (0 : Int))

/-- `Int` with the usual order except that `2` is the least element; lawful `<`: a linear order,
not translation invariant (no `OrderedAdd`). -/
def IL2 := Int
abbrev IL2.le (a b : Int) : Prop := a = 2 ∨ (b ≠ 2 ∧ a ≤ b)
abbrev IL2.lt (a b : Int) : Prop := IL2.le a b ∧ ¬ IL2.le b a
instance : DecidableEq IL2 := inferInstanceAs (DecidableEq Int)
instance : CommRing IL2 := inferInstanceAs (CommRing Int)
instance : LE IL2 := ⟨IL2.le⟩
instance : LT IL2 := ⟨IL2.lt⟩
instance : DecidableLE IL2 := fun (a b : Int) => inferInstanceAs (Decidable (IL2.le a b))
instance : DecidableLT IL2 := fun (a b : Int) => inferInstanceAs (Decidable (IL2.lt a b))
instance : IsLinearOrder IL2 where
  le_refl (a : Int) := (by omega : IL2.le a a)
  le_trans (a b c : Int) (h₁ : IL2.le a b) (h₂ : IL2.le b c) := (by omega : IL2.le a c)
  le_antisymm (a b : Int) (h₁ : IL2.le a b) (h₂ : IL2.le b a) := (by omega : a = b)
  le_total (a b : Int) := (by omega : IL2.le a b ∨ IL2.le b a)
instance : LawfulOrderLT IL2 where
  lt_iff _ _ := Iff.rfl

/-! ### Nat and `Fin 2` models -/

/-- `Nat` with `a ≤ b := a = b ∨ b = a + 1` (reflexive, not transitive) and lawful `<`
(`a < b := b = a + 1`): `0 < 1`, `1 < 2`, but not `0 < 2`. -/
def NSucc := Nat
abbrev NSucc.le (a b : Nat) : Prop := a = b ∨ b = a + 1
abbrev NSucc.lt (a b : Nat) : Prop := b = a + 1
instance : LE NSucc := ⟨NSucc.le⟩
instance : LT NSucc := ⟨NSucc.lt⟩
instance : DecidableLE NSucc := fun (a b : Nat) => inferInstanceAs (Decidable (NSucc.le a b))
instance : DecidableLT NSucc := fun (a b : Nat) => inferInstanceAs (Decidable (NSucc.lt a b))
instance : OfNat NSucc n := ⟨(n : Nat)⟩
instance : LawfulOrderLT NSucc where
  lt_iff (a b : Nat) := (by omega : NSucc.lt a b ↔ NSucc.le a b ∧ ¬ NSucc.le b a)

/-- `Fin 2` with `≤` and `<` always true: preorder, `OrderedRing`, `<` not lawful, characteristic 2. -/
def F2T := Fin 2
instance : DecidableEq F2T := inferInstanceAs (DecidableEq (Fin 2))
instance : CommRing F2T := inferInstanceAs (CommRing (Fin 2))
instance : LE F2T := ⟨fun _ _ => True⟩
instance : LT F2T := ⟨fun _ _ => True⟩
instance : IsPreorder F2T where
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial
instance : OrderedRing F2T where
  add_le_left_iff _ := Iff.rfl
  zero_lt_one := trivial
  mul_lt_mul_of_pos_left _ _ := trivial
  mul_lt_mul_of_pos_right _ _ := trivial
theorem F2T.not_charP0 : ¬ IsCharP F2T 0 := fun h => by
  have := (h.ofNat_ext_iff (x := 2) (y := 0)).mp (by decide)
  simp at this

/-! ### Rat models -/

/-- `Rat`, usual `≤`, `a < b := a + 1 ≤ b`: ordered field, `<` not lawful
(`0 < 2` holds, `0 < 1/2` does not). -/
def RLTge1 := Rat
abbrev RLTge1.lt (a b : Rat) : Prop := a + 1 ≤ b
instance : DecidableEq RLTge1 := inferInstanceAs (DecidableEq Rat)
instance : Field RLTge1 := inferInstanceAs (Field Rat)
instance : LE RLTge1 := inferInstanceAs (LE Rat)
instance : LT RLTge1 := ⟨RLTge1.lt⟩
instance : DecidableLE RLTge1 := inferInstanceAs (DecidableLE Rat)
instance : DecidableLT RLTge1 := fun (a b : Rat) => inferInstanceAs (Decidable (RLTge1.lt a b))
instance : IsLinearOrder RLTge1 := inferInstanceAs (IsLinearOrder Rat)
instance : OrderedAdd RLTge1 := inferInstanceAs (OrderedAdd Rat)
theorem RLTge1.mul_left {a b c : Rat} (h : a + 1 ≤ b) (hc : 0 + 1 ≤ c) : c * a + 1 ≤ c * b := by
  have h1 : c * 1 ≤ c * (b - a) :=
    OrderedRing.mul_le_mul_of_nonneg_left (by grind) (by grind)
  grind
theorem RLTge1.mul_right {a b c : Rat} (h : a + 1 ≤ b) (hc : 0 + 1 ≤ c) : a * c + 1 ≤ b * c := by
  have := RLTge1.mul_left h hc
  grind
instance : OrderedRing RLTge1 where
  zero_lt_one := (by decide +kernel : RLTge1.lt 0 1)
  mul_lt_mul_of_pos_left := RLTge1.mul_left
  mul_lt_mul_of_pos_right := RLTge1.mul_right

/-- `Rat`, usual `≤`, `a < b := a ≠ b`: ordered field (no zero divisors), `<` not lawful. -/
def RLTne := Rat
instance : DecidableEq RLTne := inferInstanceAs (DecidableEq Rat)
instance : Field RLTne := inferInstanceAs (Field Rat)
instance : LE RLTne := inferInstanceAs (LE Rat)
instance : LT RLTne := ⟨fun (a b : Rat) => a ≠ b⟩
instance : DecidableLE RLTne := inferInstanceAs (DecidableLE Rat)
instance : DecidableLT RLTne := fun (a b : Rat) => inferInstanceAs (Decidable (a ≠ b))
instance : IsLinearOrder RLTne := inferInstanceAs (IsLinearOrder Rat)
instance : OrderedAdd RLTne := inferInstanceAs (OrderedAdd Rat)
instance : OrderedRing RLTne where
  zero_lt_one := (by decide +kernel : (0 : Rat) ≠ 1)
  mul_lt_mul_of_pos_left {a b c : Rat} (h : a ≠ b) (hc : 0 ≠ c) := (by grind : c * a ≠ c * b)
  mul_lt_mul_of_pos_right {a b c : Rat} (h : a ≠ b) (hc : 0 ≠ c) := (by grind : a * c ≠ b * c)

/-- `Rat` with the reversed order (lawful `<`): linear order, `OrderedAdd`, no `OrderedRing`. -/
def RRev := Rat
instance : DecidableEq RRev := inferInstanceAs (DecidableEq Rat)
instance : Field RRev := inferInstanceAs (Field Rat)
instance : LE RRev := ⟨fun (a b : Rat) => b ≤ a⟩
instance : LT RRev := ⟨fun (a b : Rat) => b < a⟩
instance : DecidableLE RRev := fun (a b : Rat) => inferInstanceAs (Decidable (b ≤ a))
instance : DecidableLT RRev := fun (a b : Rat) => inferInstanceAs (Decidable (b < a))
instance : IsLinearOrder RRev where
  le_refl (a : Rat) := Std.le_refl a
  le_trans (a b c : Rat) h₁ h₂ := Std.le_trans (α := Rat) h₂ h₁
  le_antisymm (a b : Rat) h₁ h₂ := Std.le_antisymm (α := Rat) h₂ h₁
  le_total (a b : Rat) := Std.le_total (α := Rat) (a := b) (b := a)
instance : LawfulOrderLT RRev where
  lt_iff (a b : Rat) := LawfulOrderLT.lt_iff (α := Rat) b a
instance : OrderedAdd RRev where
  add_le_left_iff {a b : Rat} c := OrderedAdd.add_le_left_iff (M := Rat) c

/-- `Rat` with the usual order except that `1/2` is the least element; lawful `<`: a linear order,
not translation invariant. -/
def RLh := Rat
abbrev RLh.le (a b : Rat) : Prop := a = 2⁻¹ ∨ (b ≠ 2⁻¹ ∧ a ≤ b)
abbrev RLh.lt (a b : Rat) : Prop := RLh.le a b ∧ ¬ RLh.le b a
instance : DecidableEq RLh := inferInstanceAs (DecidableEq Rat)
instance : Field RLh := inferInstanceAs (Field Rat)
instance : LE RLh := ⟨RLh.le⟩
instance : LT RLh := ⟨RLh.lt⟩
instance : DecidableLE RLh := fun (a b : Rat) => inferInstanceAs (Decidable (RLh.le a b))
instance : DecidableLT RLh := fun (a b : Rat) => inferInstanceAs (Decidable (RLh.lt a b))
instance : IsLinearOrder RLh where
  le_refl (a : Rat) := (by grind : RLh.le a a)
  le_trans (a b c : Rat) (h₁ : RLh.le a b) (h₂ : RLh.le b c) := (by grind : RLh.le a c)
  le_antisymm (a b : Rat) (h₁ : RLh.le a b) (h₂ : RLh.le b a) := (by grind : a = b)
  le_total (a b : Rat) := (by grind : RLh.le a b ∨ RLh.le b a)
instance : LawfulOrderLT RLh where
  lt_iff _ _ := Iff.rfl

/-- `Rat`, usual `≤`, `<` is also `≤`: ordered field (`OrderedRing` holds for `≤`), `<` not lawful (`0 < 0`). -/
def RLTle := Rat
instance : DecidableEq RLTle := inferInstanceAs (DecidableEq Rat)
instance : Field RLTle := inferInstanceAs (Field Rat)
instance : LE RLTle := inferInstanceAs (LE Rat)
instance : LT RLTle := ⟨fun (a b : Rat) => a ≤ b⟩
instance : DecidableLE RLTle := inferInstanceAs (DecidableLE Rat)
instance : DecidableLT RLTle := fun (a b : Rat) => inferInstanceAs (Decidable (a ≤ b))
instance : IsLinearOrder RLTle := inferInstanceAs (IsLinearOrder Rat)
instance : OrderedAdd RLTle := inferInstanceAs (OrderedAdd Rat)
instance : OrderedRing RLTle where
  zero_lt_one := (by decide +kernel : (0 : Rat) ≤ 1)
  mul_lt_mul_of_pos_left {a b c : Rat} (h : a ≤ b) (hc : 0 ≤ c) := OrderedRing.mul_le_mul_of_nonneg_left h hc
  mul_lt_mul_of_pos_right {a b c : Rat} (h : a ≤ b) (hc : 0 ≤ c) := OrderedRing.mul_le_mul_of_nonneg_right h hc

/-- `Rat` with `≤` and `<` both the strict order: lawful `<`, `≤` not reflexive (no `IsLinearOrder`). -/
def RS := Rat
instance : DecidableEq RS := inferInstanceAs (DecidableEq Rat)
instance : Field RS := inferInstanceAs (Field Rat)
instance : LE RS := ⟨fun (a b : Rat) => a < b⟩
instance : LT RS := ⟨fun (a b : Rat) => a < b⟩
instance : DecidableLE RS := fun (a b : Rat) => inferInstanceAs (Decidable (a < b))
instance : DecidableLT RS := fun (a b : Rat) => inferInstanceAs (Decidable (a < b))
instance : LawfulOrderLT RS where
  lt_iff (a b : Rat) := ⟨fun h => ⟨h, fun h' => Std.lt_irrefl (α := Rat) (Std.lt_trans h h')⟩, fun h => h.1⟩
theorem RS.not_linear : ¬ IsLinearOrder RS := fun h => Std.lt_irrefl (α := Rat) (h.le_refl (0 : Rat))

end GrindPrivHand
open GrindPrivHand


namespace GrindPrivHand

/-- The field with two elements (`inv := id`), of characteristic `2` (copied from `SolverHand.F2field`). -/
instance F2field : Field (Fin 2) where
  inv := id
  div := (· * ·)
  zpow := ⟨fun a n => a ^ n.natAbs⟩
  div_eq_mul_inv := by decide
  zero_ne_one := by decide
  inv_zero := by decide
  mul_inv_cancel := by decide
  zpow_zero a := Semiring.pow_zero a
  zpow_succ a n := Semiring.pow_succ a n
  zpow_neg a n := by show a ^ (-n).natAbs = a ^ n.natAbs; rw [Int.natAbs_neg]

/-- Decides `InvVars.ok` (copied from `SolverHand.decInvVarsOk`). -/
instance decInvVarsOk {α : Type} [Field α] [DecidableEq α] (ctx : CommRing.Context α) (invs : CommRing.InvVars) :
    Decidable (invs.ok ctx) :=
  inferInstanceAs (Decidable (invs.denoteVars ctx = invs.denoteInvs))

/-- `Nat` with its semiring and order, but `<` is always false (copied from `GrindMiscHand.NL`). -/
def NL := Nat
instance : Semiring NL := inferInstanceAs (Semiring Nat)
instance : LE NL := inferInstanceAs (LE Nat)
instance : LT NL := ⟨fun _ _ => False⟩
instance : Std.IsPreorder NL := inferInstanceAs (Std.IsPreorder Nat)
instance : OrderedAdd NL := inferInstanceAs (OrderedAdd Nat)

/-- `OrOver n p` is decidable for decidable `p` (it unfolds to a finite disjunction). -/
instance decOrOver : (n : Nat) → (p : Nat → Prop) → [DecidablePred p] → Decidable (Int.Internal.Linear.OrOver n p)
  | 0, _, _ => isFalse id
  | n + 1, p, _ => have := decOrOver n p; inferInstanceAs (Decidable (p n ∨ Int.Internal.Linear.OrOver n p))

end GrindPrivHand
open GrindPrivHand


/-! ### `Init.Data.Int.Linear` -/

-- `Int.Internal.Linear.cooper_dvd_left_core` (hypothesis 8): a = 0, b = d = 1, the rest 0: the bound lcm 0 _ is 0, so OrOver 0 _ = False.
theorem IntLinear_cooper_dvd_left_core_h8 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_dvd_left_core 8 :=
  fun h => by
    have := h (a := 0) (b := 1) (c := 0) (d := 1) (s := 0) (p := 0) (q := 0) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_dvd_left_core` (hypothesis 9): a = b = -1, d = 1, q = x = 1: OrOver 1 needs b*p + (-a)*q = 1 ≤ 0.
theorem IntLinear_cooper_dvd_left_core_h9 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_dvd_left_core 9 :=
  fun h => by
    have := h (a := -1) (b := -1) (c := 0) (d := 1) (s := 0) (p := 0) (q := 1) (x := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_dvd_left_core` (hypothesis 10): d = 0 (0 ∣ 0 holds): the bound lcm (-1) 0 is 0.
theorem IntLinear_cooper_dvd_left_core_h10 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_dvd_left_core 10 :=
  fun h => by
    have := h (a := -1) (b := 1) (c := 0) (d := 0) (s := 0) (p := 0) (q := 0) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_dvd_left_core` (hypothesis 11): a = -1, b = d = p = 1: OrOver 1 needs p + q = 1 ≤ 0.
theorem IntLinear_cooper_dvd_left_core_h11 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_dvd_left_core 11 :=
  fun h => by
    have := h (a := -1) (b := 1) (c := 0) (d := 1) (s := 0) (p := 1) (q := 0) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_dvd_left_core` (hypothesis 12): a = -1, b = d = q = 1: OrOver 1 needs p + q = 1 ≤ 0.
theorem IntLinear_cooper_dvd_left_core_h12 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_dvd_left_core 12 :=
  fun h => by
    have := h (a := -1) (b := 1) (c := 0) (d := 1) (s := 0) (p := 0) (q := 1) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_dvd_left_core` (hypothesis 13): a = -1, b = c = s = 1, d = 2 (2 ∤ 1): for k = 0 the divisibility 2 ∣ 1 fails, for k = 1 the bound 1 ≤ 0.
theorem IntLinear_cooper_dvd_left_core_h13 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_dvd_left_core 13 :=
  fun h => by
    have := h (a := -1) (b := 1) (c := 1) (d := 2) (s := 1) (p := 0) (q := 0) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_dvd_right_core` (hypothesis 8): a = b = d = p = 1, x = -5: OrOver 1 needs b*p - a*q = 1 ≤ 0.
theorem IntLinear_cooper_dvd_right_core_h8 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_dvd_right_core 8 :=
  fun h => by
    have := h (a := 1) (b := 1) (c := 0) (d := 1) (s := 0) (p := 1) (q := 0) (x := -5) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_dvd_right_core` (hypothesis 9): b = 0: the bound lcm 0 _ is 0.
theorem IntLinear_cooper_dvd_right_core_h9 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_dvd_right_core 9 :=
  fun h => by
    have := h (a := -1) (b := 0) (c := 0) (d := 1) (s := 0) (p := 0) (q := 0) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_dvd_right_core` (hypothesis 10): d = 0: the bound lcm 1 0 is 0.
theorem IntLinear_cooper_dvd_right_core_h10 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_dvd_right_core 10 :=
  fun h => by
    have := h (a := -1) (b := 1) (c := 0) (d := 0) (s := 0) (p := 0) (q := 0) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_dvd_right_core` (hypothesis 11): a = -1, b = d = p = 1: OrOver 1 needs p + q = 1 ≤ 0.
theorem IntLinear_cooper_dvd_right_core_h11 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_dvd_right_core 11 :=
  fun h => by
    have := h (a := -1) (b := 1) (c := 0) (d := 1) (s := 0) (p := 1) (q := 0) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_dvd_right_core` (hypothesis 12): a = -1, b = d = q = 1: OrOver 1 needs p + q = 1 ≤ 0.
theorem IntLinear_cooper_dvd_right_core_h12 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_dvd_right_core 12 :=
  fun h => by
    have := h (a := -1) (b := 1) (c := 0) (d := 1) (s := 0) (p := 0) (q := 1) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_dvd_right_core` (hypothesis 13): a = -1, b = c = s = 1, d = 2: k = 0 needs 2 ∣ 1, k = 1 needs 1 ≤ 0.
theorem IntLinear_cooper_dvd_right_core_h13 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_dvd_right_core 13 :=
  fun h => by
    have := h (a := -1) (b := 1) (c := 1) (d := 2) (s := 1) (p := 0) (q := 0) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_left_core` (hypothesis 5): a = 0: OrOver 0 _ = False.
theorem IntLinear_cooper_left_core_h5 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_left_core 5 :=
  fun h => by
    have := h (a := 0) (b := 1) (p := 0) (q := 0) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_left_core` (hypothesis 6): a = b = -1, q = x = 1: OrOver 1 needs b*p + (-a)*q = 1 ≤ 0.
theorem IntLinear_cooper_left_core_h6 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_left_core 6 :=
  fun h => by
    have := h (a := -1) (b := -1) (p := 0) (q := 1) (x := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_left_core` (hypothesis 7): a = -1, b = p = 1: OrOver 1 needs p + q = 1 ≤ 0.
theorem IntLinear_cooper_left_core_h7 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_left_core 7 :=
  fun h => by
    have := h (a := -1) (b := 1) (p := 1) (q := 0) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_left_core` (hypothesis 8): a = -1, b = q = 1: OrOver 1 needs p + q = 1 ≤ 0.
theorem IntLinear_cooper_left_core_h8 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_left_core 8 :=
  fun h => by
    have := h (a := -1) (b := 1) (p := 0) (q := 1) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_right_core` (hypothesis 5): a = b = p = 1, x = -5: OrOver 1 needs b*p - a*q = 1 ≤ 0.
theorem IntLinear_cooper_right_core_h5 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_right_core 5 :=
  fun h => by
    have := h (a := 1) (b := 1) (p := 1) (q := 0) (x := -5) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_right_core` (hypothesis 6): b = 0: OrOver 0 _ = False.
theorem IntLinear_cooper_right_core_h6 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_right_core 6 :=
  fun h => by
    have := h (a := -1) (b := 0) (p := 0) (q := 0) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_right_core` (hypothesis 7): a = -1, b = p = 1: OrOver 1 needs p + q = 1 ≤ 0.
theorem IntLinear_cooper_right_core_h7 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_right_core 7 :=
  fun h => by
    have := h (a := -1) (b := 1) (p := 1) (q := 0) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_right_core` (hypothesis 8): a = -1, b = q = 1: OrOver 1 needs p + q = 1 ≤ 0.
theorem IntLinear_cooper_right_core_h8 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_right_core 8 :=
  fun h => by
    have := h (a := -1) (b := 1) (p := 0) (q := 1) (x := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    revert this; decide +kernel

-- `Int.Internal.Linear.cooper_unsat'` (hypothesis 9): a = c = x = -4, b = d = 3, e = -2, α = β = -1: all other premises hold, 3 ∤ 14.
theorem IntLinear_cooper_unsat_p_h9 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_unsat' 9 :=
  fun h => h (a := -4) (c := -4) (b := 3) (d := 3) (e := -2) (α := -1) (β := -1) (x := -4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- `Int.Internal.Linear.cooper_unsat'` (hypothesis 10): a = c = e = x = -4, b = d = 3, α = -2, β = -4: all other premises hold, α*c + β*d = -4.
theorem IntLinear_cooper_unsat_p_h10 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_unsat' 10 :=
  fun h => h (a := -4) (c := -4) (b := 3) (d := 3) (e := -4) (α := -2) (β := -4) (x := -4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- `Int.Internal.Linear.cooper_unsat'` (hypothesis 11): a = -3, c = e = x = -4, b = 2, d = 3, α = β = -1: all other premises hold, -x + a = 1 > 0.
theorem IntLinear_cooper_unsat_p_h11 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_unsat' 11 :=
  fun h => h (a := -3) (c := -4) (b := 2) (d := 3) (e := -4) (α := -1) (β := -1) (x := -4) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- `Int.Internal.Linear.cooper_unsat'` (hypothesis 12): a = c = -4, b = d = 3, e = x = -2, α = β = -1: all other premises hold, x + b = 1 > 0.
theorem IntLinear_cooper_unsat_p_h12 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_unsat' 12 :=
  fun h => h (a := -4) (c := -4) (b := 3) (d := 3) (e := -2) (α := -1) (β := -1) (x := -2) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- `Int.Internal.Linear.orOver_of_exists` (hypothesis 2): n = 0: OrOver 0 _ = False.
theorem IntLinear_orOver_of_exists_h2 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.orOver_of_exists 2 :=
  fun h => h (n := 0) (p := fun _ => True)

-- `Int.Internal.Linear.orOver_of_p` (hypothesis 3): i = n = 0, p true: OrOver 0 _ = False.
theorem IntLinear_orOver_of_p_h3 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.orOver_of_p 3 :=
  fun h => h (i := 0) (n := 0) (p := fun _ => True) trivial

-- `Int.Internal.Linear.orOver_of_p` (hypothesis 4): i = 0, n = 1, p false: OrOver 1 _ = False ∨ False.
theorem IntLinear_orOver_of_p_h4 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.orOver_of_p 4 :=
  fun h => by
    have := h (i := 0) (n := 1) (p := fun _ => False) (by decide)
    revert this; decide +kernel

-- `Int.Internal.Linear.poly_eq_zero_eq_false` (hypothesis 3): p = x₀ - 1, k = 2, x₀ = 1: cmod (-1) 2 = -1 < 0 but x₀ - 1 = 0 (the coefficient 1 is not divisible by 2).
theorem IntLinear_poly_eq_zero_eq_false_h3 : ¬ drop0% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.poly_eq_zero_eq_false 3 :=
  fun h => by
    have := h (.leaf 1) (p := .add 1 0 (.num (-1))) (k := 2) (by decide +kernel) (by decide +kernel)
    exact cast this (by decide +kernel)

-- `Int.Internal.Linear.poly_eq_zero_eq_false` (hypothesis 4): removable. For every k,
-- p.denote = (p.div k).denote * k + cmod c k (Poly.denote_div_eq_of_divCoeffs has no sign condition);
-- k = 0 gives p.denote = cmod c 0 < 0, and k < 0 gives k < cmod c k < 0, so p.denote ≠ 0 by the private `contra` at -k.
theorem IntLinear_poly_eq_zero_eq_false_h4 : drop% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.poly_eq_zero_eq_false 4 := by
  intro ctx p k h₁ h₃
  have e := Int.Internal.Linear.Poly.denote_div_eq_of_divCoeffs ctx p k h₁
  rcases Int.lt_trichotomy k 0 with hk | rfl | hk
  · have hm := Int.emod_lt_of_neg (-p.getConst) hk
    have hlt : k < Int.Internal.Linear.cmod p.getConst k := by
      unfold Int.Internal.Linear.cmod; omega
    apply eq_false; intro hd; rw [hd] at e
    exact (priv% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.contra)
      (k := -k) (a := -((p.div k).denote ctx)) (b := Int.Internal.Linear.cmod p.getConst k)
      (by omega) (by omega) h₃ (by rw [Int.neg_mul_neg]; exact e)
  · apply eq_false; intro hd; rw [hd, Int.mul_zero, Int.zero_add] at e; omega
  · exact (priv% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.poly_eq_zero_eq_false) ctx h₁ hk h₃

/-- Helper: `cooper_unsat'_helper` without `d > 0` (a negative `d` acts as `-d`, and `d = 0` forces `x = c`). -/
theorem cooper_unsat'_helper_all {a b d c k x : Int} (h₁ : x = k * d + c) (h₂ : a ≤ x) (h₃ : x ≤ b) :
    ¬ b < Int.Internal.Linear.cdiv (a - c) d * d + c := by
  rcases Int.lt_trichotomy d 0 with hd | rfl | hd
  · have := (priv% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_unsat'_helper)
      (d := -d) (k := -k) (by omega) (show x = (-k) * (-d) + c by rw [Int.neg_mul_neg]; exact h₁) h₂ h₃
    simpa only [Int.Internal.Linear.cdiv, Int.ediv_neg, Int.neg_neg, Int.mul_neg, Int.neg_mul] using this
  · simp only [Int.mul_zero, Int.zero_add] at h₁
    simp only [Int.mul_zero, Int.zero_add]; omega
  · exact (priv% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_unsat'_helper) hd h₁ h₂ h₃

-- `Int.Internal.Linear.cooper_unsat'_helper` (hypothesis 6): removable. cdiv y (-d) * (-d) = cdiv y d * d, so a
-- negative d is the case -d; for d = 0, x = c ≤ b and the bound is c.
theorem IntLinear_cooper_unsat'_helper_h6 : drop% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_unsat'_helper 6 :=
  fun h₁ h₂ h₃ => cooper_unsat'_helper_all h₁ h₂ h₃

/-- Helper: `ex_of_dvd` without `d > 1`. -/
theorem ex_of_dvd_all {α β a b d x : Int} (h₁ : d ∣ a*x + b) (h₂ : α * a + β * d = 1) :
    ∃ k, x = k * d + (- α * b) % d := by
  rcases Int.lt_trichotomy d 1 with hd | rfl | hd
  · rcases Int.lt_trichotomy d (-1) with hd' | rfl | hd'
    · obtain ⟨k, hk⟩ := (priv% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.ex_of_dvd)
        (α := α) (β := -β) (d := -d) (by omega) (Int.neg_dvd.mpr h₁) (by rw [Int.neg_mul_neg]; exact h₂)
      refine ⟨-k, ?_⟩
      rw [Int.emod_neg] at hk; simpa only [Int.mul_neg, Int.neg_mul] using hk
    · exact ⟨-x, by rw [Int.emod_neg, Int.emod_one]; simp⟩
    · have hd0 : d = 0 := by omega
      subst hd0
      have hb : b = -(a * x) := by have := Int.zero_dvd.mp h₁; omega
      have hα : α * a = 1 := by simpa using h₂
      refine ⟨0, ?_⟩
      rw [Int.emod_zero, hb, Int.zero_mul, Int.zero_add, Int.neg_mul, Int.mul_neg, Int.neg_neg, ← Int.mul_assoc, hα, Int.one_mul]
  · exact ⟨x, by simp⟩
  · exact (priv% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.ex_of_dvd) hd h₁ h₂

-- `Int.Internal.Linear.ex_of_dvd` (hypothesis 6): removable. d = ±1: the remainder is 0; d = 0: a*x + b = 0 and
-- α*a = 1 give x = -α*b; d < -1 is the case -d (with β ↦ -β, as % and ∣ ignore the sign of d).
theorem IntLinear_ex_of_dvd_h6 : drop% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.ex_of_dvd 6 :=
  fun h₁ h₂ => ex_of_dvd_all h₁ h₂

-- `Int.Internal.Linear.cooper_unsat'` (hypothesis 8): removable. The library proof uses d > 1 only through
-- ex_of_dvd and cooper_unsat'_helper, both of which hold for every d (see the two rows above).
theorem IntLinear_cooper_unsat'_h8 : drop% _private.Init.Data.Int.Linear.«0».Int.Internal.Linear.cooper_unsat' 8 := by
  intro a c b d e α β x h₂ h₃ h₄ h₅ h₆
  obtain ⟨k, h⟩ := ex_of_dvd_all h₂ h₃
  exact cooper_unsat'_helper_all (b := -b) h (by omega) (by omega) h₆

/-! ### `Init.Grind.Ordered.Linarith`, `Init.Grind.Order` -/

-- `Lean.Grind.Linarith.le_add_le` (hypothesis 4): IL2 (2 least): 2 ≤ 0 twice, but not 4 ≤ 0.
theorem Linarith_le_add_le_h4 : ¬ drop0% _private.Init.Grind.Ordered.Linarith.«0».Lean.Grind.Linarith.le_add_le 4 :=
  fun h => absurd (h (α := IL2) (a := 2) (b := 2) (by decide) (by decide)) (by decide)

-- `Lean.Grind.Linarith.le_add_lt` (hypothesis 4): ILTodd (b - a odd positive): -1 ≤ 0, -1 < 0, but not -2 < 0.
theorem Linarith_le_add_lt_h4 : ¬ drop0% _private.Init.Grind.Ordered.Linarith.«0».Lean.Grind.Linarith.le_add_lt 4 :=
  fun h => absurd (h (α := ILTodd) (a := -1) (b := -1) (by decide) (by decide)) (by decide)

-- `Lean.Grind.Linarith.le_add_lt` (hypothesis 5): IGt (≤ and < both >): a = b = 1 satisfy 1 ≤ 0 and 1 < 0, ≤ not reflexive.
theorem Linarith_le_add_lt_h5 : ¬ indep0% _private.Init.Grind.Ordered.Linarith.«0».Lean.Grind.Linarith.le_add_lt 5 :=
  fun h => IGt.not_preorder (h (α := IGt) (a := 1) (b := 1) (by decide) (by decide))

-- `Lean.Grind.Linarith.le_add_lt` (hypothesis 6): IL2: 2 ≤ 0, -1 < 0, but not 1 < 0.
theorem Linarith_le_add_lt_h6 : ¬ drop0% _private.Init.Grind.Ordered.Linarith.«0».Lean.Grind.Linarith.le_add_lt 6 :=
  fun h => absurd (h (α := IL2) (a := 2) (b := -1) (by decide) (by decide)) (by decide)

-- `Lean.Grind.Linarith.lt_add_lt` (hypothesis 4): ILTodd: -1 < 0 twice, but not -2 < 0.
theorem Linarith_lt_add_lt_h4 : ¬ drop0% _private.Init.Grind.Ordered.Linarith.«0».Lean.Grind.Linarith.lt_add_lt 4 :=
  fun h => absurd (h (α := ILTodd) (a := -1) (b := -1) (by decide) (by decide)) (by decide)

-- `Lean.Grind.Linarith.lt_add_lt` (hypothesis 5): IGt: a = b = 1 satisfy 1 < 0, ≤ not reflexive.
theorem Linarith_lt_add_lt_h5 : ¬ indep0% _private.Init.Grind.Ordered.Linarith.«0».Lean.Grind.Linarith.lt_add_lt 5 :=
  fun h => IGt.not_preorder (h (α := IGt) (a := 1) (b := 1) (by decide) (by decide))

-- `Lean.Grind.Linarith.lt_add_lt` (hypothesis 6): IL2: 2 < 0, -1 < 0, but not 1 < 0.
theorem Linarith_lt_add_lt_h6 : ¬ drop0% _private.Init.Grind.Ordered.Linarith.«0».Lean.Grind.Linarith.lt_add_lt 6 :=
  fun h => absurd (h (α := IL2) (a := 2) (b := -1) (by decide) (by decide)) (by decide)

-- `Lean.Grind.Order.add_lt_add_of_le_of_lt` (hypothesis 3): ILTodd: 0 ≤ 1, 0 < 1, but not 0 < 2.
theorem Order_add_lt_add_of_le_of_lt_h3 : ¬ drop0% _private.Init.Grind.Order.«0».Lean.Grind.Order.add_lt_add_of_le_of_lt 3 :=
  fun h => absurd (h (α := ILTodd) (a := 0) (b := 1) (c := 0) (d := 1) (by decide) (by decide)) (by decide)

-- `Lean.Grind.Order.add_lt_add_of_le_of_lt` (hypothesis 4): IGt: 1 ≤ 0 and 1 < 0 hold, ≤ not reflexive.
theorem Order_add_lt_add_of_le_of_lt_h4 : ¬ indep0% _private.Init.Grind.Order.«0».Lean.Grind.Order.add_lt_add_of_le_of_lt 4 :=
  fun h => IGt.not_preorder (h (α := IGt) (a := 1) (b := 0) (c := 1) (d := 0) (by decide) (by decide))

-- `Lean.Grind.Order.add_lt_add_of_le_of_lt` (hypothesis 6): IPle (1 ≤ 0, 1 < 0 only): not 2 < 0.
theorem Order_add_lt_add_of_le_of_lt_h6 : ¬ drop0% _private.Init.Grind.Order.«0».Lean.Grind.Order.add_lt_add_of_le_of_lt 6 :=
  fun h => absurd (h (α := IPle) (a := 1) (b := 0) (c := 1) (d := 0) (by decide) (by decide)) (by decide)

/-! ### `Init.Grind.Ring.FieldSolver`, `Init.Grind.Ring.Kronecker` -/

-- `Lean.Grind.CommRing.sub_neg_iff` (hypothesis 4): ILTpos (a < b ∧ 0 < b): 0 < 1 but not -1 < 0.
theorem CommRing_sub_neg_iff_h4 : ¬ drop0% _private.Init.Grind.Ring.FieldSolver.«0».Lean.Grind.CommRing.sub_neg_iff 4 :=
  fun h => absurd (h (α := ILTpos) (a := 0) (b := 1)) (by decide)

-- `Lean.Grind.CommRing.sub_neg_iff'` (hypothesis 4): ILTpos: 0 < 1 but not -1 < 0.
theorem CommRing_sub_neg_iff'_h4 : ¬ drop0% _private.Init.Grind.Ring.Kronecker.«0».Lean.Grind.CommRing.sub_neg_iff' 4 :=
  fun h => absurd (h (α := ILTpos) (a := 0) (b := 1)) (by decide)

-- `Lean.Grind.CommRing.mul_inv_neg_iff` (hypothesis 4): RLTge1 (a < b iff a + 1 ≤ b), d = 2: -3/2 < 0 but not -3/4 < 0.
theorem CommRing_mul_inv_neg_iff_h4 : ¬ drop0% _private.Init.Grind.Ring.FieldSolver.«0».Lean.Grind.CommRing.mul_inv_neg_iff 4 :=
  fun h => absurd (h (α := RLTge1) (a := -3/2) (d := 2) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.CommRing.mul_inv_neg_iff` (hypothesis 6): RRev (reversed order), d = -1 positive: the sides differ at a = 1.
theorem CommRing_mul_inv_neg_iff_h6 : ¬ drop0% _private.Init.Grind.Ring.FieldSolver.«0».Lean.Grind.CommRing.mul_inv_neg_iff 6 :=
  fun h => absurd (h (α := RRev) (a := 1) (d := -1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.CommRing.mul_inv_neg_iff` (hypothesis 9): Rat, d = -1, a = 1: -1 < 0 but not 1 < 0.
theorem CommRing_mul_inv_neg_iff_h9 : ¬ drop0% _private.Init.Grind.Ring.FieldSolver.«0».Lean.Grind.CommRing.mul_inv_neg_iff 9 :=
  fun h => absurd (h (α := Rat) (a := 1) (d := -1)) (by decide +kernel)

-- `Lean.Grind.CommRing.mul_inv_nonpos_iff` (hypothesis 4): RLTne (< is ≠), d = -1: -1 ≤ 0 but not 1 ≤ 0.
theorem CommRing_mul_inv_nonpos_iff_h4 : ¬ drop0% _private.Init.Grind.Ring.FieldSolver.«0».Lean.Grind.CommRing.mul_inv_nonpos_iff 4 :=
  fun h => absurd (h (α := RLTne) (a := 1) (d := -1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.CommRing.mul_inv_nonpos_iff` (hypothesis 6): RRev, d = -1 positive: the sides differ at a = 1.
theorem CommRing_mul_inv_nonpos_iff_h6 : ¬ drop0% _private.Init.Grind.Ring.FieldSolver.«0».Lean.Grind.CommRing.mul_inv_nonpos_iff 6 :=
  fun h => absurd (h (α := RRev) (a := 1) (d := -1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.CommRing.denote_sub_of_normQ_cert` (hypothesis 2): Fin 2 (2⁻¹ = 0), table [(0, 2)] with x₀ = 0:
-- 2·x₀ - 1 normalizes to 0 over ℚ (lhs' = rhs' = 0), but 2·0 - 1 = 1 ≠ 0 * d⁻¹ in Fin 2.
theorem CommRing_denote_sub_of_normQ_cert_h2 : ¬ drop0% _private.Init.Grind.Ring.FieldSolver.«0».Lean.Grind.CommRing.denote_sub_of_normQ_cert 2 :=
  fun h => by
    obtain ⟨d, -, hd⟩ := h (α := Fin 2) (.leaf 0) false [(0, 2)] (by decide +kernel) [] trivial
      (.mul (.num 2) (.var 0)) (.num 1) (.num 0) (.num 0) (by decide +kernel)
    have e : CommRing.Expr.denote (.leaf (0 : Fin 2)) (.num 0) - CommRing.Expr.denote (.leaf (0 : Fin 2)) (.num 0) = 0 := by
      decide +kernel
    rw [e, Semiring.zero_mul] at hd
    exact absurd hd (by decide +kernel)

/-! ### `Init.Grind.Module.Envelope`, `Init.Grind.Ring.Envelope` -/

-- `Lean.Grind.IntModule.OfNatModule.rel_rfl` (hypothesis 2): removable (derivable). `r α` is an equivalence for
-- every `NatModule` (`r_rfl`, `r_sym`, `r_trans`).
theorem OfNatModule_rel_rfl_h2 : indep% _private.Init.Grind.Module.Envelope.«0».Lean.Grind.IntModule.OfNatModule.rel_rfl 2 := by
  intros
  exact ⟨IntModule.OfNatModule.r_rfl, IntModule.OfNatModule.r_sym, IntModule.OfNatModule.r_trans⟩

-- `Lean.Grind.IntModule.OfNatModule.helper` (hypothesis 2): removable (derivable), as for rel_rfl.
theorem OfNatModule_helper_h2 : indep% _private.Init.Grind.Module.Envelope.«0».Lean.Grind.IntModule.OfNatModule.helper 2 := by
  intros
  exact ⟨IntModule.OfNatModule.r_rfl, IntModule.OfNatModule.r_sym, IntModule.OfNatModule.r_trans⟩

-- `Lean.Grind.IntModule.OfNatModule.helper` (hypothesis 5): Nat, q₁ = mk (0,0), q₂ = mk (1,0): rel needs 0 + k = 1 + k.
theorem OfNatModule_helper_h5 : ¬ drop0% _private.Init.Grind.Module.Envelope.«0».Lean.Grind.IntModule.OfNatModule.helper 5 :=
  fun h => by
    obtain ⟨k, hk⟩ := h (α := Nat) ⟨IntModule.OfNatModule.r_rfl, IntModule.OfNatModule.r_sym, IntModule.OfNatModule.r_trans⟩
      (IntModule.OfNatModule.Q.mk (0, 0)) (IntModule.OfNatModule.Q.mk (1, 0))
    change 0 + 0 + k = 0 + 1 + k at hk; omega

-- `Lean.Grind.IntModule.OfNatModule.mk_lt_mk` (hypothesis 4): NL (< always false): mk (0,0) < mk (1,0) in Q but not 0 < 1.
theorem OfNatModule_mk_lt_mk_h4 : ¬ drop0% _private.Init.Grind.Module.Envelope.«0».Lean.Grind.IntModule.OfNatModule.mk_lt_mk 4 :=
  fun h => (h (α := NL) (a₁ := (0 : Nat)) (a₂ := (0 : Nat)) (b₁ := (1 : Nat)) (b₂ := (0 : Nat))).mp
    ⟨(by decide : (0 : Nat) + 0 ≤ 0 + 1), (by decide : ¬ (1 : Nat) + 0 ≤ 0 + 0)⟩

-- `Lean.Grind.IntModule.OfNatModule.mk_pos` (hypothesis 4): NL: 0 < mk (1,0) in Q but not 0 < 1.
theorem OfNatModule_mk_pos_h4 : ¬ drop0% _private.Init.Grind.Module.Envelope.«0».Lean.Grind.IntModule.OfNatModule.mk_pos 4 :=
  fun h => (h (α := NL) (a₁ := (1 : Nat)) (a₂ := (0 : Nat))).mp
    ⟨(by decide : (0 : Nat) + 0 ≤ 0 + 1), (by decide : ¬ (1 : Nat) + 0 ≤ 0 + 0)⟩

-- `Lean.Grind.Ring.OfSemiring.rel_rfl` (hypothesis 2): removable (derivable). `r α` is an equivalence for every
-- semiring (`r_rfl`, `r_sym`, `r_trans`).
theorem OfSemiring_rel_rfl_h2 : indep% _private.Init.Grind.Ring.Envelope.«0».Lean.Grind.Ring.OfSemiring.rel_rfl 2 := by
  intros
  exact ⟨Ring.OfSemiring.r_rfl, Ring.OfSemiring.r_sym, Ring.OfSemiring.r_trans⟩

-- `Lean.Grind.Ring.OfSemiring.helper` (hypothesis 2): removable (derivable), as for rel_rfl.
theorem OfSemiring_helper_h2 : indep% _private.Init.Grind.Ring.Envelope.«0».Lean.Grind.Ring.OfSemiring.helper 2 := by
  intros
  exact ⟨Ring.OfSemiring.r_rfl, Ring.OfSemiring.r_sym, Ring.OfSemiring.r_trans⟩

-- `Lean.Grind.Ring.OfSemiring.helper` (hypothesis 5): Nat, q₁ = mk (0,0), q₂ = mk (1,0): rel needs 0 + k = 1 + k.
theorem OfSemiring_helper_h5 : ¬ drop0% _private.Init.Grind.Ring.Envelope.«0».Lean.Grind.Ring.OfSemiring.helper 5 :=
  fun h => by
    obtain ⟨k, hk⟩ := h (α := Nat) ⟨Ring.OfSemiring.r_rfl, Ring.OfSemiring.r_sym, Ring.OfSemiring.r_trans⟩
      (Ring.OfSemiring.Q.mk (0, 0)) (Ring.OfSemiring.Q.mk (1, 0))
    change 0 + 0 + k = 0 + 1 + k at hk; omega

-- `Lean.Grind.Ring.OfSemiring.mk_lt_mk` (hypothesis 4): NL (< always false): mk (0,0) < mk (1,0) in Q but not 0 < 1.
theorem OfSemiring_mk_lt_mk_h4 : ¬ drop0% _private.Init.Grind.Ring.Envelope.«0».Lean.Grind.Ring.OfSemiring.mk_lt_mk 4 :=
  fun h => (h (α := NL) (a₁ := (0 : Nat)) (a₂ := (0 : Nat)) (b₁ := (1 : Nat)) (b₂ := (0 : Nat))).mp
    ⟨(by decide : (0 : Nat) + 0 ≤ 0 + 1), (by decide : ¬ (1 : Nat) + 0 ≤ 0 + 0)⟩

-- `Lean.Grind.Ring.OfSemiring.mk_pos` (hypothesis 4): NL: 0 < mk (1,0) in Q but not 0 < 1.
theorem OfSemiring_mk_pos_h4 : ¬ drop0% _private.Init.Grind.Ring.Envelope.«0».Lean.Grind.Ring.OfSemiring.mk_pos 4 :=
  fun h => (h (α := NL) (a₁ := (1 : Nat)) (a₂ := (0 : Nat))).mp
    ⟨(by decide : (0 : Nat) + 0 ≤ 0 + 1), (by decide : ¬ (1 : Nat) + 0 ≤ 0 + 0)⟩

/-! ### `Init.Grind.Ordered.Field` -/

-- `Lean.Grind.Field.IsOrdered.le_mul_inv_of_le_mul` (hypothesis 4): RLTne (< is ≠, OrderedRing, < not lawful), a = 0, b = 1, c = 1: the premises hold, the conclusion fails.
theorem Field_le_mul_inv_of_le_mul_h4 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.le_mul_inv_of_le_mul 4 :=
  fun h => absurd (h (R := RLTne) (a := 0) (b := 1) (c := 1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.le_mul_inv_of_le_mul` (hypothesis 5): RS (≤ and < both strict, lawful <, ≤ not reflexive): a = 0, b = -1, c = -1 satisfy the other premises, and RS is not a linear order.
theorem Field_le_mul_inv_of_le_mul_h5 : ¬ indep0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.le_mul_inv_of_le_mul 5 :=
  fun h => RS.not_linear (h (R := RS) (a := 0) (b := -1) (c := -1) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.Field.IsOrdered.le_mul_inv_of_le_mul` (hypothesis 6): RRev (reversed lawful linear order, no OrderedRing), a = 0, b = -1, c = 1: the premises hold, the conclusion fails.
theorem Field_le_mul_inv_of_le_mul_h6 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.le_mul_inv_of_le_mul 6 :=
  fun h => absurd (h (R := RRev) (a := 0) (b := -1) (c := 1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.le_mul_inv_of_le_mul` (hypothesis 11): Rat, a = 0, b = 1, c = -1: the premises hold, the conclusion fails.
theorem Field_le_mul_inv_of_le_mul_h11 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.le_mul_inv_of_le_mul 11 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := 1) (c := -1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.le_mul_inv_of_mul_le` (hypothesis 4): RLTne (< is ≠, OrderedRing, < not lawful), a = 0, b = -1, c = 1: the premises hold, the conclusion fails.
theorem Field_le_mul_inv_of_mul_le_h4 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.le_mul_inv_of_mul_le 4 :=
  fun h => absurd (h (R := RLTne) (a := 0) (b := -1) (c := 1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.le_mul_inv_of_mul_le` (hypothesis 5): RS (≤ and < both strict, lawful <, ≤ not reflexive): a = 0, b = 1, c = 1 satisfy the other premises, and RS is not a linear order.
theorem Field_le_mul_inv_of_mul_le_h5 : ¬ indep0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.le_mul_inv_of_mul_le 5 :=
  fun h => RS.not_linear (h (R := RS) (a := 0) (b := 1) (c := 1) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.Field.IsOrdered.le_mul_inv_of_mul_le` (hypothesis 6): RRev (reversed lawful linear order, no OrderedRing), a = 0, b = -1, c = -1: the premises hold, the conclusion fails.
theorem Field_le_mul_inv_of_mul_le_h6 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.le_mul_inv_of_mul_le 6 :=
  fun h => absurd (h (R := RRev) (a := 0) (b := -1) (c := -1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.le_mul_inv_of_mul_le` (hypothesis 11): Rat, a = 0, b = 1, c = -1: the premises hold, the conclusion fails.
theorem Field_le_mul_inv_of_mul_le_h11 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.le_mul_inv_of_mul_le 11 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := 1) (c := -1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.le_mul_of_le_mul_inv` (hypothesis 4): RLTne (< is ≠, OrderedRing, < not lawful), a = 0, b = 1, c = 1: the premises hold, the conclusion fails.
theorem Field_le_mul_of_le_mul_inv_h4 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.le_mul_of_le_mul_inv 4 :=
  fun h => absurd (h (R := RLTne) (a := 0) (b := 1) (c := 1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.le_mul_of_le_mul_inv` (hypothesis 5): RS (≤ and < both strict, lawful <, ≤ not reflexive): a = 0, b = -1, c = -1 satisfy the other premises, and RS is not a linear order.
theorem Field_le_mul_of_le_mul_inv_h5 : ¬ indep0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.le_mul_of_le_mul_inv 5 :=
  fun h => RS.not_linear (h (R := RS) (a := 0) (b := -1) (c := -1) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.Field.IsOrdered.le_mul_of_le_mul_inv` (hypothesis 6): RRev (reversed lawful linear order, no OrderedRing), a = 0, b = -1, c = 1: the premises hold, the conclusion fails.
theorem Field_le_mul_of_le_mul_inv_h6 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.le_mul_of_le_mul_inv 6 :=
  fun h => absurd (h (R := RRev) (a := 0) (b := -1) (c := 1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.le_mul_of_le_mul_inv` (hypothesis 11): Rat, a = 0, b = 1, c = -1: the premises hold, the conclusion fails.
theorem Field_le_mul_of_le_mul_inv_h11 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.le_mul_of_le_mul_inv 11 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := 1) (c := -1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.lt_mul_inv_of_lt_mul` (hypothesis 4): RLTge1 (a < b iff a + 1 ≤ b, OrderedRing, < not lawful), a = 0, b = -1/2, c = -2: the premises hold, the conclusion fails.
theorem Field_lt_mul_inv_of_lt_mul_h4 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.lt_mul_inv_of_lt_mul 4 :=
  fun h => absurd (h (R := RLTge1) (a := 0) (b := -1/2) (c := -2) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.lt_mul_inv_of_lt_mul` (hypothesis 5): RS (≤ and < both strict, lawful <, ≤ not reflexive): a = 0, b = -1, c = -1 satisfy the other premises, and RS is not a linear order.
theorem Field_lt_mul_inv_of_lt_mul_h5 : ¬ indep0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.lt_mul_inv_of_lt_mul 5 :=
  fun h => RS.not_linear (h (R := RS) (a := 0) (b := -1) (c := -1) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.Field.IsOrdered.lt_mul_inv_of_lt_mul` (hypothesis 6): RRev (reversed lawful linear order, no OrderedRing), a = 0, b = -1, c = 1: the premises hold, the conclusion fails.
theorem Field_lt_mul_inv_of_lt_mul_h6 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.lt_mul_inv_of_lt_mul 6 :=
  fun h => absurd (h (R := RRev) (a := 0) (b := -1) (c := 1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.lt_mul_inv_of_lt_mul` (hypothesis 10): Rat, a = 0, b = 1, c = 1: the premises hold, the conclusion fails.
theorem Field_lt_mul_inv_of_lt_mul_h10 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.lt_mul_inv_of_lt_mul 10 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := 1) (c := 1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.lt_mul_inv_of_lt_mul` (hypothesis 11): Rat, a = 0, b = 0, c = -1: the premises hold, the conclusion fails.
theorem Field_lt_mul_inv_of_lt_mul_h11 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.lt_mul_inv_of_lt_mul 11 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := 0) (c := -1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.lt_mul_inv_of_mul_lt` (hypothesis 4): RLTge1 (a < b iff a + 1 ≤ b, OrderedRing, < not lawful), a = 0, b = 2, c = 1: the premises hold, the conclusion fails.
theorem Field_lt_mul_inv_of_mul_lt_h4 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.lt_mul_inv_of_mul_lt 4 :=
  fun h => absurd (h (R := RLTge1) (a := 0) (b := 2) (c := 1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.lt_mul_inv_of_mul_lt` (hypothesis 5): RS (≤ and < both strict, lawful <, ≤ not reflexive): a = 0, b = 1, c = 1 satisfy the other premises, and RS is not a linear order.
theorem Field_lt_mul_inv_of_mul_lt_h5 : ¬ indep0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.lt_mul_inv_of_mul_lt 5 :=
  fun h => RS.not_linear (h (R := RS) (a := 0) (b := 1) (c := 1) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.Field.IsOrdered.lt_mul_inv_of_mul_lt` (hypothesis 6): RRev (reversed lawful linear order, no OrderedRing), a = 0, b = -1, c = -1: the premises hold, the conclusion fails.
theorem Field_lt_mul_inv_of_mul_lt_h6 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.lt_mul_inv_of_mul_lt 6 :=
  fun h => absurd (h (R := RRev) (a := 0) (b := -1) (c := -1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.lt_mul_of_lt_mul_inv` (hypothesis 4): RLTle (< is ≤, OrderedRing, < not lawful), a = 0, b = 1, c = 0: the premises hold, the conclusion fails.
theorem Field_lt_mul_of_lt_mul_inv_h4 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.lt_mul_of_lt_mul_inv 4 :=
  fun h => absurd (h (R := RLTle) (a := 0) (b := 1) (c := 0) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.lt_mul_of_lt_mul_inv` (hypothesis 5): RS (≤ and < both strict, lawful <, ≤ not reflexive): a = 0, b = -1, c = -1 satisfy the other premises, and RS is not a linear order.
theorem Field_lt_mul_of_lt_mul_inv_h5 : ¬ indep0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.lt_mul_of_lt_mul_inv 5 :=
  fun h => RS.not_linear (h (R := RS) (a := 0) (b := -1) (c := -1) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.Field.IsOrdered.lt_mul_of_lt_mul_inv` (hypothesis 6): RRev (reversed lawful linear order, no OrderedRing), a = 0, b = -1, c = 1: the premises hold, the conclusion fails.
theorem Field_lt_mul_of_lt_mul_inv_h6 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.lt_mul_of_lt_mul_inv 6 :=
  fun h => absurd (h (R := RRev) (a := 0) (b := -1) (c := 1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.lt_mul_of_lt_mul_inv` (hypothesis 10): Rat, a = 0, b = 1, c = 1: the premises hold, the conclusion fails.
theorem Field_lt_mul_of_lt_mul_inv_h10 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.lt_mul_of_lt_mul_inv 10 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := 1) (c := 1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.lt_mul_of_lt_mul_inv` (hypothesis 11): Rat, a = 0, b = 0, c = -1: the premises hold, the conclusion fails.
theorem Field_lt_mul_of_lt_mul_inv_h11 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.lt_mul_of_lt_mul_inv 11 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := 0) (c := -1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_inv_le_iff_le_mul` (hypothesis 4): RLTne (< is ≠, OrderedRing, < not lawful), a = 0, b = -1, c = 1: the premises hold, the conclusion fails.
theorem Field_mul_inv_le_iff_le_mul_h4 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_inv_le_iff_le_mul 4 :=
  fun h => absurd (h (R := RLTne) (a := 0) (c := 1) (b := -1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_inv_le_iff_le_mul` (hypothesis 5): RS (≤ and < both strict, lawful <, ≤ not reflexive): a = 0, b = 1, c = 0 satisfy the other premises, and RS is not a linear order.
theorem Field_mul_inv_le_iff_le_mul_h5 : ¬ indep0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_inv_le_iff_le_mul 5 :=
  fun h => RS.not_linear (h (R := RS) (a := 0) (c := 0) (b := 1) (by decide +kernel))

-- `Lean.Grind.Field.IsOrdered.mul_inv_le_iff_le_mul` (hypothesis 6): RRev (reversed lawful linear order, no OrderedRing), a = 0, b = -1, c = 1: the premises hold, the conclusion fails.
theorem Field_mul_inv_le_iff_le_mul_h6 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_inv_le_iff_le_mul 6 :=
  fun h => absurd (h (R := RRev) (a := 0) (c := 1) (b := -1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_inv_le_of_mul_le` (hypothesis 4): RLTne (< is ≠, OrderedRing, < not lawful), a = 0, b = 1, c = 1: the premises hold, the conclusion fails.
theorem Field_mul_inv_le_of_mul_le_h4 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_inv_le_of_mul_le 4 :=
  fun h => absurd (h (R := RLTne) (a := 0) (b := 1) (c := 1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_inv_le_of_mul_le` (hypothesis 5): RS (≤ and < both strict, lawful <, ≤ not reflexive): a = 0, b = -1, c = 1 satisfy the other premises, and RS is not a linear order.
theorem Field_mul_inv_le_of_mul_le_h5 : ¬ indep0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_inv_le_of_mul_le 5 :=
  fun h => RS.not_linear (h (R := RS) (a := 0) (b := -1) (c := 1) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.Field.IsOrdered.mul_inv_le_of_mul_le` (hypothesis 6): RRev (reversed lawful linear order, no OrderedRing), a = 0, b = 1, c = -1: the premises hold, the conclusion fails.
theorem Field_mul_inv_le_of_mul_le_h6 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_inv_le_of_mul_le 6 :=
  fun h => absurd (h (R := RRev) (a := 0) (b := 1) (c := -1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_inv_le_of_mul_le` (hypothesis 10): Rat, a = 0, b = 1, c = 1: the premises hold, the conclusion fails.
theorem Field_mul_inv_le_of_mul_le_h10 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_inv_le_of_mul_le 10 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := 1) (c := 1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_inv_le_of_mul_le` (hypothesis 11): Rat, a = 0, b = -1, c = -1: the premises hold, the conclusion fails.
theorem Field_mul_inv_le_of_mul_le_h11 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_inv_le_of_mul_le 11 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := -1) (c := -1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_inv_lt_of_mul_lt` (hypothesis 4): RLTge1 (a < b iff a + 1 ≤ b, OrderedRing, < not lawful), a = 0, b = -2, c = 1: the premises hold, the conclusion fails.
theorem Field_mul_inv_lt_of_mul_lt_h4 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_inv_lt_of_mul_lt 4 :=
  fun h => absurd (h (R := RLTge1) (a := 0) (b := -2) (c := 1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_inv_lt_of_mul_lt` (hypothesis 5): RS (≤ and < both strict, lawful <, ≤ not reflexive): a = 0, b = -1, c = 1 satisfy the other premises, and RS is not a linear order.
theorem Field_mul_inv_lt_of_mul_lt_h5 : ¬ indep0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_inv_lt_of_mul_lt 5 :=
  fun h => RS.not_linear (h (R := RS) (a := 0) (b := -1) (c := 1) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.Field.IsOrdered.mul_inv_lt_of_mul_lt` (hypothesis 6): RRev (reversed lawful linear order, no OrderedRing), a = 0, b = 1, c = -1: the premises hold, the conclusion fails.
theorem Field_mul_inv_lt_of_mul_lt_h6 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_inv_lt_of_mul_lt 6 :=
  fun h => absurd (h (R := RRev) (a := 0) (b := 1) (c := -1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_inv_lt_of_mul_lt` (hypothesis 11): Rat, a = 0, b = -1, c = 0: the premises hold, the conclusion fails.
theorem Field_mul_inv_lt_of_mul_lt_h11 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_inv_lt_of_mul_lt 11 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := -1) (c := 0) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_le_of_le_mul_inv` (hypothesis 4): RLTne (< is ≠, OrderedRing, < not lawful), a = 0, b = -1, c = -1: the premises hold, the conclusion fails.
theorem Field_mul_le_of_le_mul_inv_h4 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_le_of_le_mul_inv 4 :=
  fun h => absurd (h (R := RLTne) (a := 0) (b := -1) (c := -1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_le_of_le_mul_inv` (hypothesis 5): RS (≤ and < both strict, lawful <, ≤ not reflexive): a = 0, b = 1, c = 1 satisfy the other premises, and RS is not a linear order.
theorem Field_mul_le_of_le_mul_inv_h5 : ¬ indep0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_le_of_le_mul_inv 5 :=
  fun h => RS.not_linear (h (R := RS) (a := 0) (b := 1) (c := 1) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.Field.IsOrdered.mul_le_of_le_mul_inv` (hypothesis 6): RRev (reversed lawful linear order, no OrderedRing), a = 0, b = 1, c = -1: the premises hold, the conclusion fails.
theorem Field_mul_le_of_le_mul_inv_h6 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_le_of_le_mul_inv 6 :=
  fun h => absurd (h (R := RRev) (a := 0) (b := 1) (c := -1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_le_of_le_mul_inv` (hypothesis 10): Rat, a = 0, b = -1, c = 0: the premises hold, the conclusion fails.
theorem Field_mul_le_of_le_mul_inv_h10 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_le_of_le_mul_inv 10 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := -1) (c := 0) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_le_of_le_mul_inv` (hypothesis 11): Rat, a = 0, b = -1, c = 1: the premises hold, the conclusion fails.
theorem Field_mul_le_of_le_mul_inv_h11 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_le_of_le_mul_inv 11 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := -1) (c := 1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_le_of_mul_inv_le` (hypothesis 4): RLTne (< is ≠, OrderedRing, < not lawful), a = 0, b = 1, c = 1: the premises hold, the conclusion fails.
theorem Field_mul_le_of_mul_inv_le_h4 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_le_of_mul_inv_le 4 :=
  fun h => absurd (h (R := RLTne) (a := 0) (b := 1) (c := 1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_le_of_mul_inv_le` (hypothesis 5): RS (≤ and < both strict, lawful <, ≤ not reflexive): a = 0, b = -1, c = 1 satisfy the other premises, and RS is not a linear order.
theorem Field_mul_le_of_mul_inv_le_h5 : ¬ indep0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_le_of_mul_inv_le 5 :=
  fun h => RS.not_linear (h (R := RS) (a := 0) (b := -1) (c := 1) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.Field.IsOrdered.mul_le_of_mul_inv_le` (hypothesis 6): RRev (reversed lawful linear order, no OrderedRing), a = 0, b = 1, c = -1: the premises hold, the conclusion fails.
theorem Field_mul_le_of_mul_inv_le_h6 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_le_of_mul_inv_le 6 :=
  fun h => absurd (h (R := RRev) (a := 0) (b := 1) (c := -1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_le_of_mul_inv_le` (hypothesis 10): Rat, a = 0, b = 1, c = 1: the premises hold, the conclusion fails.
theorem Field_mul_le_of_mul_inv_le_h10 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_le_of_mul_inv_le 10 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := 1) (c := 1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_le_of_mul_inv_le` (hypothesis 11): Rat, a = 0, b = -1, c = -1: the premises hold, the conclusion fails.
theorem Field_mul_le_of_mul_inv_le_h11 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_le_of_mul_inv_le 11 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := -1) (c := -1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_lt_of_lt_mul_inv` (hypothesis 4): RLTle (< is ≤, OrderedRing, < not lawful), a = 0, b = -1, c = 0: the premises hold, the conclusion fails.
theorem Field_mul_lt_of_lt_mul_inv_h4 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_lt_of_lt_mul_inv 4 :=
  fun h => absurd (h (R := RLTle) (a := 0) (b := -1) (c := 0) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_lt_of_lt_mul_inv` (hypothesis 5): RS (≤ and < both strict, lawful <, ≤ not reflexive): a = 0, b = 1, c = 1 satisfy the other premises, and RS is not a linear order.
theorem Field_mul_lt_of_lt_mul_inv_h5 : ¬ indep0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_lt_of_lt_mul_inv 5 :=
  fun h => RS.not_linear (h (R := RS) (a := 0) (b := 1) (c := 1) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.Field.IsOrdered.mul_lt_of_lt_mul_inv` (hypothesis 6): RRev (reversed lawful linear order, no OrderedRing), a = 0, b = 1, c = -1: the premises hold, the conclusion fails.
theorem Field_mul_lt_of_lt_mul_inv_h6 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_lt_of_lt_mul_inv 6 :=
  fun h => absurd (h (R := RRev) (a := 0) (b := 1) (c := -1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_lt_of_lt_mul_inv` (hypothesis 10): Rat, a = 0, b = -1, c = -1: the premises hold, the conclusion fails.
theorem Field_mul_lt_of_lt_mul_inv_h10 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_lt_of_lt_mul_inv 10 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := -1) (c := -1) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_lt_of_mul_inv_lt` (hypothesis 4): RLTle (< is ≤, OrderedRing, < not lawful), a = -1, b = 0, c = 0: the premises hold, the conclusion fails.
theorem Field_mul_lt_of_mul_inv_lt_h4 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_lt_of_mul_inv_lt 4 :=
  fun h => absurd (h (R := RLTle) (a := -1) (b := 0) (c := 0) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_lt_of_mul_inv_lt` (hypothesis 5): RS (≤ and < both strict, lawful <, ≤ not reflexive): a = 0, b = -1, c = 1 satisfy the other premises, and RS is not a linear order.
theorem Field_mul_lt_of_mul_inv_lt_h5 : ¬ indep0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_lt_of_mul_inv_lt 5 :=
  fun h => RS.not_linear (h (R := RS) (a := 0) (b := -1) (c := 1) (by decide +kernel) (by decide +kernel))

-- `Lean.Grind.Field.IsOrdered.mul_lt_of_mul_inv_lt` (hypothesis 6): RRev (reversed lawful linear order, no OrderedRing), a = 0, b = 1, c = -1: the premises hold, the conclusion fails.
theorem Field_mul_lt_of_mul_inv_lt_h6 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_lt_of_mul_inv_lt 6 :=
  fun h => absurd (h (R := RRev) (a := 0) (b := 1) (c := -1) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Lean.Grind.Field.IsOrdered.mul_lt_of_mul_inv_lt` (hypothesis 11): Rat, a = 0, b = -1, c = 0: the premises hold, the conclusion fails.
theorem Field_mul_lt_of_mul_inv_lt_h11 : ¬ drop0% _private.Init.Grind.Ordered.Field.«0».Lean.Grind.Field.IsOrdered.mul_lt_of_mul_inv_lt 11 :=
  fun h => absurd (h (R := Rat) (a := 0) (b := -1) (c := 0) (by decide +kernel)) (by decide +kernel)
