import Lean

/-!
Hand pass over cluster `OrderOrd` (hand7): the 115 unresolved hypotheses of `Init.Data.Order.Ord`
(lawfulness classes `ReflCmp`/`OrientedCmp`/`TransCmp`/`LawfulEqCmp`/`LawfulBEqCmp`, their `Ord`
versions, their instances for `compareLex`/`compareOn`/`Prod`/`List`/`Array`/`Option`, and the
`compareOfLessAndEq` and `flatMap` lemmas). For hypothesis `hᵢ` of theorem `T` this file proves
`T'` (removable) or `¬T'` (necessary). Everything is refuted at `Type` (all universes `0`).

113 necessary, 2 removable, 0 independent.

Removable (2):
* `Std.LawfulEqCmp.opposite` and `Std.LawfulEqOrd.opposite`, `[OrientedCmp cmp]` resp.
  `[OrientedOrd α]`: the flip of a `LawfulEqCmp` comparison is `LawfulEqCmp` without orientation
  (`cmp b a = .eq → b = a`, and `cmp a a = .eq`). Orientation does not follow from `LawfulEqCmp`
  (`offGT` below), so the hypothesis is simply unneeded.

Necessary (113): each `¬T'` instantiates the hypothetical `T'` at one of the models below and
evaluates with `decide`. Comparison functions (`Fin 3`/`Bool`), each violating one law:
* `rps`: rock-paper-scissors on `Fin 3` (`0 < 1 < 2 < 0`): oriented, `LawfulEqCmp`, not transitive.
* `bridge`: on `Fin 3`, `0` is `.eq` to everything, `1 < 2`: oriented, not transitive (`.eq` is not).
* `offGT`: `.gt` off the diagonal on `Bool`: `LawfulEqCmp`, `isLE`-transitive, not oriented.
* `oneWay`: `true` is `.eq` to `false`, `false` is `.lt` than `true`: reflexive, not oriented.
* `allEq`: constantly `.eq`: transitive, not `LawfulEqCmp`. `cgt`: constantly `.gt`: not reflexive.
Type synonyms carrying them as `Ord`, with `BEq` where needed: `RPS`, `OffGT`, `CGT`, `AllEq`
(usual `==`), `BF` (`==` false, `compare` `.lt`), `BT` (`==` true, `compare` `.eq`), `BFStd`
(`==` false, usual `compare`), `BAsym` (`a == b := a || !b`, `compare` from `==`); and with
`LT`/`LE` for `compareOfLessAndEq`: `LeAll` (`≤` true, `<` empty: not antisymmetric), `Cyc`
(cyclic tournament on `Fin 3`: not transitive), `LeEq` (`≤` is `=`: not total), `LtNone` (usual
`≤`, `<` empty: `not_le` fails). The laws each model satisfies are proved once as instances.
`List`/`Array`/`Option` instances fail at singletons (`[x]`, `#[x]`, `some x`); the `flatMap`
lemmas fail for blocks of different lengths compared by `allEq` (`LawfulEq`), for `f false` a
prefix of `f true` (`hp`), and for `f _ = []` on `Unit` (`hx`).

`drop% T i` elaborates to `T'` (`T` without binder `i`, universe parameters set to `0`), read off
the library rather than retyped; `check_hand.py` compares it with its own construction.

Run with the lean4 repo's stage1 binary: `lean checks/OrderOrdHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option warn.classDefReducibility false

open Lean Meta Elab Term in
/-- `drop% T i`: `T` at universe `0` with its (non-dependent) Prop binder `i` dropped. -/
elab "drop% " T:ident i:num : term => do
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

/-- Evaluate a specialization of the hypothetical `T'` to `False`. -/
macro "ev " t:term : tactic => `(tactic| (have := $t; revert this; decide))

namespace OrderOrdHand

/-! ## Comparison functions -/

/-- Rock-paper-scissors on `Fin 3`: `a < a + 1` cyclically. -/
def rps (a b : Fin 3) : Ordering := if a = b then .eq else if b = a + 1 then .lt else .gt
/-- `0` compares `.eq` to everything, `1 < 2`. -/
def bridge (a b : Fin 3) : Ordering :=
  if a = b ∨ a = 0 ∨ b = 0 then .eq else if a < b then .lt else .gt
/-- `.gt` off the diagonal. -/
def offGT (a b : Bool) : Ordering := if a = b then .eq else .gt
/-- `cmp true false = .eq`, `cmp false true = .lt`. -/
def oneWay (a b : Bool) : Ordering := if a = b then .eq else if a then .eq else .lt
/-- Constantly `.eq`. -/
def allEq {α : Type} (_ _ : α) : Ordering := .eq
/-- Constantly `.gt`. -/
def cgt {α : Type} (_ _ : α) : Ordering := .gt

instance rps_oriented : Std.OrientedCmp rps := ⟨fun {a b} => by revert a b; decide⟩
instance rps_lawfulEq : Std.LawfulEqCmp rps :=
  { compare_self := fun {a} => by revert a; decide, eq_of_compare := fun {a b} => by revert a b; decide }
theorem rps_not_trans : ¬ Std.TransCmp rps := fun h =>
  absurd (h.isLE_trans (a := 0) (b := 1) (c := 2) (by decide) (by decide)) (by decide)

instance bridge_oriented : Std.OrientedCmp bridge := ⟨fun {a b} => by revert a b; decide⟩
theorem bridge_not_trans : ¬ Std.TransCmp bridge := fun h =>
  absurd (h.eq_trans (a := 1) (b := 0) (c := 2) (by decide) (by decide)) (by decide)

instance offGT_lawfulEq : Std.LawfulEqCmp offGT :=
  { compare_self := fun {a} => by revert a; decide, eq_of_compare := fun {a b} => by revert a b; decide }
theorem offGT_isLE_trans : ∀ {a b c : Bool}, (offGT a b).isLE → (offGT b c).isLE → (offGT a c).isLE := by
  decide
theorem offGT_not_oriented : ¬ Std.OrientedCmp offGT := fun h =>
  absurd (h.eq_swap (a := false) (b := true)) (by decide)

instance oneWay_refl : Std.ReflCmp oneWay := ⟨fun {a} => by revert a; decide⟩
theorem oneWay_not_oriented : ¬ Std.OrientedCmp oneWay := fun h =>
  absurd (h.eq_swap (a := true) (b := false)) (by decide)

instance allEq_trans {α : Type} : Std.TransCmp (allEq (α := α)) :=
  { eq_swap := rfl, isLE_trans := fun _ _ => rfl }
theorem allEq_not_lawfulEq : ¬ Std.LawfulEqCmp (allEq (α := Bool)) := fun h =>
  absurd (h.eq_of_compare (a := false) (b := true) rfl) (by decide)

theorem cgt_not_refl : ¬ Std.ReflCmp (cgt (α := Bool)) := fun h =>
  absurd (h.compare_self (a := true)) (by decide)

/-! ## Type synonyms with `Ord` / `BEq` / `LT` / `LE` instances -/

/-- `Fin 3` with `compare := rps`. -/
def RPS := Fin 3
instance {p : RPS → Prop} [d : DecidablePred p] : Decidable (∀ x, p x) := @Nat.decidableForallFin 3 p d
instance : DecidableEq RPS := inferInstanceAs (DecidableEq (Fin 3))
instance (n : Nat) : OfNat RPS n := ⟨Fin.ofNat 3 n⟩
instance : Ord RPS := ⟨rps⟩
instance : Std.OrientedOrd RPS := rps_oriented
instance : Std.LawfulEqOrd RPS := rps_lawfulEq

/-- `Bool` with `compare := offGT`. -/
def OffGT := Bool
instance : DecidableEq OffGT := inferInstanceAs (DecidableEq Bool)
instance {p : OffGT → Prop} [d : DecidablePred p] : Decidable (∀ x, p x) :=
  @Bool.instDecidableForallOfDecidablePred p d
instance : Ord OffGT := ⟨offGT⟩
instance : Std.LawfulEqOrd OffGT := offGT_lawfulEq

/-- `Bool` with `compare` constantly `.gt`. -/
def CGT := Bool
instance : DecidableEq CGT := inferInstanceAs (DecidableEq Bool)
instance {p : CGT → Prop} [d : DecidablePred p] : Decidable (∀ x, p x) :=
  @Bool.instDecidableForallOfDecidablePred p d
instance : Ord CGT := ⟨cgt⟩

/-- `Bool` with the usual `==` and `compare` constantly `.eq`. -/
def AllEq := Bool
instance {p : AllEq → Prop} [d : DecidablePred p] : Decidable (∀ x, p x) :=
  @Bool.instDecidableForallOfDecidablePred p d
instance : DecidableEq AllEq := inferInstanceAs (DecidableEq Bool)
instance : BEq AllEq := inferInstanceAs (BEq Bool)
instance : LawfulBEq AllEq := inferInstanceAs (LawfulBEq Bool)
instance : Ord AllEq := ⟨allEq⟩
instance : Std.TransOrd AllEq := allEq_trans

/-- `Bool` with `==` constantly `false` and `compare` constantly `.lt`. -/
def BF := Bool
instance : DecidableEq BF := inferInstanceAs (DecidableEq Bool)
instance {p : BF → Prop} [d : DecidablePred p] : Decidable (∀ x, p x) :=
  @Bool.instDecidableForallOfDecidablePred p d
instance : BEq BF := ⟨fun _ _ => false⟩
instance : Ord BF := ⟨fun _ _ => .lt⟩
instance : Std.LawfulBEqOrd BF := ⟨fun {a b} => by revert a b; decide⟩

/-- `Bool` with `==` constantly `true` and `compare` constantly `.eq`. -/
def BT := Bool
instance : DecidableEq BT := inferInstanceAs (DecidableEq Bool)
instance {p : BT → Prop} [d : DecidablePred p] : Decidable (∀ x, p x) :=
  @Bool.instDecidableForallOfDecidablePred p d
instance : BEq BT := ⟨fun _ _ => true⟩
instance : Ord BT := ⟨allEq⟩
instance : Std.LawfulBEqOrd BT := ⟨fun {a b} => by revert a b; decide⟩
instance : Std.TransOrd BT := allEq_trans

/-- `Bool` with `==` constantly `false` and the usual `compare`. -/
def BFStd := Bool
instance : DecidableEq BFStd := inferInstanceAs (DecidableEq Bool)
instance {p : BFStd → Prop} [d : DecidablePred p] : Decidable (∀ x, p x) :=
  @Bool.instDecidableForallOfDecidablePred p d
instance : BEq BFStd := ⟨fun _ _ => false⟩
instance : Ord BFStd := inferInstanceAs (Ord Bool)
instance : Std.TransOrd BFStd := inferInstanceAs (Std.TransOrd Bool)
instance : Std.LawfulEqOrd BFStd := inferInstanceAs (Std.LawfulEqOrd Bool)

/-- `Bool` with `a == b := a || !b` (reflexive, not symmetric) and `compare` from `==`. -/
def BAsym := Bool
instance : DecidableEq BAsym := inferInstanceAs (DecidableEq Bool)
instance {p : BAsym → Prop} [d : DecidablePred p] : Decidable (∀ x, p x) :=
  @Bool.instDecidableForallOfDecidablePred p d
instance : BEq BAsym := ⟨fun (a b : Bool) => a || !b⟩
instance : Ord BAsym := ⟨fun a b => if a == b then .eq else .lt⟩
instance : Std.LawfulBEqOrd BAsym := ⟨fun {a b} => by revert a b; decide⟩

/-- `Bool` with `≤` everywhere true and `<` empty. -/
def LeAll := Bool
instance : DecidableEq LeAll := inferInstanceAs (DecidableEq Bool)
instance : LE LeAll := ⟨fun _ _ => True⟩
instance : LT LeAll := ⟨fun _ _ => False⟩
instance : DecidableLE LeAll := fun _ _ => instDecidableTrue
instance : DecidableLT LeAll := fun _ _ => instDecidableFalse
instance {p : LeAll → Prop} [d : DecidablePred p] : Decidable (∀ x, p x) :=
  @Bool.instDecidableForallOfDecidablePred p d

/-- `Fin 3` with `a < b ↔ b = a + 1` and `a ≤ b ↔ a = b ∨ b = a + 1` (a cyclic tournament). -/
def Cyc := Fin 3
instance : DecidableEq Cyc := inferInstanceAs (DecidableEq (Fin 3))
instance (n : Nat) : OfNat Cyc n := ⟨Fin.ofNat 3 n⟩
instance : LE Cyc := ⟨fun (a b : Fin 3) => a = b ∨ b = a + 1⟩
instance : LT Cyc := ⟨fun (a b : Fin 3) => b = a + 1⟩
instance : DecidableLE Cyc := fun (a b : Fin 3) => inferInstanceAs (Decidable (a = b ∨ b = a + 1))
instance : DecidableLT Cyc := fun (a b : Fin 3) => inferInstanceAs (Decidable (b = a + 1))
instance {p : Cyc → Prop} [d : DecidablePred p] : Decidable (∀ x, p x) := @Nat.decidableForallFin 3 p d

/-- `Bool` with `≤` and `<` both equality resp. inequality. -/
def LeEq := Bool
instance : DecidableEq LeEq := inferInstanceAs (DecidableEq Bool)
instance : LE LeEq := ⟨fun a b => a = b⟩
instance : LT LeEq := ⟨fun a b => a ≠ b⟩
instance : DecidableLE LeEq := fun (a b : Bool) => inferInstanceAs (Decidable (a = b))
instance : DecidableLT LeEq := fun (a b : Bool) => inferInstanceAs (Decidable (a ≠ b))
instance {p : LeEq → Prop} [d : DecidablePred p] : Decidable (∀ x, p x) :=
  @Bool.instDecidableForallOfDecidablePred p d

/-- `Bool` with the usual `≤` and `<` empty. -/
def LtNone := Bool
instance : DecidableEq LtNone := inferInstanceAs (DecidableEq Bool)
instance : LE LtNone := inferInstanceAs (LE Bool)
instance : LT LtNone := ⟨fun _ _ => False⟩
instance : DecidableLE LtNone := inferInstanceAs (DecidableLE Bool)
instance : DecidableLT LtNone := fun _ _ => instDecidableFalse
instance {p : LtNone → Prop} [d : DecidablePred p] : Decidable (∀ x, p x) :=
  @Bool.instDecidableForallOfDecidablePred p d

/-- `hp` of the `Array` `flatMap` lemmas for `f a := if a then #[true, true] else #[false]`. -/
theorem hpA1 : ∀ (a b : Bool) (zs : Array Bool),
    (if a then #[true, true] else #[false]) ++ zs = (if b then #[true, true] else #[false]) → a = b := by
  intro a b zs h
  cases a <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  · have := congrArg Array.toList h; simp at this
  · have := congrArg Array.size h; simp at this; omega

-- `Std.OrientedCmp.isGE_antisymm`, idx 2 (inst : Std.OrientedCmp cmp): cmp := offGT (.gt off the diagonal on Bool: LawfulEqCmp, not oriented), a = false, b = true
theorem Std.OrientedCmp.isGE_antisymm.h2 : ¬ drop% Std.OrientedCmp.isGE_antisymm 2 := fun h => by
  ev @h _ offGT false true (by decide) (by decide)

-- `Std.OrientedCmp.not_gt_of_isGE`, idx 2 (inst : Std.OrientedCmp cmp): cmp := offGT (.gt off the diagonal on Bool: LawfulEqCmp, not oriented), a = false, b = true
theorem Std.OrientedCmp.not_gt_of_isGE.h2 : ¬ drop% Std.OrientedCmp.not_gt_of_isGE 2 := fun h => by
  ev @h _ offGT false true (by decide)

-- `Std.OrientedCmp.lt_of_gt`, idx 2 (inst : Std.OrientedCmp cmp): cmp := offGT (.gt off the diagonal on Bool: LawfulEqCmp, not oriented), a = false, b = true
theorem Std.OrientedCmp.lt_of_gt.h2 : ¬ drop% Std.OrientedCmp.lt_of_gt 2 := fun h => by
  ev @h _ offGT false true (by decide)

-- `Std.OrientedCmp.not_gt_of_gt`, idx 2 (inst : Std.OrientedCmp cmp): cmp := offGT (.gt off the diagonal on Bool: LawfulEqCmp, not oriented), a = false, b = true
theorem Std.OrientedCmp.not_gt_of_gt.h2 : ¬ drop% Std.OrientedCmp.not_gt_of_gt 2 := fun h => by
  ev @h _ offGT false true (by decide)

-- `Std.OrientedCmp.lt_of_not_isLE`, idx 2 (inst : Std.OrientedCmp cmp): cmp := offGT (.gt off the diagonal on Bool: LawfulEqCmp, not oriented), a = false, b = true
theorem Std.OrientedCmp.lt_of_not_isLE.h2 : ¬ drop% Std.OrientedCmp.lt_of_not_isLE 2 := fun h => by
  ev @h _ offGT false true (by decide)

-- `Std.OrientedCmp.isLE_of_isGE`, idx 2 (inst : Std.OrientedCmp cmp): cmp := offGT (.gt off the diagonal on Bool: LawfulEqCmp, not oriented), a = false, b = true
theorem Std.OrientedCmp.isLE_of_isGE.h2 : ¬ drop% Std.OrientedCmp.isLE_of_isGE 2 := fun h => by
  ev @h _ offGT false true (by decide)

-- `Std.OrientedCmp.not_isGE_of_gt`, idx 2 (inst : Std.OrientedCmp cmp): cmp := offGT (.gt off the diagonal on Bool: LawfulEqCmp, not oriented), a = false, b = true
theorem Std.OrientedCmp.not_isGE_of_gt.h2 : ¬ drop% Std.OrientedCmp.not_isGE_of_gt 2 := fun h => by
  ev @h _ offGT false true (by decide)

-- `Std.OrientedCmp.eq_symm`, idx 2 (inst : Std.OrientedCmp cmp): cmp := oneWay (oneWay true false = .eq, oneWay false true = .lt: reflexive, not oriented), a = true, b = false
theorem Std.OrientedCmp.eq_symm.h2 : ¬ drop% Std.OrientedCmp.eq_symm 2 := fun h => by
  ev @h _ oneWay true false (by decide)

-- `Std.OrientedCmp.eq_comm`, idx 2 (inst : Std.OrientedCmp cmp): cmp := oneWay (oneWay true false = .eq, oneWay false true = .lt: reflexive, not oriented), a = true, b = false
theorem Std.OrientedCmp.eq_comm.h2 : ¬ drop% Std.OrientedCmp.eq_comm 2 := fun h => by
  ev @h _ oneWay true false

-- `Std.OrientedCmp.opposite`, idx 2 (inst : Std.OrientedCmp cmp): cmp := offGT (not oriented, and neither is its flip): eq_swap fails at false, true
theorem Std.OrientedCmp.opposite.h2 : ¬ drop% Std.OrientedCmp.opposite 2 := fun h => by
  ev (@h _ offGT).eq_swap (a := false) (b := true)

-- `Std.OrientedOrd.opposite`, idx 2 (inst : Std.OrientedOrd α): Ord from offGT on a Bool synonym (OffGT, not oriented): the opposite fails eq_swap at false, true
theorem Std.OrientedOrd.opposite.h2 : ¬ drop% Std.OrientedOrd.opposite 2 := fun h => by
  ev @Std.OrientedCmp.eq_swap _ _ (@h OffGT _) false true

-- `Std.instReflCmpOfOrientedCmp`, idx 2 (inst : Std.OrientedCmp cmp): cmp := cgt (constantly .gt on Bool): cmp true true ≠ .eq
theorem Std.instReflCmpOfOrientedCmp.h2 : ¬ drop% Std.instReflCmpOfOrientedCmp 2 := fun h => by
  ev (@h _ (cgt (α := Bool))).compare_self (a := true)

-- `Std.TransCmp.toOrientedCmp`, idx 2 (self : Std.TransCmp cmp): cmp := offGT (LawfulEqCmp, isLE-transitive, not oriented): eq_swap fails at false, true
theorem Std.TransCmp.toOrientedCmp.h2 : ¬ drop% Std.TransCmp.toOrientedCmp 2 := fun h => by
  ev (@h _ offGT).eq_swap (a := false) (b := true)

-- `Std.TransCmp.isGE_trans`, idx 2 (inst : Std.TransCmp cmp): cmp := rps (rock-paper-scissors on Fin 3, 0 < 1 < 2 < 0: oriented and LawfulEqCmp, not transitive), a = 1, b = 0, c = 2
theorem Std.TransCmp.isGE_trans.h2 : ¬ drop% Std.TransCmp.isGE_trans 2 := fun h => by
  ev @h _ rps 1 0 2 (by decide) (by decide)

-- `Std.TransCmp.gt_of_gt_of_gt`, idx 2 (inst : Std.TransCmp cmp): cmp := rps (rock-paper-scissors on Fin 3, 0 < 1 < 2 < 0: oriented and LawfulEqCmp, not transitive), a = 1, b = 0, c = 2
theorem Std.TransCmp.gt_of_gt_of_gt.h2 : ¬ drop% Std.TransCmp.gt_of_gt_of_gt 2 := fun h => by
  ev @h _ rps 1 0 2 (by decide) (by decide)

-- `Std.TransCmp.gt_trans`, idx 2 (inst : Std.TransCmp cmp): cmp := rps (rock-paper-scissors on Fin 3, 0 < 1 < 2 < 0: oriented and LawfulEqCmp, not transitive), a = 1, b = 0, c = 2
theorem Std.TransCmp.gt_trans.h2 : ¬ drop% Std.TransCmp.gt_trans 2 := fun h => by
  ev @h _ rps 1 0 2 (by decide) (by decide)

-- `Std.TransCmp.gt_of_gt_of_isGE`, idx 2 (inst : Std.TransCmp cmp): cmp := rps (rock-paper-scissors on Fin 3, 0 < 1 < 2 < 0: oriented and LawfulEqCmp, not transitive), a = 1, b = 0, c = 2
theorem Std.TransCmp.gt_of_gt_of_isGE.h2 : ¬ drop% Std.TransCmp.gt_of_gt_of_isGE 2 := fun h => by
  ev @h _ rps 1 0 2 (by decide) (by decide)

-- `Std.TransCmp.gt_of_isGE_of_gt`, idx 2 (inst : Std.TransCmp cmp): cmp := rps (rock-paper-scissors on Fin 3, 0 < 1 < 2 < 0: oriented and LawfulEqCmp, not transitive), a = 1, b = 0, c = 2
theorem Std.TransCmp.gt_of_isGE_of_gt.h2 : ¬ drop% Std.TransCmp.gt_of_isGE_of_gt 2 := fun h => by
  ev @h _ rps 1 0 2 (by decide) (by decide)

-- `Std.TransCmp.isLE_trans`, idx 2 (self : Std.TransCmp cmp): cmp := rps (rock-paper-scissors on Fin 3, 0 < 1 < 2 < 0: oriented and LawfulEqCmp, not transitive), a = 0, b = 1, c = 2
theorem Std.TransCmp.isLE_trans.h2 : ¬ drop% Std.TransCmp.isLE_trans 2 := fun h => by
  ev @h _ rps 0 1 2 (by decide) (by decide)

-- `Std.TransCmp.lt_of_eq_of_lt`, idx 2 (inst : Std.TransCmp cmp): cmp := bridge (on Fin 3, 0 compares .eq to everything and 1 < 2: oriented, not transitive), a = 0, b = 1, c = 2
theorem Std.TransCmp.lt_of_eq_of_lt.h2 : ¬ drop% Std.TransCmp.lt_of_eq_of_lt 2 := fun h => by
  ev @h _ bridge 0 1 2 (by decide) (by decide)

-- `Std.TransCmp.lt_of_lt_of_eq`, idx 2 (inst : Std.TransCmp cmp): cmp := bridge (on Fin 3, 0 compares .eq to everything and 1 < 2: oriented, not transitive), a = 1, b = 2, c = 0
theorem Std.TransCmp.lt_of_lt_of_eq.h2 : ¬ drop% Std.TransCmp.lt_of_lt_of_eq 2 := fun h => by
  ev @h _ bridge 1 2 0 (by decide) (by decide)

-- `Std.TransCmp.gt_of_eq_of_gt`, idx 2 (inst : Std.TransCmp cmp): cmp := bridge (on Fin 3, 0 compares .eq to everything and 1 < 2: oriented, not transitive), a = 0, b = 2, c = 1
theorem Std.TransCmp.gt_of_eq_of_gt.h2 : ¬ drop% Std.TransCmp.gt_of_eq_of_gt 2 := fun h => by
  ev @h _ bridge 0 2 1 (by decide) (by decide)

-- `Std.TransCmp.gt_of_gt_of_eq`, idx 2 (inst : Std.TransCmp cmp): cmp := bridge (on Fin 3, 0 compares .eq to everything and 1 < 2: oriented, not transitive), a = 2, b = 1, c = 0
theorem Std.TransCmp.gt_of_gt_of_eq.h2 : ¬ drop% Std.TransCmp.gt_of_gt_of_eq 2 := fun h => by
  ev @h _ bridge 2 1 0 (by decide) (by decide)

-- `Std.TransCmp.eq_trans`, idx 2 (inst : Std.TransCmp cmp): cmp := bridge (on Fin 3, 0 compares .eq to everything and 1 < 2: oriented, not transitive), a = 1, b = 0, c = 2
theorem Std.TransCmp.eq_trans.h2 : ¬ drop% Std.TransCmp.eq_trans 2 := fun h => by
  ev @h _ bridge 1 0 2 (by decide) (by decide)

-- `Std.TransCmp.congr_left`, idx 2 (inst : Std.TransCmp cmp): cmp := bridge (on Fin 3, 0 compares .eq to everything and 1 < 2: oriented, not transitive), a = 0, b = 1, c = 2
theorem Std.TransCmp.congr_left.h2 : ¬ drop% Std.TransCmp.congr_left 2 := fun h => by
  ev @h _ bridge 0 1 2 (by decide)

-- `Std.TransCmp.congr_right`, idx 2 (inst : Std.TransCmp cmp): cmp := bridge (on Fin 3, 0 compares .eq to everything and 1 < 2: oriented, not transitive), a = 2, b = 1, c = 0
theorem Std.TransCmp.congr_right.h2 : ¬ drop% Std.TransCmp.congr_right 2 := fun h => by
  ev @h _ bridge 2 1 0 (by decide)

-- `Std.TransOrd.isGE_trans`, idx 2 (inst : Std.TransOrd α): Ord from rps on a Fin 3 synonym (RPS: oriented, LawfulEqOrd, not transitive), a = 1, b = 0, c = 2
theorem Std.TransOrd.isGE_trans.h2 : ¬ drop% Std.TransOrd.isGE_trans 2 := fun h => by
  ev @h RPS _ 1 0 2 (by decide) (by decide)

-- `Std.TransOrd.isLE_trans`, idx 2 (inst : Std.TransOrd α): Ord from rps on a Fin 3 synonym (RPS: oriented, LawfulEqOrd, not transitive), a = 0, b = 1, c = 2
theorem Std.TransOrd.isLE_trans.h2 : ¬ drop% Std.TransOrd.isLE_trans 2 := fun h => by
  ev @h RPS _ 0 1 2 (by decide) (by decide)

-- `Std.TransCmp.opposite`, idx 2 (inst : Std.TransCmp cmp): cmp := rps (rock-paper-scissors on Fin 3, 0 < 1 < 2 < 0: oriented and LawfulEqCmp, not transitive): the flip fails isLE_trans at 2, 1, 0
theorem Std.TransCmp.opposite.h2 : ¬ drop% Std.TransCmp.opposite 2 := fun h => by
  ev (@h _ rps).isLE_trans (a := 2) (b := 1) (c := 0) (by decide) (by decide)

-- `Std.TransOrd.opposite`, idx 2 (inst : Std.TransOrd α): Ord from rps (RPS): the opposite fails isLE_trans at 2, 1, 0
theorem Std.TransOrd.opposite.h2 : ¬ drop% Std.TransOrd.opposite 2 := fun h => by
  ev @Std.TransCmp.isLE_trans _ _ (@h RPS _) 2 1 0 (by decide) (by decide)

-- `Std.ReflCmp.isLE_rfl`, idx 2 (inst : Std.ReflCmp cmp): cmp := cgt (constantly .gt on Bool), a = true
theorem Std.ReflCmp.isLE_rfl.h2 : ¬ drop% Std.ReflCmp.isLE_rfl 2 := fun h => by
  ev @h _ (cgt (α := Bool)) true

-- `Std.ReflOrd.isLE_rfl`, idx 2 (inst : Std.ReflOrd α): Ord constantly .gt on a Bool synonym (CGT), a = true
theorem Std.ReflOrd.isLE_rfl.h2 : ¬ drop% Std.ReflOrd.isLE_rfl 2 := fun h => by
  ev @h CGT _ true

-- `Std.LawfulEqCmp.toReflCmp`, idx 2 (self : Std.LawfulEqCmp cmp): cmp := cgt (constantly .gt on Bool): cmp true true ≠ .eq
theorem Std.LawfulEqCmp.toReflCmp.h2 : ¬ drop% Std.LawfulEqCmp.toReflCmp 2 := fun h => by
  ev (@h _ (cgt (α := Bool))).compare_self (a := true)

-- `Std.LawfulEqCmp.opposite`, idx 2 (inst : Std.OrientedCmp cmp): the flip of a LawfulEqCmp is LawfulEqCmp without orientation: cmp b a = .eq → b = a
-- Stated with a universe variable (not via `drop%`, which fixes universes to 0).
theorem Std.LawfulEqCmp.opposite.h2.{u} {α : Type u} {cmp : α → α → Ordering}
    [inst : Std.LawfulEqCmp cmp] : Std.LawfulEqCmp (fun a b => cmp b a) :=
  { compare_self := inst.compare_self, eq_of_compare := fun h => (inst.eq_of_compare h).symm }

-- `Std.LawfulEqOrd.opposite`, idx 2 (inst : Std.OrientedOrd α): the opposite of a LawfulEqOrd is LawfulEqOrd without orientation: compare b a = .eq → b = a
-- Stated with a universe variable (not via `drop%`, which fixes universes to 0).
theorem Std.LawfulEqOrd.opposite.h2.{u} {α : Type u} [o : Ord α] [inst : Std.LawfulEqOrd α] :
    letI := Ord.opposite (α := α) o; Std.LawfulEqOrd α :=
  { compare_self := inst.compare_self, eq_of_compare := fun h => (inst.eq_of_compare h).symm }

-- `Std.LawfulEqCmp.opposite`, idx 3 (inst : Std.LawfulEqCmp cmp): cmp := allEq (constantly .eq on Bool: transitive, not LawfulEqCmp): false, true
theorem Std.LawfulEqCmp.opposite.h3 : ¬ drop% Std.LawfulEqCmp.opposite 3 := fun h => by
  exact absurd ((@h _ allEq _).eq_of_compare (a := false) (b := true) rfl) (by exact Bool.false_ne_true)

-- `Std.LawfulEqOrd.opposite`, idx 3 (inst : Std.LawfulEqOrd α): Ord constantly .eq on a Bool synonym (AllEq: TransOrd, not LawfulEqOrd): false, true
theorem Std.LawfulEqOrd.opposite.h3 : ¬ drop% Std.LawfulEqOrd.opposite 3 := fun h => by
  exact absurd (@Std.LawfulEqCmp.eq_of_compare _ _ (@h AllEq _ _) false true rfl) (by exact Bool.false_ne_true)

-- `Std.LawfulBEqCmp.opposite`, idx 3 (inst : Std.OrientedCmp cmp): BAsym: Bool with a == b := a || !b (not symmetric) and cmp a b := if a == b then .eq else .lt (LawfulBEqCmp): the flip has cmp false true = .eq but (false == true) = false
theorem Std.LawfulBEqCmp.opposite.h3 : ¬ drop% Std.LawfulBEqCmp.opposite 3 := fun h => by
  ev (@h BAsym _ compare _).compare_eq_iff_beq (a := false) (b := true)

-- `Std.LawfulBEqCmp.opposite`, idx 4 (inst : Std.LawfulBEqCmp cmp): AllEq: Bool with the usual == (LawfulBEq) and cmp constantly .eq (transitive, not LawfulBEqCmp): false, true
theorem Std.LawfulBEqCmp.opposite.h4 : ¬ drop% Std.LawfulBEqCmp.opposite 4 := fun h => by
  ev (@h AllEq _ compare _).compare_eq_iff_beq (a := false) (b := true)

-- `Std.LawfulBEqOrd.opposite`, idx 3 (inst : Std.OrientedOrd α): BAsym: Bool with a == b := a || !b (not symmetric) and cmp a b := if a == b then .eq else .lt (LawfulBEqCmp) as Ord: the opposite has compare false true = .eq but (false == true) = false
theorem Std.LawfulBEqOrd.opposite.h3 : ¬ drop% Std.LawfulBEqOrd.opposite 3 := fun h => by
  ev @Std.LawfulBEqCmp.compare_eq_iff_beq _ _ _ (@h BAsym _ _ _) false true

-- `Std.LawfulBEqOrd.opposite`, idx 4 (inst : Std.LawfulBEqOrd α): AllEq: Bool with the usual == (LawfulBEq) and cmp constantly .eq (transitive, not LawfulBEqCmp) as Ord: false, true
theorem Std.LawfulBEqOrd.opposite.h4 : ¬ drop% Std.LawfulBEqOrd.opposite 4 := fun h => by
  ev @Std.LawfulBEqCmp.compare_eq_iff_beq _ _ _ (@h AllEq _ _ _) false true

-- `Std.LawfulBEqCmp.equivBEq`, idx 3 (inst : Std.LawfulBEqCmp cmp): BFStd: Bool with == constantly false and the usual compare (TransCmp, LawfulEqCmp, not LawfulBEqCmp): == is not reflexive
theorem Std.LawfulBEqCmp.equivBEq.h3 : ¬ drop% Std.LawfulBEqCmp.equivBEq 3 := fun h => by
  ev (@h BFStd _ compare _).rfl (a := true)

-- `Std.LawfulBEqCmp.equivBEq`, idx 4 (inst : Std.TransCmp cmp): BF: Bool with == constantly false and cmp constantly .lt (LawfulBEqCmp, not reflexive): == is not reflexive
theorem Std.LawfulBEqCmp.equivBEq.h4 : ¬ drop% Std.LawfulBEqCmp.equivBEq 4 := fun h => by
  ev (@h BF _ compare _).rfl (a := true)

-- `Std.LawfulBEqCmp.lawfulBEq`, idx 3 (inst : Std.LawfulBEqCmp cmp): BFStd: Bool with == constantly false and the usual compare (TransCmp, LawfulEqCmp, not LawfulBEqCmp): == is not reflexive
theorem Std.LawfulBEqCmp.lawfulBEq.h3 : ¬ drop% Std.LawfulBEqCmp.lawfulBEq 3 := fun h => by
  ev (@h BFStd _ compare _).rfl (a := true)

-- `Std.LawfulBEqCmp.lawfulBEq`, idx 4 (inst : Std.LawfulEqCmp cmp): BT: Bool with == constantly true and cmp constantly .eq (LawfulBEqCmp, transitive, not LawfulEqCmp, == not lawful): false == true
theorem Std.LawfulBEqCmp.lawfulBEq.h4 : ¬ drop% Std.LawfulBEqCmp.lawfulBEq 4 := fun h => by
  exact absurd ((@h BT _ compare _).eq_of_beq (a := false) (b := true) rfl) (by exact Bool.false_ne_true)

-- `Std.LawfulBEqCmp.lawfulEqCmp`, idx 3 (inst : Std.LawfulBEqCmp cmp): AllEq: Bool with the usual == (LawfulBEq) and cmp constantly .eq (transitive, not LawfulBEqCmp): cmp false true = .eq
theorem Std.LawfulBEqCmp.lawfulEqCmp.h3 : ¬ drop% Std.LawfulBEqCmp.lawfulEqCmp 3 := fun h => by
  exact absurd ((@h AllEq _ compare _).eq_of_compare (a := false) (b := true) rfl) (by exact Bool.false_ne_true)

-- `Std.LawfulBEqCmp.lawfulEqCmp`, idx 4 (inst : LawfulBEq α): BT: Bool with == constantly true and cmp constantly .eq (LawfulBEqCmp, transitive, not LawfulEqCmp, == not lawful): cmp false true = .eq
theorem Std.LawfulBEqCmp.lawfulEqCmp.h4 : ¬ drop% Std.LawfulBEqCmp.lawfulEqCmp 4 := fun h => by
  exact absurd ((@h BT _ compare _).eq_of_compare (a := false) (b := true) rfl) (by exact Bool.false_ne_true)

-- `Std.LawfulBEqOrd.equivBEq`, idx 3 (inst : Std.LawfulBEqOrd α): BFStd: Bool with == constantly false and the usual compare (TransCmp, LawfulEqCmp, not LawfulBEqCmp): == is not reflexive
theorem Std.LawfulBEqOrd.equivBEq.h3 : ¬ drop% Std.LawfulBEqOrd.equivBEq 3 := fun h => by
  ev (@h BFStd _ _ _).rfl (a := true)

-- `Std.LawfulBEqOrd.equivBEq`, idx 4 (inst : Std.TransOrd α): BF: Bool with == constantly false and cmp constantly .lt (LawfulBEqCmp, not reflexive): == is not reflexive
theorem Std.LawfulBEqOrd.equivBEq.h4 : ¬ drop% Std.LawfulBEqOrd.equivBEq 4 := fun h => by
  ev (@h BF _ _ _).rfl (a := true)

-- `Std.LawfulBEqOrd.lawfulBEq`, idx 3 (inst : Std.LawfulBEqOrd α): BFStd: Bool with == constantly false and the usual compare (TransCmp, LawfulEqCmp, not LawfulBEqCmp): == is not reflexive
theorem Std.LawfulBEqOrd.lawfulBEq.h3 : ¬ drop% Std.LawfulBEqOrd.lawfulBEq 3 := fun h => by
  ev (@h BFStd _ _ _).rfl (a := true)

-- `Std.LawfulBEqOrd.lawfulBEq`, idx 4 (inst : Std.LawfulEqOrd α): BT: Bool with == constantly true and cmp constantly .eq (LawfulBEqCmp, transitive, not LawfulEqCmp, == not lawful): false == true
theorem Std.LawfulBEqOrd.lawfulBEq.h4 : ¬ drop% Std.LawfulBEqOrd.lawfulBEq 4 := fun h => by
  exact absurd ((@h BT _ _ _).eq_of_beq (a := false) (b := true) rfl) (by exact Bool.false_ne_true)

-- `Std.LawfulBEqOrd.lawfulEqOrd`, idx 3 (inst : Std.LawfulBEqOrd α): AllEq: Bool with the usual == (LawfulBEq) and cmp constantly .eq (transitive, not LawfulBEqCmp): cmp false true = .eq
theorem Std.LawfulBEqOrd.lawfulEqOrd.h3 : ¬ drop% Std.LawfulBEqOrd.lawfulEqOrd 3 := fun h => by
  exact absurd ((@h AllEq _ _ _).eq_of_compare (a := false) (b := true) rfl) (by exact Bool.false_ne_true)

-- `Std.LawfulBEqOrd.lawfulEqOrd`, idx 4 (inst : LawfulBEq α): BT: Bool with == constantly true and cmp constantly .eq (LawfulBEqCmp, transitive, not LawfulEqCmp, == not lawful): cmp false true = .eq
theorem Std.LawfulBEqOrd.lawfulEqOrd.h4 : ¬ drop% Std.LawfulBEqOrd.lawfulEqOrd 4 := fun h => by
  exact absurd ((@h BT _ _ _).eq_of_compare (a := false) (b := true) rfl) (by exact Bool.false_ne_true)

-- `Std.LawfulBEqCmp.reflBEq`, idx 3 (inst : Std.LawfulBEqCmp cmp): BFStd: Bool with == constantly false and the usual compare (TransCmp, LawfulEqCmp, not LawfulBEqCmp): == is not reflexive
theorem Std.LawfulBEqCmp.reflBEq.h3 : ¬ drop% Std.LawfulBEqCmp.reflBEq 3 := fun h => by
  ev (@h BFStd _ compare _).rfl (a := true)

-- `Std.LawfulBEqCmp.reflBEq`, idx 4 (inst : Std.ReflCmp cmp): BF: Bool with == constantly false and cmp constantly .lt (LawfulBEqCmp, not reflexive): == is not reflexive
theorem Std.LawfulBEqCmp.reflBEq.h4 : ¬ drop% Std.LawfulBEqCmp.reflBEq 4 := fun h => by
  ev (@h BF _ compare _).rfl (a := true)

-- `Std.instLawfulBEqCmpOfLawfulEqCmpOfLawfulBEq`, idx 3 (inst : Std.LawfulEqCmp cmp): AllEq: Bool with the usual == (LawfulBEq) and cmp constantly .eq (transitive, not LawfulBEqCmp): cmp false true = .eq but (false == true) = false
theorem Std.instLawfulBEqCmpOfLawfulEqCmpOfLawfulBEq.h3 : ¬ drop% Std.instLawfulBEqCmpOfLawfulEqCmpOfLawfulBEq 3 := fun h => by
  ev (@h AllEq _ compare _).compare_eq_iff_beq (a := false) (b := true)

-- `Std.instLawfulBEqCmpOfLawfulEqCmpOfLawfulBEq`, idx 4 (inst : LawfulBEq α): BFStd: Bool with == constantly false and the usual compare (TransCmp, LawfulEqCmp, not LawfulBEqCmp): cmp true true = .eq but (true == true) = false
theorem Std.instLawfulBEqCmpOfLawfulEqCmpOfLawfulBEq.h4 : ¬ drop% Std.instLawfulBEqCmpOfLawfulEqCmpOfLawfulBEq 4 := fun h => by
  ev (@h BFStd _ compare _).compare_eq_iff_beq (a := true) (b := true)

-- `Std.instTransCmpCompareOnOfTransOrd`, idx 4 (inst : Std.TransOrd β): β = RPS (Ord from rps, not transitive), f = id: 0, 1, 2
theorem Std.instTransCmpCompareOnOfTransOrd.h4 : ¬ drop% Std.instTransCmpCompareOnOfTransOrd 4 := fun h => by
  ev (@h RPS RPS id _).isLE_trans (a := 0) (b := 1) (c := 2) (by decide) (by decide)

-- `Std.instOrientedCmpCompareOnOfOrientedOrd`, idx 4 (inst : Std.OrientedOrd β): β = OffGT (Ord from offGT, not oriented), f = id: false, true
theorem Std.instOrientedCmpCompareOnOfOrientedOrd.h4 : ¬ drop% Std.instOrientedCmpCompareOnOfOrientedOrd 4 := fun h => by
  ev (@h OffGT OffGT id _).eq_swap (a := false) (b := true)

-- `Std.instReflCmpCompareOnOfReflOrd`, idx 4 (inst : Std.ReflOrd β): β = CGT (Ord constantly .gt), f = id: true
theorem Std.instReflCmpCompareOnOfReflOrd.h4 : ¬ drop% Std.instReflCmpCompareOnOfReflOrd 4 := fun h => by
  ev (@h CGT CGT id _).compare_self (a := true)

-- `Std.instReflCmpCompareLex`, idx 3 (inst : Std.ReflCmp cmp₁): cmp₁ := cgt, cmp₂ := allEq on Bool: true
theorem Std.instReflCmpCompareLex.h3 : ¬ drop% Std.instReflCmpCompareLex 3 := fun h => by
  ev (@h Bool cgt allEq _).compare_self (a := true)

-- `Std.instReflCmpCompareLex`, idx 4 (inst : Std.ReflCmp cmp₂): cmp₁ := allEq, cmp₂ := cgt on Bool: true
theorem Std.instReflCmpCompareLex.h4 : ¬ drop% Std.instReflCmpCompareLex 4 := fun h => by
  ev (@h Bool allEq cgt _).compare_self (a := true)

-- `Std.instOrientedCmpCompareLex`, idx 3 (inst : Std.OrientedCmp cmp₁): cmp₁ := offGT, cmp₂ := allEq on Bool: false, true
theorem Std.instOrientedCmpCompareLex.h3 : ¬ drop% Std.instOrientedCmpCompareLex 3 := fun h => by
  ev (@h Bool offGT allEq _).eq_swap (a := false) (b := true)

-- `Std.instOrientedCmpCompareLex`, idx 4 (inst : Std.OrientedCmp cmp₂): cmp₁ := allEq, cmp₂ := offGT on Bool: false, true
theorem Std.instOrientedCmpCompareLex.h4 : ¬ drop% Std.instOrientedCmpCompareLex 4 := fun h => by
  ev (@h Bool allEq offGT _).eq_swap (a := false) (b := true)

-- `Std.instTransCmpCompareLex`, idx 3 (inst : Std.TransCmp cmp₁): cmp₁ := rps, cmp₂ := allEq on Fin 3: 0, 1, 2
theorem Std.instTransCmpCompareLex.h3 : ¬ drop% Std.instTransCmpCompareLex 3 := fun h => by
  ev (@h (Fin 3) rps allEq _).isLE_trans (a := 0) (b := 1) (c := 2) (by decide) (by decide)

-- `Std.instTransCmpCompareLex`, idx 4 (inst : Std.TransCmp cmp₂): cmp₁ := allEq, cmp₂ := rps on Fin 3: 0, 1, 2
theorem Std.instTransCmpCompareLex.h4 : ¬ drop% Std.instTransCmpCompareLex 4 := fun h => by
  ev (@h (Fin 3) allEq rps _).isLE_trans (a := 0) (b := 1) (c := 2) (by decide) (by decide)

-- `Std.instReflOrdProd`, idx 4 (inst : Std.ReflOrd α): α = CGT (compare constantly .gt), β = Bool: (true, true)
theorem Std.instReflOrdProd.h4 : ¬ drop% Std.instReflOrdProd 4 := fun h => by
  ev @Std.ReflCmp.compare_self _ _ (@h CGT Bool _ _ _) ((true : CGT), true)

-- `Std.instReflOrdProd`, idx 5 (inst : Std.ReflOrd β): α = Bool, β = CGT (compare constantly .gt): (true, true)
theorem Std.instReflOrdProd.h5 : ¬ drop% Std.instReflOrdProd 5 := fun h => by
  ev @Std.ReflCmp.compare_self _ _ (@h Bool CGT _ _ _) (true, (true : CGT))

-- `Std.instOrientedOrdProd`, idx 4 (inst : Std.OrientedOrd α): α = OffGT (not oriented), β = Bool: (false, true), (true, true)
theorem Std.instOrientedOrdProd.h4 : ¬ drop% Std.instOrientedOrdProd 4 := fun h => by
  ev @Std.OrientedCmp.eq_swap _ _ (@h OffGT Bool _ _ _) ((false : OffGT), true) ((true : OffGT), true)

-- `Std.instOrientedOrdProd`, idx 5 (inst : Std.OrientedOrd β): α = Bool, β = OffGT (not oriented): (true, false), (true, true)
theorem Std.instOrientedOrdProd.h5 : ¬ drop% Std.instOrientedOrdProd 5 := fun h => by
  ev @Std.OrientedCmp.eq_swap _ _ (@h Bool OffGT _ _ _) (true, (false : OffGT)) (true, (true : OffGT))

-- `Std.instTransOrdProd`, idx 4 (inst : Std.TransOrd α): α = RPS (not transitive), β = Bool: (0, true), (1, true), (2, true)
theorem Std.instTransOrdProd.h4 : ¬ drop% Std.instTransOrdProd 4 := fun h => by
  ev @Std.TransCmp.isLE_trans _ _ (@h RPS Bool _ _ _) ((0 : RPS), true) ((1 : RPS), true) ((2 : RPS), true) (by decide) (by decide)

-- `Std.instTransOrdProd`, idx 5 (inst : Std.TransOrd β): α = Bool, β = RPS (not transitive): (true, 0), (true, 1), (true, 2)
theorem Std.instTransOrdProd.h5 : ¬ drop% Std.instTransOrdProd 5 := fun h => by
  ev @Std.TransCmp.isLE_trans _ _ (@h Bool RPS _ _ _) (true, (0 : RPS)) (true, (1 : RPS)) (true, (2 : RPS)) (by decide) (by decide)

-- `Std.instLawfulEqOrdProd`, idx 4 (inst : Std.LawfulEqOrd α): α = AllEq (compare constantly .eq), β = Bool: (false, true), (true, true)
theorem Std.instLawfulEqOrdProd.h4 : ¬ drop% Std.instLawfulEqOrdProd 4 := fun h => by
  exact absurd (@Std.LawfulEqCmp.eq_of_compare _ _ (@h AllEq Bool _ _ _) ((false : AllEq), true) ((true : AllEq), true) rfl) (by decide)

-- `Std.instLawfulEqOrdProd`, idx 5 (inst : Std.LawfulEqOrd β): α = Bool, β = AllEq (compare constantly .eq): (true, false), (true, true)
theorem Std.instLawfulEqOrdProd.h5 : ¬ drop% Std.instLawfulEqOrdProd 5 := fun h => by
  exact absurd (@Std.LawfulEqCmp.eq_of_compare _ _ (@h Bool AllEq _ _ _) (true, (false : AllEq)) (true, (true : AllEq)) rfl) (by decide)

-- `List.instOrientedOrd`, idx 2 (inst : Std.OrientedOrd α): α = OffGT (Ord from offGT, not oriented); singletons [x] inherit the failure
theorem List.instOrientedOrd.h2 : ¬ drop% List.instOrientedOrd 2 := fun h => by
  ev (@h OffGT _).eq_swap (a := [(false : OffGT)]) (b := [(true : OffGT)])

-- `List.instLawfulEqOrd`, idx 2 (inst : Std.LawfulEqOrd α): α = AllEq (compare constantly .eq, transitive); singletons [x] inherit the failure
theorem List.instLawfulEqOrd.h2 : ¬ drop% List.instLawfulEqOrd 2 := fun h => by
  exact absurd ((@h AllEq _).eq_of_compare (a := [(false : AllEq)]) (b := [(true : AllEq)]) rfl) (by decide)

-- `List.instTransOrd`, idx 2 (inst : Std.TransOrd α): α = RPS (Ord from rps, oriented, not transitive); singletons [x] inherit the failure
theorem List.instTransOrd.h2 : ¬ drop% List.instTransOrd 2 := fun h => by
  ev (@h RPS _).isLE_trans (a := [(0 : RPS)]) (b := [(1 : RPS)]) (c := [(2 : RPS)]) (by decide) (by decide)

-- `List.instReflOrd`, idx 2 (inst : Std.ReflOrd α): α = CGT (compare constantly .gt); singletons [x] inherit the failure
theorem List.instReflOrd.h2 : ¬ drop% List.instReflOrd 2 := fun h => by
  ev (@h CGT _).compare_self (a := [(true : CGT)])

-- `List.instLawfulBEqOrd`, idx 3 (inst : Std.LawfulBEqOrd α): α = AllEq (usual ==, compare constantly .eq); singletons [x] inherit the failure
theorem List.instLawfulBEqOrd.h3 : ¬ drop% List.instLawfulBEqOrd 3 := fun h => by
  ev (@h AllEq _ _).compare_eq_iff_beq (a := [(false : AllEq)]) (b := [(true : AllEq)])

-- `List.instReflCmpCompareLex`, idx 2 (inst : Std.ReflCmp cmp): cmp := cgt on Bool; singletons [x] inherit the failure
theorem List.instReflCmpCompareLex.h2 : ¬ drop% List.instReflCmpCompareLex 2 := fun h => by
  ev (@h Bool cgt).compare_self (a := [true])

-- `List.instTransCmpCompareLex`, idx 2 (inst : Std.TransCmp cmp): cmp := rps on Fin 3; singletons [x] inherit the failure
theorem List.instTransCmpCompareLex.h2 : ¬ drop% List.instTransCmpCompareLex 2 := fun h => by
  ev (@h (Fin 3) rps).isLE_trans (a := [(0 : Fin 3)]) (b := [(1 : Fin 3)]) (c := [(2 : Fin 3)]) (by decide) (by decide)

-- `List.instLawfulEqCmpCompareLex`, idx 2 (inst : Std.LawfulEqCmp cmp): cmp := allEq on Bool; singletons [x] inherit the failure
theorem List.instLawfulEqCmpCompareLex.h2 : ¬ drop% List.instLawfulEqCmpCompareLex 2 := fun h => by
  exact absurd ((@h Bool allEq).eq_of_compare (a := [false]) (b := [true]) rfl) (by decide)

-- `List.instOrientedCmpCompareLex`, idx 2 (inst : Std.OrientedCmp cmp): cmp := offGT on Bool; singletons [x] inherit the failure
theorem List.instOrientedCmpCompareLex.h2 : ¬ drop% List.instOrientedCmpCompareLex 2 := fun h => by
  ev (@h Bool offGT).eq_swap (a := [false]) (b := [true])

-- `List.instLawfulBEqCmpCompareLex`, idx 3 (inst : Std.LawfulBEqCmp cmp): cmp := allEq on Bool with the usual ==; singletons [x] inherit the failure
theorem List.instLawfulBEqCmpCompareLex.h3 : ¬ drop% List.instLawfulBEqCmpCompareLex 3 := fun h => by
  ev (@h Bool allEq _).compare_eq_iff_beq (a := [false]) (b := [true])

-- `Array.instOrientedOrd`, idx 2 (inst : Std.OrientedOrd α): α = OffGT (Ord from offGT, not oriented); singletons #[x] inherit the failure
theorem Array.instOrientedOrd.h2 : ¬ drop% Array.instOrientedOrd 2 := fun h => by
  ev (@h OffGT _).eq_swap (a := #[(false : OffGT)]) (b := #[(true : OffGT)])

-- `Array.instLawfulEqOrd`, idx 2 (inst : Std.LawfulEqOrd α): α = AllEq (compare constantly .eq, transitive); singletons #[x] inherit the failure
theorem Array.instLawfulEqOrd.h2 : ¬ drop% Array.instLawfulEqOrd 2 := fun h => by
  exact absurd ((@h AllEq _).eq_of_compare (a := #[(false : AllEq)]) (b := #[(true : AllEq)]) rfl) (by decide)

-- `Array.instTransOrd`, idx 2 (inst : Std.TransOrd α): α = RPS (Ord from rps, oriented, not transitive); singletons #[x] inherit the failure
theorem Array.instTransOrd.h2 : ¬ drop% Array.instTransOrd 2 := fun h => by
  ev (@h RPS _).isLE_trans (a := #[(0 : RPS)]) (b := #[(1 : RPS)]) (c := #[(2 : RPS)]) (by decide) (by decide)

-- `Array.instReflOrd`, idx 2 (inst : Std.ReflOrd α): α = CGT (compare constantly .gt); singletons #[x] inherit the failure
theorem Array.instReflOrd.h2 : ¬ drop% Array.instReflOrd 2 := fun h => by
  ev (@h CGT _).compare_self (a := #[(true : CGT)])

-- `Array.instLawfulBEqOrd`, idx 3 (inst : Std.LawfulBEqOrd α): α = AllEq (usual ==, compare constantly .eq); singletons #[x] inherit the failure
theorem Array.instLawfulBEqOrd.h3 : ¬ drop% Array.instLawfulBEqOrd 3 := fun h => by
  ev (@h AllEq _ _).compare_eq_iff_beq (a := #[(false : AllEq)]) (b := #[(true : AllEq)])

-- `Array.instTransCmpCompareLex`, idx 2 (inst : Std.TransCmp cmp): cmp := rps on Fin 3; singletons #[x] inherit the failure
theorem Array.instTransCmpCompareLex.h2 : ¬ drop% Array.instTransCmpCompareLex 2 := fun h => by
  ev (@h (Fin 3) rps).isLE_trans (a := #[(0 : Fin 3)]) (b := #[(1 : Fin 3)]) (c := #[(2 : Fin 3)]) (by decide) (by decide)

-- `Array.instLawfulEqCmpCompareLex`, idx 2 (inst : Std.LawfulEqCmp cmp): cmp := allEq on Bool; singletons #[x] inherit the failure
theorem Array.instLawfulEqCmpCompareLex.h2 : ¬ drop% Array.instLawfulEqCmpCompareLex 2 := fun h => by
  exact absurd ((@h Bool allEq).eq_of_compare (a := #[false]) (b := #[true]) rfl) (by decide)

-- `Option.instOrientedOrd`, idx 2 (inst : Std.OrientedOrd α): α = OffGT (Ord from offGT, not oriented); some x inherit the failure
theorem Option.instOrientedOrd.h2 : ¬ drop% Option.instOrientedOrd 2 := fun h => by
  ev (@h OffGT _).eq_swap (a := some (false : OffGT)) (b := some (true : OffGT))

-- `Option.instLawfulEqOrd`, idx 2 (inst : Std.LawfulEqOrd α): α = AllEq (compare constantly .eq, transitive); some x inherit the failure
theorem Option.instLawfulEqOrd.h2 : ¬ drop% Option.instLawfulEqOrd 2 := fun h => by
  exact absurd ((@h AllEq _).eq_of_compare (a := some (false : AllEq)) (b := some (true : AllEq)) rfl) (by decide)

-- `Option.instTransOrd`, idx 2 (inst : Std.TransOrd α): α = RPS (Ord from rps, oriented, not transitive); some x inherit the failure
theorem Option.instTransOrd.h2 : ¬ drop% Option.instTransOrd 2 := fun h => by
  ev (@h RPS _).isLE_trans (a := some (0 : RPS)) (b := some (1 : RPS)) (c := some (2 : RPS)) (by decide) (by decide)

-- `Option.instReflOrd`, idx 2 (inst : Std.ReflOrd α): α = CGT (compare constantly .gt); some x inherit the failure
theorem Option.instReflOrd.h2 : ¬ drop% Option.instReflOrd 2 := fun h => by
  ev (@h CGT _).compare_self (a := some (true : CGT))

-- `Option.instLawfulBEqOrd`, idx 3 (inst : Std.LawfulBEqOrd α): α = AllEq (usual ==, compare constantly .eq); some x inherit the failure
theorem Option.instLawfulBEqOrd.h3 : ¬ drop% Option.instLawfulBEqOrd 3 := fun h => by
  ev (@h AllEq _ _).compare_eq_iff_beq (a := some (false : AllEq)) (b := some (true : AllEq))

-- `Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le`, idx 6 (antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y): LeAll: Bool with ≤ everywhere true, < empty (preorder, total, not_le; not antisymmetric): cmp false true = cmp true false = .gt
theorem Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le.h6 : ¬ drop% Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le 6 := fun h => by
  ev (@h LeAll _ _ _ _ _ (by decide) (by decide) (by decide)).eq_swap (a := false) (b := true)

-- `Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le`, idx 7 (trans : ∀ {x y z : α}, x ≤ y → y ≤ z → x ≤ z): Cyc: Fin 3 with a ≤ b ↔ a = b ∨ b = a + 1, a < b ↔ b = a + 1 (antisymmetric, total, not_le; not transitive): isLE_trans fails at 0, 1, 2
theorem Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le.h7 : ¬ drop% Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le 7 := fun h => by
  ev (@h Cyc _ _ _ _ _ (by decide) (by decide) (by decide)).isLE_trans (a := 0) (b := 1) (c := 2) (by decide) (by decide)

-- `Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le`, idx 8 (total : ∀ (x y : α), x ≤ y ∨ y ≤ x): LeEq: Bool with ≤ equality, < inequality (antisymmetric, transitive, not_le; not total): cmp false true = cmp true false = .lt
theorem Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le.h8 : ¬ drop% Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le 8 := fun h => by
  ev (@h LeEq _ _ _ _ _ (by decide) (by decide) (by decide)).eq_swap (a := false) (b := true)

-- `Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le`, idx 9 (not_le : ∀ {x y : α}, ¬x ≤ y ↔ y < x): LtNone: Bool with the usual ≤ and < empty: cmp false true = cmp true false = .gt
theorem Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le.h9 : ¬ drop% Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le 9 := fun h => by
  ev (@h LtNone _ _ _ _ _ (by decide) (by decide) (by decide)).eq_swap (a := false) (b := true)

-- `Std.TransOrd.compareOfLessAndEq_of_lt_trans_of_lt_iff`, idx 4 (lt_trans : ∀ {a b c : α}, a < b → b < c → a < c): Cyc: Fin 3 with a < b ↔ b = a + 1 (satisfies h, not transitive): isLE_trans fails at 0, 1, 2
theorem Std.TransOrd.compareOfLessAndEq_of_lt_trans_of_lt_iff.h4 : ¬ drop% Std.TransOrd.compareOfLessAndEq_of_lt_trans_of_lt_iff 4 := fun h => by
  ev (@h Cyc _ _ _ (by decide)).isLE_trans (a := 0) (b := 1) (c := 2) (by decide) (by decide)

-- `Std.TransOrd.compareOfLessAndEq_of_lt_trans_of_lt_iff`, idx 5 (h : ∀ (x y : α), x < y ↔ ¬y < x ∧ x ≠ y): LtNone: Bool with < empty (transitive): cmp false true = cmp true false = .gt
theorem Std.TransOrd.compareOfLessAndEq_of_lt_trans_of_lt_iff.h5 : ¬ drop% Std.TransOrd.compareOfLessAndEq_of_lt_trans_of_lt_iff 5 := fun h => by
  ev (@h LtNone _ _ _ (by decide)).eq_swap (a := false) (b := true)

-- `List.compareLex_flatMap_flatMap`, idx 4 (inst : Std.LawfulEqCmp cmp'): cmp' := allEq on Bool (not LawfulEqCmp), f a := if a then [true, true] else [false], cmp induced by hf; l₁ = [false, true], l₂ = [true, false]: the flatMaps have equal length (.eq), cmp false true = .lt
theorem List.compareLex_flatMap_flatMap.h4 : ¬ drop% List.compareLex_flatMap_flatMap 4 := fun h => by
  ev @h Bool _ Bool allEq (fun a : Bool => if a then [true, true] else [false]) (fun _ _ => rfl) (by decide) (by decide) [false, true] [true, false]

-- `List.compareLex_flatMap_flatMap`, idx 7 (hp : ∀ (a b : α), f a <+: f b → a = b): cmp' := compare on Bool, f a := if a then [false, false] else [false] (f false <+: f true), cmp induced by hf; l₁ = [false, false], l₂ = [true]
theorem List.compareLex_flatMap_flatMap.h7 : ¬ drop% List.compareLex_flatMap_flatMap 7 := fun h => by
  ev @h Bool _ Bool compare _ (fun a : Bool => if a then [false, false] else [false]) (fun _ _ => rfl) (by decide) [false, false] [true]

-- `List.compareLex_flatMap_flatMap`, idx 8 (hx : ∀ (a : α), f a ≠ []): α = Unit, f _ = [] (then hp holds), cmp' := compare on Bool, cmp constantly .eq; l₁ = [], l₂ = [()]
theorem List.compareLex_flatMap_flatMap.h8 : ¬ drop% List.compareLex_flatMap_flatMap 8 := fun h => by
  ev @h Unit (fun _ _ => .eq) Bool compare _ (fun _ => []) (fun _ _ => rfl) (fun _ _ _ => rfl) [] [()]

-- `List.compare_flatMap_flatMap`, idx 4 (inst : Std.LawfulEqOrd β): β = AllEq (compare constantly .eq, not LawfulEqOrd), α = Bool, f a := if a then [true, true] else [false]; l₁ = [false, true], l₂ = [true, false]
theorem List.compare_flatMap_flatMap.h4 : ¬ drop% List.compare_flatMap_flatMap 4 := fun h => by
  ev @h Bool _ AllEq _ (fun a : Bool => if a then [(true : AllEq), true] else [false]) (by decide) (by decide) (by decide) [false, true] [true, false]

-- `List.compare_flatMap_flatMap`, idx 7 (hp : ∀ (a b : α), f a <+: f b → a = b): α = β = Bool, f a := if a then [false, false] else [false] (f false <+: f true); l₁ = [false, false], l₂ = [true]
theorem List.compare_flatMap_flatMap.h7 : ¬ drop% List.compare_flatMap_flatMap 7 := fun h => by
  ev @h Bool _ Bool _ _ (fun a : Bool => if a then [false, false] else [false]) (by decide) (by decide) [false, false] [true]

-- `List.compare_flatMap_flatMap`, idx 8 (hx : ∀ (a : α), f a ≠ []): α = Unit (compare constantly .eq), f _ = []; l₁ = [], l₂ = [()]
theorem List.compare_flatMap_flatMap.h8 : ¬ drop% List.compare_flatMap_flatMap 8 := fun h => by
  ev @h Unit ⟨fun _ _ => .eq⟩ Bool _ _ (fun _ => []) (fun _ _ => rfl) (fun _ _ _ => rfl) [] [()]

-- `Array.compareLex_flatMap_flatMap`, idx 4 (inst : Std.LawfulEqCmp cmp'): cmp' := allEq on Bool (not LawfulEqCmp), f a := if a then #[true, true] else #[false], cmp induced by hf; xs = #[false, true], ys = #[true, false]
theorem Array.compareLex_flatMap_flatMap.h4 : ¬ drop% Array.compareLex_flatMap_flatMap 4 := fun h => by
  ev @h Bool _ Bool allEq (fun a : Bool => if a then #[true, true] else #[false]) (fun _ _ => rfl) hpA1 (by decide) #[false, true] #[true, false]

-- `Array.compareLex_flatMap_flatMap`, idx 7 (hp : ∀ (a b : α) (zs : Array β), f a ++ zs = f b → a = b): cmp' := compare on Bool, f a := if a then #[false, false] else #[false] (f false ++ #[false] = f true), cmp induced by hf; xs = #[false, false], ys = #[true]
theorem Array.compareLex_flatMap_flatMap.h7 : ¬ drop% Array.compareLex_flatMap_flatMap 7 := fun h => by
  ev @h Bool _ Bool compare _ (fun a : Bool => if a then #[false, false] else #[false]) (fun _ _ => rfl) (by decide) #[false, false] #[true]

-- `Array.compareLex_flatMap_flatMap`, idx 8 (hx : ∀ (a : α), f a ≠ #[]): α = Unit, f _ = #[] (then hp holds), cmp' := compare on Bool, cmp constantly .eq; xs = #[], ys = #[()]
theorem Array.compareLex_flatMap_flatMap.h8 : ¬ drop% Array.compareLex_flatMap_flatMap 8 := fun h => by
  ev @h Unit (fun _ _ => .eq) Bool compare _ (fun _ => #[]) (fun _ _ => rfl) (fun _ _ _ _ => rfl) #[] #[()]

-- `Array.compare_flatMap_flatMap`, idx 4 (inst : Std.LawfulEqOrd β): β = AllEq (compare constantly .eq, not LawfulEqOrd), α = Bool, f a := if a then #[true, true] else #[false]; xs = #[false, true], ys = #[true, false]
theorem Array.compare_flatMap_flatMap.h4 : ¬ drop% Array.compare_flatMap_flatMap 4 := fun h => by
  ev @h Bool _ AllEq _ (fun a : Bool => if a then #[(true : AllEq), true] else #[false]) (by decide) hpA1 (by decide) #[false, true] #[true, false]

-- `Array.compare_flatMap_flatMap`, idx 7 (hp : ∀ (a b : α) (zs : Array β), f a ++ zs = f b → a = b): α = β = Bool, f a := if a then #[false, false] else #[false] (f false ++ #[false] = f true); xs = #[false, false], ys = #[true]
theorem Array.compare_flatMap_flatMap.h7 : ¬ drop% Array.compare_flatMap_flatMap 7 := fun h => by
  ev @h Bool _ Bool _ _ (fun a : Bool => if a then #[false, false] else #[false]) (by decide) (by decide) #[false, false] #[true]

-- `Array.compare_flatMap_flatMap`, idx 8 (hx : ∀ (a : α), f a ≠ #[]): α = Unit (compare constantly .eq), f _ = #[]; xs = #[], ys = #[()]
theorem Array.compare_flatMap_flatMap.h8 : ¬ drop% Array.compare_flatMap_flatMap 8 := fun h => by
  ev @h Unit ⟨fun _ _ => .eq⟩ Bool _ _ (fun _ => #[]) (fun _ _ => rfl) (fun _ _ _ _ => rfl) #[] #[()]

-- `Array.compare_map_map`, idx 5 (hf : ∀ (a b : α), compare (f a) (f b) = compare a b): α = β = Bool, f constantly false; xs = #[false], ys = #[true]
theorem Array.compare_map_map.h5 : ¬ drop% Array.compare_map_map 5 := fun h => by
  have := @h Bool _ Bool _ (fun _ => false) #[false] #[true]; revert this; decide +kernel
end OrderOrdHand
