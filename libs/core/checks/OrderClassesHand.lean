import Lean

/-!
Hand pass over cluster `OrderClasses` (hand7): the 59 unresolved hypotheses of
`Init.Data.Order.Classes`, `Factories`, `FactoriesExtra`, `Opposite` and `PackageFactories`
(order-class instance hypotheses, explicit `∀`-law and `autoParam` hypotheses of the instance
factories). For hypothesis `hᵢ` of theorem `T` this file proves `¬T'`.

59 necessary, 0 removable, 0 independent.

`Trans` is not a Prop, so the `Trans` models are `def`s. Witnesses are written `.tt`/`.ff`
(`B.tt : B := true`), since instance search does not unify a model type with `Bool`.

Every theorem here builds a class instance whose fields are (or follow directly from) the dropped
law, so each refutation instantiates the hypothetical `T'` at a model that satisfies the remaining
hypotheses, takes the field that fails and evaluates it. `drop% T i` elaborates to `T'` read off the
library; `check_hand.py` compares it with its own construction. An `autoParam` binder is an ordinary
Prop parameter of `T'`, so it is supplied explicitly.

Models (each a copy of `Bool` or `Unit` with its own instances, each breaking one law):
* `B`: `Bool` with the usual `≤`/`<` (a lawful linear order); combined with `min := (· || ·)` or
  `max := (· && ·)` (which still satisfy `min_eq_or`/`max_eq_or` but are the wrong lattice
  operation), or with a projection `min a b := b` (fails `min_le_left`).
* `BT`: `Bool` with `≤` always true (preorder, total, not antisymmetric); with `min a b := !a`
  (fails `min_eq_or`).
* `BE`: `Bool` with `≤` equality (partial order, not total).
* `BF`: `Bool` with `<` always false (asymmetric, `¬<` transitive, not trichotomous).
* `UF`: `Unit` with `≤` false (transitive, antisymmetric, not reflexive, not total).
* `UT`: `Unit` with `≤`/`<` true (`<` reflexive, so not asymmetric/irreflexive).
* `UO`: `Unit` with `≤` true, `compare` constantly `.lt` (not oriented) and `==` false.
* `BTO`: `Bool` with `≤` true and `compare` constantly `.gt` (not lawful for `≤`).

Run with the lean4 repo's stage1 binary: `lean checks/OrderClassesHand.lean`.
-/

set_option linter.unusedVariables false
set_option warn.classDefReducibility false

open Lean Meta Elab Term in
/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library, with
all universe parameters set to `0` (the models here live in `Type`). -/
elab "drop% " T:ident i:num : term => do
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

namespace OrderClassesHand

/-! ## Models -/

/-- `Bool` with the usual `≤` and `<`. -/
def B := Bool
instance : LE B := ⟨fun a b => ((!a || b : Bool)) = true⟩
instance : LT B := ⟨fun a b => ((!a && b : Bool)) = true⟩
instance : DecidableLE B := fun a b => inferInstanceAs (Decidable (((!a || b : Bool)) = true))
instance : DecidableLT B := fun a b => inferInstanceAs (Decidable (((!a && b : Bool)) = true))
instance : DecidableEq B := inferInstanceAs (DecidableEq Bool)
def B.ff : B := false
def B.tt : B := true
instance (p : B → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .ff ∧ p .tt)
    ⟨fun ⟨h₁, h₂⟩ x => by cases x <;> assumption, fun h => ⟨h _, h _⟩⟩
def B.trans : Trans (α := B) (· ≤ ·) (· ≤ ·) (· ≤ ·) :=
  ⟨fun {a b c} => by revert a b c; decide⟩

/-- `Bool` with `≤` always true. -/
def BT := Bool
instance : LE BT := ⟨fun _ _ => True⟩
instance : DecidableLE BT := fun _ _ => inferInstanceAs (Decidable True)
instance : DecidableEq BT := inferInstanceAs (DecidableEq Bool)
def BT.ff : BT := false
def BT.tt : BT := true
instance (p : BT → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .ff ∧ p .tt)
    ⟨fun ⟨h₁, h₂⟩ x => by cases x <;> assumption, fun h => ⟨h _, h _⟩⟩
def BT.trans : Trans (α := BT) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨fun _ _ => trivial⟩
theorem BT.total : Std.Total (α := BT) (· ≤ ·) := ⟨fun _ _ => Or.inl trivial⟩
theorem BT.refl : Std.Refl (α := BT) (· ≤ ·) := ⟨fun _ => trivial⟩

/-- `Bool` with `≤` equality. -/
def BE := Bool
instance : LE BE := ⟨fun a b => a = b⟩
instance : DecidableEq BE := inferInstanceAs (DecidableEq Bool)
instance : DecidableLE BE := fun a b => inferInstanceAs (Decidable (a = b))
def BE.ff : BE := false
def BE.tt : BE := true
def BE.trans : Trans (α := BE) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨fun h1 h2 => Eq.trans h1 h2⟩
theorem BE.antisymm : Std.Antisymm (α := BE) (· ≤ ·) := ⟨fun _ _ h _ => h⟩

/-- `Bool` with `<` always false. -/
def BF := Bool
instance : LT BF := ⟨fun _ _ => False⟩
instance : DecidableLT BF := fun _ _ => inferInstanceAs (Decidable False)
instance : DecidableEq BF := inferInstanceAs (DecidableEq Bool)
def BF.ff : BF := false
def BF.tt : BF := true
instance (p : BF → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .ff ∧ p .tt)
    ⟨fun ⟨h₁, h₂⟩ x => by cases x <;> assumption, fun h => ⟨h _, h _⟩⟩
theorem BF.asymm : Std.Asymm (α := BF) (· < ·) := ⟨fun _ _ h _ => h⟩
def BF.notTrans : Trans (α := BF) (¬ · < ·) (¬ · < ·) (¬ · < ·) := ⟨fun _ _ h => h⟩

/-- `Unit` with `≤` always false. -/
def UF := Unit
instance : LE UF := ⟨fun _ _ => False⟩
def UF.trans : Trans (α := UF) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨fun h _ => h⟩
theorem UF.antisymm : Std.Antisymm (α := UF) (· ≤ ·) := ⟨fun _ _ h _ => h.elim⟩
instance : DecidableLE UF := fun _ _ => inferInstanceAs (Decidable False)

/-- `Unit` with `≤` and `<` always true. -/
def UT := Unit
instance : LE UT := ⟨fun _ _ => True⟩
instance : LT UT := ⟨fun _ _ => True⟩
def UT.notTrans : Trans (α := UT) (¬ · < ·) (¬ · < ·) (¬ · < ·) := ⟨fun h _ => absurd trivial h⟩
theorem UT.trich : Std.Trichotomous (α := UT) (· < ·) := ⟨fun _ _ h _ => absurd trivial h⟩

/-- `Unit` with `≤` true, `compare` constantly `.lt`, `==` false. -/
def UO := Unit
instance : LE UO := ⟨fun _ _ => True⟩
instance : Ord UO := ⟨fun _ _ => .lt⟩
instance : BEq UO := ⟨fun _ _ => false⟩

/-- `Bool` with `≤` true and `compare` constantly `.gt`. -/
def BTO := Bool
instance : LE BTO := ⟨fun _ _ => True⟩
instance : Ord BTO := ⟨fun _ _ => .gt⟩
instance : DecidableEq BTO := inferInstanceAs (DecidableEq Bool)
def BTO.ff : BTO := false
def BTO.tt : BTO := true

/-! ## `Init.Data.Order.Factories` -/

-- `Std.LawfulOrderMax.of_le_max`, idx 4 (`left_le_max`): `B` with `max a b := b`;
-- `max true false = false ≤ false` but `¬ true ≤ false`.
theorem of_le_max.h4 : ¬ drop% Std.LawfulOrderMax.of_le_max 4 := fun h =>
  absurd ((@h B ⟨fun _ b => b⟩ inferInstance B.trans (by decide) (by decide)).max_le_iff .tt .ff .ff)
    (by decide)

-- `Std.LawfulOrderMax.of_le_max`, idx 5 (`right_le_max`): `B` with `max a b := a`.
theorem of_le_max.h5 : ¬ drop% Std.LawfulOrderMax.of_le_max 5 := fun h =>
  absurd ((@h B ⟨fun a _ => a⟩ inferInstance B.trans (by decide) (by decide)).max_le_iff .ff .tt .ff)
    (by decide)

-- `Std.LawfulOrderMax.of_le_max`, idx 6 (`max_eq_or`): `BT` with `max a b := !a`.
theorem of_le_max.h6 : ¬ drop% Std.LawfulOrderMax.of_le_max 6 := fun h =>
  absurd ((@h BT ⟨fun a _ => !a⟩ inferInstance BT.trans (by decide) (by decide)).max_eq_or .tt .tt)
    (by decide)

-- `Std.LawfulOrderMin.of_min_le`, idx 4 (`min_le_left`): `B` with `min a b := b`.
theorem of_min_le.h4 : ¬ drop% Std.LawfulOrderMin.of_min_le 4 := fun h =>
  absurd ((@h B ⟨fun _ b => b⟩ inferInstance B.trans (by decide) (by decide)).le_min_iff .tt .ff .tt)
    (by decide)

-- `Std.LawfulOrderMin.of_min_le`, idx 5 (`min_le_right`): `B` with `min a b := a`.
theorem of_min_le.h5 : ¬ drop% Std.LawfulOrderMin.of_min_le 5 := fun h =>
  absurd ((@h B ⟨fun a _ => a⟩ inferInstance B.trans (by decide) (by decide)).le_min_iff .tt .tt .ff)
    (by decide)

-- `Std.LawfulOrderMin.of_min_le`, idx 6 (`min_eq_or`): `BT` with `min a b := !a`.
theorem of_min_le.h6 : ¬ drop% Std.LawfulOrderMin.of_min_le 6 := fun h =>
  absurd ((@h BT ⟨fun a _ => !a⟩ inferInstance BT.trans (by decide) (by decide)).min_eq_or .tt .tt)
    (by decide)

-- `Std.IsPreorder.of_le`, idx 2 (`le_refl`): `UF` (`≤` false, vacuously transitive).
theorem IsPreorder.of_le.h2 : ¬ drop% Std.IsPreorder.of_le 2 := fun h =>
  (@h UF inferInstance UF.trans).le_refl ()

-- `Std.IsLinearPreorder.of_le`, idx 3 (`le_total`): `UF`.
theorem IsLinearPreorder.of_le.h3 : ¬ drop% Std.IsLinearPreorder.of_le 3 := fun h =>
  ((@h UF inferInstance UF.trans).le_total () ()).elim id id

-- `Std.IsPartialOrder.of_le`, idx 2 (`le_refl`): `UF`.
theorem IsPartialOrder.of_le.h2 : ¬ drop% Std.IsPartialOrder.of_le 2 := fun h =>
  (@h UF inferInstance UF.antisymm UF.trans).le_refl ()

-- `Std.IsPartialOrder.of_le`, idx 3 (`le_antisymm`): `BT` (`≤` true); `true ≤ false ≤ true`.
theorem IsPartialOrder.of_le.h3 : ¬ drop% Std.IsPartialOrder.of_le 3 := fun h =>
  absurd ((@h BT inferInstance BT.refl BT.trans).le_antisymm .tt .ff trivial trivial) (by decide)

-- `Std.IsLinearOrder.of_le`, idx 2 (`le_antisymm`): `BT`.
theorem IsLinearOrder.of_le.h2 : ¬ drop% Std.IsLinearOrder.of_le 2 := fun h =>
  absurd ((@h BT inferInstance BT.trans BT.total).le_antisymm .tt .ff trivial trivial) (by decide)

-- `Std.IsLinearOrder.of_le`, idx 4 (`le_total`): `BE` (`≤` is `=`); `true`, `false` incomparable.
theorem IsLinearOrder.of_le.h4 : ¬ drop% Std.IsLinearOrder.of_le 4 := fun h =>
  absurd ((@h BE inferInstance BE.antisymm BE.trans).le_total .tt .ff) (by decide)

-- `Std.LawfulOrderLT.of_le`, idx 3 (`lt_iff`): `UT` (`<` and `≤` true).
theorem LawfulOrderLT.of_le.h3 : ¬ drop% Std.LawfulOrderLT.of_le 3 := fun h =>
  (((@h UT inferInstance inferInstance).lt_iff () ()).mp trivial).2 trivial

-- `Std.LawfulOrderBEq.of_le`, idx 3 (`beq_iff`): `UO` (`==` false, `≤` true).
theorem LawfulOrderBEq.of_le.h3 : ¬ drop% Std.LawfulOrderBEq.of_le 3 := fun h =>
  Bool.noConfusion (((@h UO inferInstance inferInstance).beq_iff_le_and_ge () ()).mpr ⟨trivial, trivial⟩)

-- `Std.LawfulOrderInf.of_le`, idx 3 (`le_min_iff`): `B` with `min := (· || ·)`.
theorem LawfulOrderInf.of_le.h3 : ¬ drop% Std.LawfulOrderInf.of_le 3 := fun h =>
  absurd ((@h B ⟨fun a b => a || b⟩ inferInstance).le_min_iff .tt .tt .ff) (by decide)

-- `Std.LawfulOrderMin.of_le_min_iff`, idx 3 (`le_min_iff`): `B` with `min := (· || ·)`.
theorem of_le_min_iff.h3 : ¬ drop% Std.LawfulOrderMin.of_le_min_iff 3 := fun h =>
  absurd ((@h B ⟨fun a b => a || b⟩ inferInstance (by decide)).le_min_iff .tt .tt .ff) (by decide)

-- `Std.LawfulOrderMin.of_le_min_iff`, idx 4 (`min_eq_or`): `BT` with `min a b := !a`.
theorem of_le_min_iff.h4 : ¬ drop% Std.LawfulOrderMin.of_le_min_iff 4 := fun h =>
  absurd ((@h BT ⟨fun a _ => !a⟩ inferInstance (by decide)).min_eq_or .tt .tt) (by decide)

-- `Std.LawfulOrderSup.of_le`, idx 3 (`max_le_iff`): `B` with `max := (· && ·)`.
theorem LawfulOrderSup.of_le.h3 : ¬ drop% Std.LawfulOrderSup.of_le 3 := fun h =>
  absurd ((@h B ⟨fun a b => a && b⟩ inferInstance).max_le_iff .tt .ff .ff) (by decide)

-- `Std.LawfulOrderMax.of_max_le_iff`, idx 3 (`max_le_iff`): `B` with `max := (· && ·)`.
theorem of_max_le_iff.h3 : ¬ drop% Std.LawfulOrderMax.of_max_le_iff 3 := fun h =>
  absurd ((@h B ⟨fun a b => a && b⟩ inferInstance (by decide)).max_le_iff .tt .ff .ff) (by decide)

-- `Std.LawfulOrderLT.of_lt`, idx 2 (`i : Asymm (· < ·)`): `UT` (`<` reflexive); `LE.ofLT` makes
-- `() < ()` but not `() ≤ ()`.
theorem LawfulOrderLT.of_lt.h2 : ¬ drop% Std.LawfulOrderLT.of_lt 2 := fun h =>
  (((@h UT inferInstance).lt_iff () ()).mp trivial).1 trivial

-- `Std.IsLinearPreorder.of_lt`, idx 2 (`lt_asymm`): `UT`; `LE.ofLT` is not reflexive.
theorem IsLinearPreorder.of_lt.h2 : ¬ drop% Std.IsLinearPreorder.of_lt 2 := fun h =>
  (@h UT inferInstance UT.notTrans).le_refl () trivial

-- `Std.instIsLinearPreorderOfAsymmOfTransNotLt`, idx 2 (`Asymm (· < ·)`): `UT`.
theorem instIsLinearPreorderOfAsymmOfTransNotLt.h2 :
    ¬ drop% Std.instIsLinearPreorderOfAsymmOfTransNotLt 2 := fun h =>
  (@h UT inferInstance UT.notTrans).le_refl () trivial

-- `Std.IsLinearOrder.of_lt`, idx 2 (`lt_asymm`): `UT`.
theorem IsLinearOrder.of_lt.h2 : ¬ drop% Std.IsLinearOrder.of_lt 2 := fun h =>
  (@h UT inferInstance UT.notTrans UT.trich).le_refl () trivial

-- `Std.IsLinearOrder.of_lt`, idx 4 (`lt_trichotomous`): `BF` (`<` false, so `LE.ofLT` is true and
-- not antisymmetric).
theorem IsLinearOrder.of_lt.h4 : ¬ drop% Std.IsLinearOrder.of_lt 4 := fun h =>
  absurd ((@h BF inferInstance BF.asymm BF.notTrans).le_antisymm .tt .ff id id) (by decide)

-- `Std.instIsLinearOrderOfAsymmOfTransNotOfTrichotomousLt`, idx 2 (`Asymm (· < ·)`): `UT`.
theorem instIsLinearOrderOfAsymm.h2 :
    ¬ drop% Std.instIsLinearOrderOfAsymmOfTransNotOfTrichotomousLt 2 := fun h =>
  (@h UT inferInstance UT.notTrans UT.trich).le_refl () trivial

-- `Std.instIsLinearOrderOfAsymmOfTransNotOfTrichotomousLt`, idx 4 (`Trichotomous (· < ·)`): `BF`.
theorem instIsLinearOrderOfAsymm.h4 :
    ¬ drop% Std.instIsLinearOrderOfAsymmOfTransNotOfTrichotomousLt 4 := fun h =>
  absurd ((@h BF inferInstance BF.asymm BF.notTrans).le_antisymm .tt .ff id id) (by decide)

-- `Std.LawfulOrderInf.of_lt`, idx 3 (`min_lt_iff`): `B` with `min := (· || ·)`.
theorem LawfulOrderInf.of_lt.h3 : ¬ drop% Std.LawfulOrderInf.of_lt 3 := fun h =>
  absurd ((@h B ⟨fun a b => a || b⟩ inferInstance).le_min_iff .tt .tt .ff) (by decide)

-- `Std.LawfulOrderMin.of_lt`, idx 3 (`min_lt_iff`): `B` with `min := (· || ·)`.
theorem LawfulOrderMin.of_lt.h3 : ¬ drop% Std.LawfulOrderMin.of_lt 3 := fun h =>
  absurd ((@h B ⟨fun a b => a || b⟩ inferInstance (by decide)).le_min_iff .tt .tt .ff) (by decide)

-- `Std.LawfulOrderMin.of_lt`, idx 4 (`min_eq_or`): `BF` with `min a b := !a`.
theorem LawfulOrderMin.of_lt.h4 : ¬ drop% Std.LawfulOrderMin.of_lt 4 := fun h =>
  absurd ((@h BF ⟨fun a _ => !a⟩ inferInstance (by decide)).min_eq_or .tt .tt) (by decide)

-- `Std.LawfulOrderSup.of_lt`, idx 3 (`lt_max_iff`): `B` with `max := (· && ·)`.
theorem LawfulOrderSup.of_lt.h3 : ¬ drop% Std.LawfulOrderSup.of_lt 3 := fun h =>
  absurd ((@h B ⟨fun a b => a && b⟩ inferInstance).max_le_iff .tt .ff .ff) (by decide)

-- `Std.LawfulOrderMax.of_lt`, idx 3 (`lt_max_iff`): `B` with `max := (· && ·)`.
theorem LawfulOrderMax.of_lt.h3 : ¬ drop% Std.LawfulOrderMax.of_lt 3 := fun h =>
  absurd ((@h B ⟨fun a b => a && b⟩ inferInstance (by decide)).max_le_iff .tt .ff .ff) (by decide)

-- `Std.LawfulOrderMax.of_lt`, idx 4 (`max_eq_or`): `BF` with `max a b := !a`.
theorem LawfulOrderMax.of_lt.h4 : ¬ drop% Std.LawfulOrderMax.of_lt 4 := fun h =>
  absurd ((@h BF ⟨fun a _ => !a⟩ inferInstance (by decide)).max_eq_or .tt .tt) (by decide)

/-! ## `Init.Data.Order.Classes` (parent projections) -/

-- `Std.IsPartialOrder.toIsPreorder`, idx 2 (`self`): `UF`.
theorem IsPartialOrder.toIsPreorder.h2 : ¬ drop% Std.IsPartialOrder.toIsPreorder 2 := fun h =>
  (@h UF inferInstance).le_refl ()

-- `Std.IsLinearOrder.toIsPartialOrder`, idx 2 (`self`): `UF`.
theorem IsLinearOrder.toIsPartialOrder.h2 : ¬ drop% Std.IsLinearOrder.toIsPartialOrder 2 := fun h =>
  (@h UF inferInstance).le_refl ()

-- `Std.IsLinearOrder.toIsLinearPreorder`, idx 2 (`self`): `UF`.
theorem IsLinearOrder.toIsLinearPreorder.h2 : ¬ drop% Std.IsLinearOrder.toIsLinearPreorder 2 :=
  fun h => (@h UF inferInstance).le_refl ()

-- `Std.LawfulOrderMin.toMinEqOr`, idx 3 (`self`): `BT` with `min a b := !a`.
theorem LawfulOrderMin.toMinEqOr.h3 : ¬ drop% Std.LawfulOrderMin.toMinEqOr 3 := fun h =>
  absurd ((@h BT ⟨fun a _ => !a⟩ inferInstance).min_eq_or .tt .tt) (by decide)

-- `Std.LawfulOrderMax.toMaxEqOr`, idx 3 (`self`): `BT` with `max a b := !a`.
theorem LawfulOrderMax.toMaxEqOr.h3 : ¬ drop% Std.LawfulOrderMax.toMaxEqOr 3 := fun h =>
  absurd ((@h BT ⟨fun a _ => !a⟩ inferInstance).max_eq_or .tt .tt) (by decide)

/-! ## `Init.Data.Order.FactoriesExtra` and `PackageFactories` -/

-- `Std.instLawfulOrderOrd_ofOrd`, idx 2 (`OrientedOrd α`): `UO` (`compare` constantly `Ordering.lt`);
-- `(compare () ()).isGE = false` but `LE.ofOrd` gives `() ≤ ()`.
theorem instLawfulOrderOrd_ofOrd.h2 : ¬ drop% Std.instLawfulOrderOrd_ofOrd 2 := fun h =>
  Bool.noConfusion (((@h UO inferInstance).isGE_compare () ()).mpr rfl)

-- `Std.instLawfulOrderLT_ofOrd`, idx 3 (`LawfulOrderOrd α`): `UO`; `LT.ofOrd` gives `() < ()`.
theorem instLawfulOrderLT_ofOrd.h3 : ¬ drop% Std.instLawfulOrderLT_ofOrd 3 := fun h =>
  (((@h UO inferInstance inferInstance).lt_iff () ()).mp rfl).2 trivial

-- `Std.instLawfulOrderBEq_ofOrd`, idx 3 (`LawfulOrderOrd α`): `UO`; `BEq.ofOrd` gives `() != ()`.
theorem instLawfulOrderBEq_ofOrd.h3 : ¬ drop% Std.instLawfulOrderBEq_ofOrd 3 := fun h =>
  Bool.noConfusion (((@h UO inferInstance inferInstance).beq_iff_le_and_ge () ()).mpr ⟨trivial, trivial⟩)

-- `Std.FactoryInstances.instLawfulOrderOrdOfDecidableLE`, idx 3 (`Total (· ≤ ·)`): `UF`;
-- `compare () () = .gt`, which `isGE` although `¬ () ≤ ()`.
theorem instLawfulOrderOrdOfDecidableLE.h3 :
    ¬ drop% Std.FactoryInstances.instLawfulOrderOrdOfDecidableLE 3 := fun h =>
  ((@h UF inferInstance inferInstance).isGE_compare () ()).mp rfl

-- `Std.OrientedCmp.of_gt_iff_lt`, idx 2 (`h`): `cmp` constantly `Ordering.lt` on `Unit`.
theorem OrientedCmp.of_gt_iff_lt.h2 : ¬ drop% Std.OrientedCmp.of_gt_iff_lt 2 := fun h =>
  Ordering.noConfusion ((@h Unit fun _ _ => .lt).eq_swap (a := ()) (b := ()))

-- `Std.FactoryInstances.instLawfulOrderLeftLeaningMinOfOrd`, idx 3 (`LawfulOrderOrd α`): `BTO`
-- (`≤` true, `compare` constantly `Ordering.gt`); `min true false = false` although `true ≤ false`.
theorem instLawfulOrderLeftLeaningMinOfOrd.h3 :
    ¬ drop% Std.FactoryInstances.instLawfulOrderLeftLeaningMinOfOrd 3 := fun h =>
  absurd ((@h BTO inferInstance inferInstance).min_eq_left .tt .ff trivial) (by decide)

-- `Std.FactoryInstances.instLawfulOrderLeftLeaningMaxOfOrd`, idx 3 (`LawfulOrderOrd α`): `BTO`;
-- `max true false = false` although `false ≤ true`.
theorem instLawfulOrderLeftLeaningMaxOfOrd.h3 :
    ¬ drop% Std.FactoryInstances.instLawfulOrderLeftLeaningMaxOfOrd 3 := fun h =>
  absurd ((@h BTO inferInstance inferInstance).max_eq_left .tt .ff trivial) (by decide)

/-! ## `Init.Data.Order.Opposite` -/

-- `Std.OppositeOrderInstances.instLESymmOpposite`, idx 2 (`Symm (· ≤ ·)`): `B`; the opposite of
-- the usual order is not symmetric.
theorem instLESymmOpposite.h2 : ¬ drop% Std.OppositeOrderInstances.instLESymmOpposite 2 := fun h => by
  have := (@h B inferInstance).symm .tt .ff
  unfold LE.opposite at this
  revert this; decide

-- `Std.OppositeOrderInstances.instLEAntisymmOpposite`, idx 2 (`Antisymm (· ≤ ·)`): `BT`.
theorem instLEAntisymmOpposite.h2 : ¬ drop% Std.OppositeOrderInstances.instLEAntisymmOpposite 2 :=
  fun h => by
    have := (@h BT inferInstance).antisymm .tt .ff
    unfold LE.opposite at this
    exact absurd (this trivial trivial) (by decide)

-- `Std.OppositeOrderInstances.instLEAsymmOpposite`, idx 2 (`Asymm (· ≤ ·)`): `UT`.
theorem instLEAsymmOpposite.h2 : ¬ drop% Std.OppositeOrderInstances.instLEAsymmOpposite 2 :=
  fun h => by
    have := (@h UT inferInstance).asymm () ()
    unfold LE.opposite at this
    exact this trivial trivial

-- `Std.OppositeOrderInstances.instLETotalOpposite`, idx 2 (`Total (· ≤ ·)`): `UF`.
theorem instLETotalOpposite.h2 : ¬ drop% Std.OppositeOrderInstances.instLETotalOpposite 2 :=
  fun h => by
    have := (@h UF inferInstance).total () ()
    unfold LE.opposite at this
    exact this.elim id id

-- `Std.OppositeOrderInstances.instLEIrreflOpposite`, idx 2 (`Irrefl (· ≤ ·)`): `UT`.
theorem instLEIrreflOpposite.h2 : ¬ drop% Std.OppositeOrderInstances.instLEIrreflOpposite 2 :=
  fun h => by
    have := (@h UT inferInstance).irrefl ()
    unfold LE.opposite at this
    exact this trivial

-- `Std.OppositeOrderInstances.instIsPreorderOpposite`, idx 2 (`IsPreorder α`): `UF`.
theorem instIsPreorderOpposite.h2 : ¬ drop% Std.OppositeOrderInstances.instIsPreorderOpposite 2 :=
  fun h => by
    have := (@h UF inferInstance).le_refl ()
    unfold LE.opposite at this
    exact this

-- `Std.OppositeOrderInstances.instIsPartialOrderOpposite`, idx 2 (`IsPartialOrder α`): `UF`.
theorem instIsPartialOrderOpposite.h2 :
    ¬ drop% Std.OppositeOrderInstances.instIsPartialOrderOpposite 2 := fun h => by
  have := (@h UF inferInstance).le_refl ()
  unfold LE.opposite at this
  exact this

-- `Std.OppositeOrderInstances.instIsLinearOrderOpposite`, idx 2 (`IsLinearOrder α`): `UF`.
theorem instIsLinearOrderOpposite.h2 :
    ¬ drop% Std.OppositeOrderInstances.instIsLinearOrderOpposite 2 := fun h => by
  have := (@h UF inferInstance).le_refl ()
  unfold LE.opposite at this
  exact this

-- `Std.OppositeOrderInstances.instLawfulOrderOrdOpposite`, idx 3 (`LawfulOrderOrd α`): `UO`;
-- the opposite `compare` is still constantly `Ordering.lt`.
theorem instLawfulOrderOrdOpposite.h3 :
    ¬ drop% Std.OppositeOrderInstances.instLawfulOrderOrdOpposite 3 := fun h => by
  have := (@h UO inferInstance inferInstance).isGE_compare () ()
  unfold LE.opposite Ord.opposite at this
  exact Bool.noConfusion (this.mpr trivial)

-- `Std.OppositeOrderInstances.instLawfulOrderBEqOpposite`, idx 3 (`LawfulOrderBEq α`): `UO`.
theorem instLawfulOrderBEqOpposite.h3 :
    ¬ drop% Std.OppositeOrderInstances.instLawfulOrderBEqOpposite 3 := fun h => by
  have := (@h UO inferInstance inferInstance).beq_iff_le_and_ge () ()
  unfold LE.opposite at this
  exact Bool.noConfusion (this.mpr ⟨trivial, trivial⟩)

-- `Std.OppositeOrderInstances.instLawfulOrderInfOpposite`, idx 3 (`LawfulOrderInf α`): `B` with
-- `min := (· || ·)`; opposite: `max true false ≥ true` but not `false ≥ true`.
theorem instLawfulOrderInfOpposite.h3 :
    ¬ drop% Std.OppositeOrderInstances.instLawfulOrderInfOpposite 3 := fun h => by
  have := (@h B inferInstance ⟨fun a b => a || b⟩).max_le_iff .tt .ff .tt
  unfold LE.opposite Min.oppositeMax at this
  revert this; decide

-- `Std.OppositeOrderInstances.instLawfulOrderMinOpposite`, idx 3 (`LawfulOrderMin α`): `B` with
-- `min := (· || ·)`; opposite: `max true false ≥ true` but not `false ≥ true`.
theorem instLawfulOrderMinOpposite.h3 :
    ¬ drop% Std.OppositeOrderInstances.instLawfulOrderMinOpposite 3 := fun h => by
  have := (@h B inferInstance ⟨fun a b => a || b⟩).max_le_iff .tt .ff .tt
  unfold LE.opposite Min.oppositeMax at this
  revert this; decide

-- `Std.OppositeOrderInstances.instLawfulOrderSupOpposite`, idx 3 (`LawfulOrderSup α`): `B` with
-- `max := (· && ·)`; opposite: `false ≥ min true false` but not `false ≥ true`.
theorem instLawfulOrderSupOpposite.h3 :
    ¬ drop% Std.OppositeOrderInstances.instLawfulOrderSupOpposite 3 := fun h => by
  have := (@h B inferInstance ⟨fun a b => a && b⟩).le_min_iff .ff .tt .ff
  unfold LE.opposite Max.oppositeMin at this
  revert this; decide

-- `Std.OppositeOrderInstances.instLawfulOrderMaxOpposite`, idx 3 (`LawfulOrderMax α`): `B` with
-- `max := (· && ·)`; opposite: `false ≥ min true false` but not `false ≥ true`.
theorem instLawfulOrderMaxOpposite.h3 :
    ¬ drop% Std.OppositeOrderInstances.instLawfulOrderMaxOpposite 3 := fun h => by
  have := (@h B inferInstance ⟨fun a b => a && b⟩).le_min_iff .ff .tt .ff
  unfold LE.opposite Max.oppositeMin at this
  revert this; decide

-- `Std.OppositeOrderInstances.instLawfulOrderLeftLeaningMinOpposite`, idx 3
-- (`LawfulOrderLeftLeaningMin α`): `BT` with `min a b := b`; `max true false = false`.
theorem instLawfulOrderLeftLeaningMinOpposite.h3 :
    ¬ drop% Std.OppositeOrderInstances.instLawfulOrderLeftLeaningMinOpposite 3 := fun h => by
  have := (@h BT inferInstance ⟨fun _ b => b⟩).max_eq_left .tt .ff
  unfold LE.opposite Min.oppositeMax at this
  exact absurd (this trivial) (by decide)

end OrderClassesHand
