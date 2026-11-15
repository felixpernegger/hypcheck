import Lean

/-!
Hand pass over cluster `OrderLemmas` (hand7): the 115 unresolved hypotheses of
`Init.Data.Order.Lemmas`, `Init.Data.Order.LemmasExtra` and `Init.Data.Order.MinMaxOn`. For
hypothesis `hᵢ` of theorem `T` this file proves `T'` (removable) or `¬T'` (necessary).

112 necessary, 3 removable, 0 independent, 0 left unresolved.

Removable (3):
* `maxOn_eq_right_of_lt`, `minOn_eq_right_of_lt` (`Total (· ≤ ·)`): `LawfulOrderLT` alone turns the
  hypothesis `f x < f y` (resp. `f y < f x`) into `¬ f y ≤ f x` (resp. `¬ f x ≤ f y`), which selects
  the `else` branch of `maxOn`/`minOn`.
* `instAntisymmLtOfLawfulOrderLTOfLe` (`Antisymm (· ≤ ·)`): a lawful `<` is asymmetric, so
  `Antisymm (· < ·)` holds vacuously.

Necessary (112): each `¬T'` specializes the hypothetical `T'` to one of the models below (each a
copy of `Fin n` with its own instances, violating one law; the laws it does satisfy are proved by
`decide`) and evaluates with `decide`. The lemmas about abstract relations use `True`, `False`, `=`
or `≠` on `Bool`/`Unit`.

`drop% T i` elaborates to `T'` (`T` without binder `i`) read off the library, with `T`'s universe
parameters kept (used for the removable verdicts); `dropu% [l₁, …] T i` is the same statement at
the given universe levels (used for the refutations).

Run with the lean4 repo's stage1 binary: `lean checks/OrderLemmasHand.lean`.
-/

open Lean Meta Elab Term in
/-- `T'` for the non-dependent Prop binder `i` of `T`, with universe levels `us` (fresh if `none`). -/
def HandDrop.dropType (T : Ident) (i : Nat) (us? : Option (List Level)) : TermElabM Expr := do
  let n ← realizeGlobalConstNoOverloadWithInfo T
  let ci ← getConstInfo n
  let us ← match us? with
    | some us => pure us
    | none => ci.levelParams.mapM fun _ => mkFreshLevelMVar
  unless us.length == ci.levelParams.length do
    throwError "{n} has {ci.levelParams.length} universe parameters"
  forallTelescope (ci.type.instantiateLevelParams ci.levelParams us) fun xs body => do
    let x := xs[i]!
    unless ← isProp (← inferType x) do throwError "binder {i} of {n} is not a Prop"
    for j in [i+1:xs.size] do
      if (← inferType xs[j]!).containsFVar x.fvarId! then throwError "binder {i} of {n} is dependent"
    if body.containsFVar x.fvarId! then throwError "binder {i} of {n} is dependent"
    mkForallFVars (xs.eraseIdx! i) body

/-- `drop% T i`: `T` with its (non-dependent) Prop binder `i` dropped, read off the library. -/
elab "drop% " T:ident i:num : term => HandDrop.dropType T i.getNat none

/-- `dropu% [l₁, …] T i`: `drop% T i` with `T`'s universe parameters set to the given levels. -/
elab "dropu% " "[" ls:num,* "]" T:ident i:num : term =>
  HandDrop.dropType T i.getNat (some (ls.getElems.map fun l => Lean.Level.ofNat l.getNat).toList)

set_option linter.unusedVariables false

namespace OrderLemmasHand

/-! ## Models (each a copy of `Fin n` with its own instances; laws checked by `decide`) -/

/-- `≤` is `=`: reflexive, antisymmetric, transitive, not total; `<` empty (its lawful strict
part); `compare` constantly `.eq`; `min`/`max` the usual ones. -/
def Eq2 := Fin 2
instance {k : Nat} : OfNat Eq2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq Eq2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : Eq2 → Prop} [h : DecidablePred P] : Decidable (∀ x : Eq2, P x) :=
  @Nat.decidableForallFin 2 P h
def Eq2.val (a : Eq2) : Nat := Fin.val a
instance : LE Eq2 := ⟨fun a b => a = b⟩
instance : DecidableLE Eq2 := fun a b => inferInstanceAs (Decidable (a = b))
instance : LT Eq2 := ⟨fun _ _ => False⟩
instance : DecidableLT Eq2 := fun _ _ => instDecidableFalse
instance : Ord Eq2 := ⟨fun _ _ => .eq⟩
instance : Min Eq2 := ⟨fun a b => if a.val ≤ b.val then a else b⟩
instance : Max Eq2 := ⟨fun a b => if a.val ≤ b.val then b else a⟩
instance : Std.Refl (α := Eq2) (· ≤ ·) := ⟨by decide⟩
instance : Std.Antisymm (α := Eq2) (· ≤ ·) := ⟨by decide⟩
instance : Trans (α := Eq2) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨fun {a b c} => by revert a b c; decide⟩
instance : Std.LawfulOrderLT Eq2 := ⟨by decide⟩

/-- `≤` everywhere true (a linear preorder, not antisymmetric), `<` empty, `compare` constantly
`.eq`, `min`/`max` the left projection, lawful `==`. -/
def Tr2 := Fin 2
instance {k : Nat} : OfNat Tr2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq Tr2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : Tr2 → Prop} [h : DecidablePred P] : Decidable (∀ x : Tr2, P x) :=
  @Nat.decidableForallFin 2 P h
def Tr2.val (a : Tr2) : Nat := Fin.val a
instance : LE Tr2 := ⟨fun _ _ => True⟩
instance : DecidableLE Tr2 := fun _ _ => instDecidableTrue
instance : LT Tr2 := ⟨fun _ _ => False⟩
instance : DecidableLT Tr2 := fun _ _ => instDecidableFalse
instance : Ord Tr2 := ⟨fun _ _ => .eq⟩
instance : Min Tr2 := ⟨fun a _ => a⟩
instance : Max Tr2 := ⟨fun a _ => a⟩
instance : Std.IsLinearPreorder Tr2 where
  le_refl := by decide
  le_trans := by decide
  le_total := by decide
instance : Std.LawfulOrderLT Tr2 := ⟨by decide⟩
instance : Std.LawfulOrderOrd Tr2 := ⟨by decide, by decide⟩
instance : Std.TransOrd Tr2 where
  eq_swap := fun {a b} => by revert a b; decide
  isLE_trans := fun {a b c} => by revert a b c; decide
instance : Std.LawfulOrderMin Tr2 where
  min_eq_or := by decide
  le_min_iff := by decide
instance : Std.LawfulOrderMax Tr2 where
  max_eq_or := by decide
  max_le_iff := by decide
instance : Std.LawfulOrderLeftLeaningMin Tr2 := ⟨by decide, by decide⟩
instance : Std.LawfulOrderLeftLeaningMax Tr2 := ⟨by decide, by decide⟩

/-- `≤` everywhere true, `compare` constantly `.eq`, `min`/`max` constantly `1` (not selecting). -/
def TrC2 := Fin 2
instance {k : Nat} : OfNat TrC2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq TrC2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : TrC2 → Prop} [h : DecidablePred P] : Decidable (∀ x : TrC2, P x) :=
  @Nat.decidableForallFin 2 P h
def TrC2.val (a : TrC2) : Nat := Fin.val a
instance : LE TrC2 := ⟨fun _ _ => True⟩
instance : DecidableLE TrC2 := fun _ _ => instDecidableTrue
instance : Ord TrC2 := ⟨fun _ _ => .eq⟩
instance : Min TrC2 := ⟨fun _ _ => 1⟩
instance : Max TrC2 := ⟨fun _ _ => 1⟩
instance : Std.LawfulOrderOrd TrC2 := ⟨by decide, by decide⟩
instance : Std.LawfulOrderInf TrC2 := ⟨by decide⟩
instance : Std.LawfulOrderSup TrC2 := ⟨by decide⟩

/-- The usual linear order, `<` and `compare`, with `min`/`max` the left projection. -/
def NatL2 := Fin 2
instance {k : Nat} : OfNat NatL2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq NatL2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : NatL2 → Prop} [h : DecidablePred P] : Decidable (∀ x : NatL2, P x) :=
  @Nat.decidableForallFin 2 P h
def NatL2.val (a : NatL2) : Nat := Fin.val a
instance : LE NatL2 := ⟨fun a b => a.val ≤ b.val⟩
instance : DecidableLE NatL2 := fun a b => Nat.decLe a.val b.val
instance : LT NatL2 := ⟨fun a b => a.val < b.val⟩
instance : DecidableLT NatL2 := fun a b => Nat.decLt a.val b.val
instance : Ord NatL2 := ⟨fun a b => compare a.val b.val⟩
instance : Min NatL2 := ⟨fun a _ => a⟩
instance : Max NatL2 := ⟨fun a _ => a⟩
instance : Std.IsLinearOrder NatL2 where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
instance : Std.LawfulOrderLT NatL2 := ⟨by decide⟩
instance : Std.LawfulOrderOrd NatL2 := ⟨by decide, by decide⟩

/-- The usual linear order with `min`/`max` constantly `1` (not selecting). -/
def NatC2 := Fin 2
instance {k : Nat} : OfNat NatC2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq NatC2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : NatC2 → Prop} [h : DecidablePred P] : Decidable (∀ x : NatC2, P x) :=
  @Nat.decidableForallFin 2 P h
def NatC2.val (a : NatC2) : Nat := Fin.val a
instance : LE NatC2 := ⟨fun a b => a.val ≤ b.val⟩
instance : DecidableLE NatC2 := fun a b => Nat.decLe a.val b.val
instance : Min NatC2 := ⟨fun _ _ => 1⟩
instance : Max NatC2 := ⟨fun _ _ => 1⟩
instance : Std.IsLinearOrder NatC2 where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide

/-- Rock–paper–scissors selection on `Fin 3`: `sel a b = a` if `b ≡ a + 1`, else `b`. Selecting
and commutative, not associative (`sel (sel 0 1) 2 = 2`, `sel 0 (sel 1 2) = 0`). -/
def rps (a b : Nat) : Bool := b % 3 == (a + 1) % 3

/-- The usual linear order on `Fin 3` with `min`/`max` the rock–paper–scissors selection. -/
def NatR3 := Fin 3
instance {k : Nat} : OfNat NatR3 k := inferInstanceAs (OfNat (Fin 3) k)
instance : DecidableEq NatR3 := inferInstanceAs (DecidableEq (Fin 3))
instance {P : NatR3 → Prop} [h : DecidablePred P] : Decidable (∀ x : NatR3, P x) :=
  @Nat.decidableForallFin 3 P h
def NatR3.val (a : NatR3) : Nat := Fin.val a
instance : LE NatR3 := ⟨fun a b => a.val ≤ b.val⟩
instance : DecidableLE NatR3 := fun a b => Nat.decLe a.val b.val
instance : Min NatR3 := ⟨fun a b => if rps a.val b.val then a else b⟩
instance : Max NatR3 := ⟨fun a b => if rps a.val b.val then a else b⟩
instance : Std.IsLinearOrder NatR3 where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide

/-- `≤` everywhere true on `Fin 3` with `min`/`max` the rock–paper–scissors selection: lawful
`min`/`max` (selecting, and `≤` is trivially compatible), not associative. -/
def TrR3 := Fin 3
instance {k : Nat} : OfNat TrR3 k := inferInstanceAs (OfNat (Fin 3) k)
instance : DecidableEq TrR3 := inferInstanceAs (DecidableEq (Fin 3))
instance {P : TrR3 → Prop} [h : DecidablePred P] : Decidable (∀ x : TrR3, P x) :=
  @Nat.decidableForallFin 3 P h
def TrR3.val (a : TrR3) : Nat := Fin.val a
instance : LE TrR3 := ⟨fun _ _ => True⟩
instance : DecidableLE TrR3 := fun _ _ => instDecidableTrue
instance : Min TrR3 := ⟨fun a b => if rps a.val b.val then a else b⟩
instance : Max TrR3 := ⟨fun a b => if rps a.val b.val then a else b⟩
instance : Std.LawfulOrderMin TrR3 where
  min_eq_or := by decide
  le_min_iff := by decide
instance : Std.LawfulOrderMax TrR3 where
  max_eq_or := by decide
  max_le_iff := by decide

/-- Rock–paper–scissors `≤` on `Fin 3`: `a ≤ b ↔ b = a ∨ b ≡ a + 1`. Reflexive, total and
antisymmetric, not transitive (`0 ≤ 1 ≤ 2`, `¬ 0 ≤ 2`); with the lawful `compare`, `<` and the
left-leaning `min`/`max` it determines. -/
def Rps3 := Fin 3
instance {k : Nat} : OfNat Rps3 k := inferInstanceAs (OfNat (Fin 3) k)
instance : DecidableEq Rps3 := inferInstanceAs (DecidableEq (Fin 3))
instance {P : Rps3 → Prop} [h : DecidablePred P] : Decidable (∀ x : Rps3, P x) :=
  @Nat.decidableForallFin 3 P h
def Rps3.val (a : Rps3) : Nat := Fin.val a
instance : LE Rps3 := ⟨fun a b => b.val = a.val ∨ rps a.val b.val⟩
instance : DecidableLE Rps3 := fun a b => inferInstanceAs (Decidable (_ ∨ _))
instance : LT Rps3 := ⟨fun a b => a ≤ b ∧ ¬ b ≤ a⟩
instance : DecidableLT Rps3 := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : Ord Rps3 := ⟨fun a b => if a ≤ b then if b ≤ a then .eq else .lt else .gt⟩
instance : Min Rps3 := ⟨fun a b => if a ≤ b then a else b⟩
instance : Max Rps3 := ⟨fun a b => if b ≤ a then a else b⟩
instance : Std.LawfulOrderLT Rps3 := ⟨by decide⟩
instance : Std.LawfulOrderOrd Rps3 := ⟨by decide, by decide⟩
instance : Std.LawfulEqOrd Rps3 where
  compare_self := fun {a} => by revert a; decide
  eq_of_compare := fun {a b} => by revert a b; decide
instance : Std.LawfulOrderLeftLeaningMin Rps3 := ⟨by decide, by decide⟩
instance : Std.LawfulOrderLeftLeaningMax Rps3 := ⟨by decide, by decide⟩

/-- `≤` everywhere false (antisymmetric and transitive, not reflexive), with the usual `<`,
`compare`, `min`, `max` and lawful `==`. -/
def LeF2 := Fin 2
instance {k : Nat} : OfNat LeF2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq LeF2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : LeF2 → Prop} [h : DecidablePred P] : Decidable (∀ x : LeF2, P x) :=
  @Nat.decidableForallFin 2 P h
def LeF2.val (a : LeF2) : Nat := Fin.val a
instance : LE LeF2 := ⟨fun _ _ => False⟩
instance : DecidableLE LeF2 := fun _ _ => instDecidableFalse
instance : LT LeF2 := ⟨fun a b => a.val < b.val⟩
instance : DecidableLT LeF2 := fun a b => Nat.decLt a.val b.val
instance : Ord LeF2 := ⟨fun a b => compare a.val b.val⟩
instance : Min LeF2 := ⟨fun a b => if a.val ≤ b.val then a else b⟩
instance : Max LeF2 := ⟨fun a b => if a.val ≤ b.val then b else a⟩
instance : Std.Antisymm (α := LeF2) (· ≤ ·) := ⟨by decide⟩
instance : Std.LawfulOrderMin LeF2 where
  min_eq_or := by decide
  le_min_iff := by decide
instance : Std.LawfulOrderMax LeF2 where
  max_eq_or := by decide
  max_le_iff := by decide
instance : Std.TransOrd LeF2 where
  eq_swap := fun {a b} => by revert a b; decide
  isLE_trans := fun {a b c} => by revert a b c; decide
instance : Std.LawfulEqOrd LeF2 where
  compare_self := fun {a} => by revert a; decide
  eq_of_compare := fun {a b} => by revert a b; decide
instance : Std.LawfulBEqOrd LeF2 := ⟨fun {a b} => by revert a b; decide⟩

/-- `≤` everywhere false and `==` constantly `false` (a lawful pair, `==` not reflexive). -/
def LeFB2 := Fin 2
instance {k : Nat} : OfNat LeFB2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq LeFB2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : LeFB2 → Prop} [h : DecidablePred P] : Decidable (∀ x : LeFB2, P x) :=
  @Nat.decidableForallFin 2 P h
def LeFB2.val (a : LeFB2) : Nat := Fin.val a
instance : LE LeFB2 := ⟨fun _ _ => False⟩
instance : DecidableLE LeFB2 := fun _ _ => instDecidableFalse
instance : BEq LeFB2 := ⟨fun _ _ => false⟩
instance : Std.LawfulOrderBEq LeFB2 := ⟨by decide⟩

/-- `≤` everywhere true and `==` constantly `true` (a lawful pair, `==` not lawful). -/
def TrB2 := Fin 2
instance {k : Nat} : OfNat TrB2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq TrB2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : TrB2 → Prop} [h : DecidablePred P] : Decidable (∀ x : TrB2, P x) :=
  @Nat.decidableForallFin 2 P h
def TrB2.val (a : TrB2) : Nat := Fin.val a
instance : LE TrB2 := ⟨fun _ _ => True⟩
instance : DecidableLE TrB2 := fun _ _ => instDecidableTrue
instance : BEq TrB2 := ⟨fun _ _ => true⟩
instance : Std.LawfulOrderBEq TrB2 := ⟨by decide⟩

/-- The usual linear order and `compare` with `==` constantly `false`. -/
def BF2 := Fin 2
instance {k : Nat} : OfNat BF2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq BF2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : BF2 → Prop} [h : DecidablePred P] : Decidable (∀ x : BF2, P x) :=
  @Nat.decidableForallFin 2 P h
def BF2.val (a : BF2) : Nat := Fin.val a
instance : LE BF2 := ⟨fun a b => a.val ≤ b.val⟩
instance : DecidableLE BF2 := fun a b => Nat.decLe a.val b.val
instance : Ord BF2 := ⟨fun a b => compare a.val b.val⟩
instance : BEq BF2 := ⟨fun _ _ => false⟩
instance : Std.IsLinearOrder BF2 where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
instance : Std.LawfulOrderOrd BF2 := ⟨by decide, by decide⟩

/-- `≤` everywhere true with the usual `<` (trichotomous) and `compare` (lawful `eq`). -/
def TrN2 := Fin 2
instance {k : Nat} : OfNat TrN2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq TrN2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : TrN2 → Prop} [h : DecidablePred P] : Decidable (∀ x : TrN2, P x) :=
  @Nat.decidableForallFin 2 P h
def TrN2.val (a : TrN2) : Nat := Fin.val a
instance : LE TrN2 := ⟨fun _ _ => True⟩
instance : DecidableLE TrN2 := fun _ _ => instDecidableTrue
instance : LT TrN2 := ⟨fun a b => a.val < b.val⟩
instance : DecidableLT TrN2 := fun a b => Nat.decLt a.val b.val
instance : Ord TrN2 := ⟨fun a b => compare a.val b.val⟩
instance : Std.LawfulEqOrd TrN2 where
  compare_self := fun {a} => by revert a; decide
  eq_of_compare := fun {a b} => by revert a b; decide
instance : Std.Trichotomous (α := TrN2) (· < ·) := ⟨by decide⟩

/-- The usual linear order with `compare` constantly `.lt` (not oriented). -/
def OrdLt2 := Fin 2
instance {k : Nat} : OfNat OrdLt2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq OrdLt2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : OrdLt2 → Prop} [h : DecidablePred P] : Decidable (∀ x : OrdLt2, P x) :=
  @Nat.decidableForallFin 2 P h
def OrdLt2.val (a : OrdLt2) : Nat := Fin.val a
instance : LE OrdLt2 := ⟨fun a b => a.val ≤ b.val⟩
instance : DecidableLE OrdLt2 := fun a b => Nat.decLe a.val b.val
instance : Ord OrdLt2 := ⟨fun _ _ => .lt⟩
instance : Std.IsLinearOrder OrdLt2 where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide

/-- The usual linear order, `<` and lawful `==`, with `compare` constantly `.eq`. -/
def OrdEq2 := Fin 2
instance {k : Nat} : OfNat OrdEq2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq OrdEq2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : OrdEq2 → Prop} [h : DecidablePred P] : Decidable (∀ x : OrdEq2, P x) :=
  @Nat.decidableForallFin 2 P h
def OrdEq2.val (a : OrdEq2) : Nat := Fin.val a
instance : LE OrdEq2 := ⟨fun a b => a.val ≤ b.val⟩
instance : DecidableLE OrdEq2 := fun a b => Nat.decLe a.val b.val
instance : LT OrdEq2 := ⟨fun a b => a.val < b.val⟩
instance : DecidableLT OrdEq2 := fun a b => Nat.decLt a.val b.val
instance : Ord OrdEq2 := ⟨fun _ _ => .eq⟩
instance : Std.IsLinearOrder OrdEq2 where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
instance : Std.LawfulOrderLT OrdEq2 := ⟨by decide⟩
instance : Std.LawfulOrderBEq OrdEq2 := ⟨by decide⟩

/-- The usual linear order and `compare` with `<` empty (asymmetric, not trichotomous, not the
strict part of `≤`). -/
def LtF2 := Fin 2
instance {k : Nat} : OfNat LtF2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq LtF2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : LtF2 → Prop} [h : DecidablePred P] : Decidable (∀ x : LtF2, P x) :=
  @Nat.decidableForallFin 2 P h
def LtF2.val (a : LtF2) : Nat := Fin.val a
instance : LE LtF2 := ⟨fun a b => a.val ≤ b.val⟩
instance : DecidableLE LtF2 := fun a b => Nat.decLe a.val b.val
instance : LT LtF2 := ⟨fun _ _ => False⟩
instance : DecidableLT LtF2 := fun _ _ => instDecidableFalse
instance : Ord LtF2 := ⟨fun a b => compare a.val b.val⟩
instance : Std.IsLinearOrder LtF2 where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
instance : Std.LawfulOrderOrd LtF2 := ⟨by decide, by decide⟩

/-- `a == b ↔ a ≤ b` for the usual order (not symmetric). -/
def BLe2 := Fin 2
instance {k : Nat} : OfNat BLe2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq BLe2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : BLe2 → Prop} [h : DecidablePred P] : Decidable (∀ x : BLe2, P x) :=
  @Nat.decidableForallFin 2 P h
def BLe2.val (a : BLe2) : Nat := Fin.val a
instance : LE BLe2 := ⟨fun a b => a.val ≤ b.val⟩
instance : DecidableLE BLe2 := fun a b => Nat.decLe a.val b.val
instance : BEq BLe2 := ⟨fun a b => decide (a.val ≤ b.val)⟩

/-- `<` everywhere true, `≤` is `=` (antisymmetric). -/
def LtT2 := Fin 2
instance {k : Nat} : OfNat LtT2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq LtT2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : LtT2 → Prop} [h : DecidablePred P] : Decidable (∀ x : LtT2, P x) :=
  @Nat.decidableForallFin 2 P h
def LtT2.val (a : LtT2) : Nat := Fin.val a
instance : LE LtT2 := ⟨fun a b => a = b⟩
instance : DecidableLE LtT2 := fun a b => inferInstanceAs (Decidable (a = b))
instance : LT LtT2 := ⟨fun _ _ => True⟩
instance : DecidableLT LtT2 := fun _ _ => instDecidableTrue
instance : Std.Antisymm (α := LtT2) (· ≤ ·) := ⟨by decide⟩

/-- `Fin 4` as `Bool × Bool` (bits) with the componentwise order: a lattice (`min` = `&&&`,
`max` = `|||`), not total; `<` its lawful strict part. -/
def Bit4 := Fin 4
instance {k : Nat} : OfNat Bit4 k := inferInstanceAs (OfNat (Fin 4) k)
instance : DecidableEq Bit4 := inferInstanceAs (DecidableEq (Fin 4))
instance {P : Bit4 → Prop} [h : DecidablePred P] : Decidable (∀ x : Bit4, P x) :=
  @Nat.decidableForallFin 4 P h
def Bit4.val (a : Bit4) : Nat := Fin.val a
instance : LE Bit4 := ⟨fun a b => a.val &&& b.val = a.val⟩
instance : DecidableLE Bit4 := fun a b => inferInstanceAs (Decidable (_ = _))
instance : LT Bit4 := ⟨fun a b => a ≤ b ∧ ¬ b ≤ a⟩
instance : DecidableLT Bit4 := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : Min Bit4 := ⟨fun a b => ⟨a.val &&& b.val, Nat.lt_of_le_of_lt Nat.and_le_left (Fin.isLt a)⟩⟩
instance : Max Bit4 := ⟨fun a b => if a.val = 0 then b else if b.val = 0 then a else
  if a.val = b.val then a else 3⟩
instance : Std.LawfulOrderLT Bit4 := ⟨by decide⟩
instance : Std.LawfulOrderInf Bit4 := ⟨by decide⟩
instance : Std.LawfulOrderSup Bit4 := ⟨by decide⟩

/-- `a ≤ b ↔ b = 0` (transitive, not reflexive at `1`), `<` its lawful strict part, the usual
`max`. -/
def LeZ2 := Fin 2
instance {k : Nat} : OfNat LeZ2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq LeZ2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : LeZ2 → Prop} [h : DecidablePred P] : Decidable (∀ x : LeZ2, P x) :=
  @Nat.decidableForallFin 2 P h
def LeZ2.val (a : LeZ2) : Nat := Fin.val a
instance : LE LeZ2 := ⟨fun _ b => b.val = 0⟩
instance : DecidableLE LeZ2 := fun _ b => inferInstanceAs (Decidable (_ = _))
instance : LT LeZ2 := ⟨fun a b => a ≤ b ∧ ¬ b ≤ a⟩
instance : DecidableLT LeZ2 := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : Max LeZ2 := ⟨fun a b => if a.val ≤ b.val then b else a⟩
instance : Std.LawfulOrderLT LeZ2 := ⟨by decide⟩
instance : Std.LawfulOrderMax LeZ2 where
  max_eq_or := by decide
  max_le_iff := by decide

/-- `a ≤ b ↔ a = 0` (transitive, not reflexive at `1`), `<` its lawful strict part, `min` the
usual `max`. -/
def LeA2 := Fin 2
instance {k : Nat} : OfNat LeA2 k := inferInstanceAs (OfNat (Fin 2) k)
instance : DecidableEq LeA2 := inferInstanceAs (DecidableEq (Fin 2))
instance {P : LeA2 → Prop} [h : DecidablePred P] : Decidable (∀ x : LeA2, P x) :=
  @Nat.decidableForallFin 2 P h
def LeA2.val (a : LeA2) : Nat := Fin.val a
instance : LE LeA2 := ⟨fun a _ => a.val = 0⟩
instance : DecidableLE LeA2 := fun a _ => inferInstanceAs (Decidable (_ = _))
instance : LT LeA2 := ⟨fun a b => a ≤ b ∧ ¬ b ≤ a⟩
instance : DecidableLT LeA2 := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : Min LeA2 := ⟨fun a b => if a.val ≤ b.val then b else a⟩
instance : Std.LawfulOrderLT LeA2 := ⟨by decide⟩
instance : Std.LawfulOrderMin LeA2 where
  min_eq_or := by decide
  le_min_iff := by decide


/-! ## Removable -/

-- `maxOn_eq_right_of_lt`, idx 5 (inst : Std.Total fun x1 x2 => x1 ≤ x2): LawfulOrderLT alone turns f x < f y into ¬ f y ≤ f x, which is the else branch of maxOn
theorem maxOn_eq_right_of_lt.h5 : drop% maxOn_eq_right_of_lt 5 :=
  by
  intro _ _ _ _ _ _ _ _ _ h
  exact maxOn_eq_right (Std.not_le_of_gt h)

-- `minOn_eq_right_of_lt`, idx 5 (inst : Std.Total fun x1 x2 => x1 ≤ x2): LawfulOrderLT alone turns f y < f x into ¬ f x ≤ f y, which is the else branch of minOn
theorem minOn_eq_right_of_lt.h5 : drop% minOn_eq_right_of_lt 5 :=
  by
  intro _ _ _ _ _ _ _ _ _ h
  exact minOn_eq_right (Std.not_le_of_gt h)

-- `Std.instAntisymmLtOfLawfulOrderLTOfLe`, idx 4 (inst : Std.Antisymm fun x1 x2 => x1 ≤ x2): a lawful < is asymmetric, so a < b → b < a → a = b holds vacuously; Antisymm (· ≤ ·) is not needed
theorem instAntisymmLtOfLawfulOrderLTOfLe.h4 : drop% Std.instAntisymmLtOfLawfulOrderLTOfLe 4 :=
  ⟨fun _ _ hab hba => (Std.not_gt_of_lt hab hba).elim⟩

/-! ## Necessary -/

-- `Std.LawfulOrderMin.of_ord`, idx 4 (inst : Std.LawfulOrderOrd α): Eq2 (≤ is =, compare constantly .eq, usual min): 0 ≤ min 0 1 but ¬ 0 ≤ 1
theorem LawfulOrderMin.of_ord.h4 : ¬ dropu% [0] Std.LawfulOrderMin.of_ord 4 :=
  fun h => absurd ((h Eq2 (by decide) (by decide)).le_min_iff 0 0 1) (by decide)

-- `Std.LawfulOrderMin.of_ord`, idx 5 (compare_min_isLE_iff : ∀ (a b c : α), (compare a (min b c)).isLE = true ↔ (compare a b).isLE = true ∧ (compare a c).isLE = true): NatL2 (usual order and compare, min the left projection): 1 ≤ min 1 0 = 1 but ¬ 1 ≤ 0
theorem LawfulOrderMin.of_ord.h5 : ¬ dropu% [0] Std.LawfulOrderMin.of_ord 5 :=
  fun h => absurd ((h NatL2 (by decide)).le_min_iff 1 1 0) (by decide)

-- `Std.LawfulOrderMin.of_ord`, idx 6 (min_eq_or : ∀ (a b : α), min a b = a ∨ min a b = b): TrC2 (≤ true, compare constantly .eq, min constantly 1): min 0 0 = 1
theorem LawfulOrderMin.of_ord.h6 : ¬ dropu% [0] Std.LawfulOrderMin.of_ord 6 :=
  fun h => absurd ((h TrC2 (by decide)).min_eq_or 0 0) (by decide)

-- `Std.LawfulOrderMax.of_ord`, idx 4 (inst : Std.LawfulOrderOrd α): Eq2 (≤ is =, compare constantly .eq, usual max): max 0 1 ≤ 1 but ¬ 0 ≤ 1
theorem LawfulOrderMax.of_ord.h4 : ¬ dropu% [0] Std.LawfulOrderMax.of_ord 4 :=
  fun h => absurd ((h Eq2 (by decide) (by decide)).max_le_iff 0 1 1) (by decide)

-- `Std.LawfulOrderMax.of_ord`, idx 5 (compare_max_isLE_iff : ∀ (a b c : α), (compare (max a b) c).isLE = true ↔ (compare a c).isLE = true ∧ (compare b c).isLE = true): NatL2 (usual order and compare, max the left projection): max 0 1 = 0 ≤ 0 but ¬ 1 ≤ 0
theorem LawfulOrderMax.of_ord.h5 : ¬ dropu% [0] Std.LawfulOrderMax.of_ord 5 :=
  fun h => absurd ((h NatL2 (by decide)).max_le_iff 0 1 0) (by decide)

-- `Std.LawfulOrderMax.of_ord`, idx 6 (max_eq_or : ∀ (a b : α), max a b = a ∨ max a b = b): TrC2 (≤ true, compare constantly .eq, max constantly 1): max 0 0 = 1
theorem LawfulOrderMax.of_ord.h6 : ¬ dropu% [0] Std.LawfulOrderMax.of_ord 6 :=
  fun h => absurd ((h TrC2 (by decide)).max_eq_or 0 0) (by decide)

-- `Std.LawfulOrderInf.of_ord`, idx 4 (inst : Std.LawfulOrderOrd α): Eq2 (≤ is =, compare constantly .eq, usual min): 0 ≤ min 0 1 but ¬ 0 ≤ 1
theorem LawfulOrderInf.of_ord.h4 : ¬ dropu% [0] Std.LawfulOrderInf.of_ord 4 :=
  fun h => absurd ((h Eq2 (by decide)).le_min_iff 0 0 1) (by decide)

-- `Std.LawfulOrderInf.of_ord`, idx 5 (compare_min_isLE_iff : ∀ (a b c : α), (compare a (min b c)).isLE = true ↔ (compare a b).isLE = true ∧ (compare a c).isLE = true): NatL2 (usual order and compare, min the left projection): 1 ≤ min 1 0 = 1 but ¬ 1 ≤ 0
theorem LawfulOrderInf.of_ord.h5 : ¬ dropu% [0] Std.LawfulOrderInf.of_ord 5 :=
  fun h => absurd ((h NatL2).le_min_iff 1 1 0) (by decide)

-- `Std.LawfulOrderSup.of_ord`, idx 4 (inst : Std.LawfulOrderOrd α): Eq2 (≤ is =, compare constantly .eq, usual max): max 0 1 ≤ 1 but ¬ 0 ≤ 1
theorem LawfulOrderSup.of_ord.h4 : ¬ dropu% [0] Std.LawfulOrderSup.of_ord 4 :=
  fun h => absurd ((h Eq2 (by decide)).max_le_iff 0 1 1) (by decide)

-- `Std.LawfulOrderSup.of_ord`, idx 5 (compare_max_isLE_iff : ∀ (a b c : α), (compare (max a b) c).isLE = true ↔ (compare a c).isLE = true ∧ (compare b c).isLE = true): NatL2 (usual order and compare, max the left projection): max 0 1 = 0 ≤ 0 but ¬ 1 ≤ 0
theorem LawfulOrderSup.of_ord.h5 : ¬ dropu% [0] Std.LawfulOrderSup.of_ord 5 :=
  fun h => absurd ((h NatL2).max_le_iff 0 1 0) (by decide)

-- `Std.LawfulOrderLT.of_ord`, idx 4 (inst : Std.LawfulOrderOrd α): LeF2 (≤ empty, usual < and compare): 0 < 1 but ¬ 0 ≤ 1
theorem LawfulOrderLT.of_ord.h4 : ¬ dropu% [0] Std.LawfulOrderLT.of_ord 4 :=
  fun h => absurd ((h LeF2 (by decide)).lt_iff 0 1) (by decide)

-- `Std.LawfulOrderLT.of_ord`, idx 5 (lt_iff_compare_eq_lt : ∀ (a b : α), a < b ↔ compare a b = Ordering.lt): LtF2 (usual ≤/compare, < empty): ¬ 0 < 1 although 0 ≤ 1, ¬ 1 ≤ 0
theorem LawfulOrderLT.of_ord.h5 : ¬ dropu% [0] Std.LawfulOrderLT.of_ord 5 :=
  fun h => absurd ((h LtF2).lt_iff 0 1) (by decide)

-- `Std.LawfulOrderBEq.of_ord`, idx 4 (inst : Std.LawfulOrderOrd α): LeF2 (≤ empty, usual compare and ==): 0 == 0 but ¬ 0 ≤ 0
theorem LawfulOrderBEq.of_ord.h4 : ¬ dropu% [0] Std.LawfulOrderBEq.of_ord 4 :=
  fun h => absurd ((h LeF2 (by decide)).beq_iff_le_and_ge 0 0) (by decide)

-- `Std.LawfulOrderBEq.of_ord`, idx 5 (beq_iff_compare_eq_eq : ∀ (a b : α), (a == b) = true ↔ compare a b = Ordering.eq): BF2 (usual order and compare, == constantly false): 0 ≤ 0 but ¬ 0 == 0
theorem LawfulOrderBEq.of_ord.h5 : ¬ dropu% [0] Std.LawfulOrderBEq.of_ord 5 :=
  fun h => absurd ((h BF2).beq_iff_le_and_ge 0 0) (by decide)

-- `Std.IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMin`, idx 4 (inst : Std.Refl fun x1 x2 => x1 ≤ x2): LeF2 (≤ empty, usual min): antisymmetric and LawfulOrderMin, not reflexive
theorem IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMin.h4 : ¬ dropu% [0] Std.IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMin 4 :=
  fun h => absurd ((h (α := LeF2)).le_refl 0) (by decide)

-- `Std.IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMin`, idx 5 (inst : Std.Antisymm fun x1 x2 => x1 ≤ x2): Tr2 (≤ true, min the left projection): reflexive and LawfulOrderMin, 0 ≤ 1 ≤ 0, 0 ≠ 1
theorem IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMin.h5 : ¬ dropu% [0] Std.IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMin 5 :=
  fun h => absurd ((h (α := Tr2)).le_antisymm 0 1 trivial trivial) (by decide)

-- `Std.IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMin`, idx 6 (inst : Std.LawfulOrderMin α): Eq2 (≤ is =): reflexive and antisymmetric, not total
theorem IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMin.h6 : ¬ dropu% [0] Std.IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMin 6 :=
  fun h => absurd ((h (α := Eq2)).le_total 0 1) (by decide)

-- `Std.IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMax`, idx 3 (inst : Std.Refl fun x1 x2 => x1 ≤ x2): LeF2 (≤ empty, usual max): antisymmetric and LawfulOrderMax, not reflexive
theorem IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMax.h3 : ¬ dropu% [0] Std.IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMax 3 :=
  fun h => absurd ((h (α := LeF2)).le_refl 0) (by decide)

-- `Std.IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMax`, idx 5 (inst : Std.LawfulOrderMax α): Eq2 (≤ is =): reflexive and antisymmetric, not total
theorem IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMax.h5 : ¬ dropu% [0] Std.IsLinearOrder.of_refl_of_antisymm_of_lawfulOrderMax 5 :=
  fun h => absurd ((h (α := Eq2)).le_total 0 1) (by decide)

-- `Std.le_max`, idx 3 (inst : Std.IsPreorder α): LeZ2 (a ≤ b ↔ b = 0, usual max, LawfulOrderMax, not reflexive): 0 ≤ 0 but ¬ 0 ≤ max 0 1 = 1
theorem le_max.h3 : ¬ dropu% [0] Std.le_max 3 :=
  fun h => absurd (h (α := LeZ2) (a := 0) (b := 0) (c := 1)) (by decide)

-- `Std.min_le`, idx 3 (inst : Std.IsPreorder α): LeA2 (a ≤ b ↔ a = 0, min the usual max, LawfulOrderMin): 0 ≤ 0 but ¬ min 0 1 = 1 ≤ 0
theorem min_le.h3 : ¬ dropu% [0] Std.min_le 3 :=
  fun h => absurd (h (α := LeA2) (a := 0) (b := 1) (c := 0)) (by decide)

-- `Std.lt_min_iff`, idx 4 (inst : Std.IsLinearPreorder α): LeA2 (a ≤ b ↔ a = 0, min the usual max, lawful <): 0 < min 1 0 = 1 but ¬ 0 < 0
theorem lt_min_iff.h4 : ¬ dropu% [0] Std.lt_min_iff 4 :=
  fun h => absurd (h (α := LeA2) (a := 0) (b := 1) (c := 0)) (by decide)

-- `Std.max_lt_iff`, idx 4 (inst : Std.IsLinearPreorder α): LeZ2 (a ≤ b ↔ b = 0, usual max, lawful <): max 0 1 = 1 < 0 but ¬ 0 < 0
theorem max_lt_iff.h4 : ¬ dropu% [0] Std.max_lt_iff 4 :=
  fun h => absurd (h (α := LeZ2) (a := 0) (b := 1) (c := 0)) (by decide)

-- `Std.min_lt_iff`, idx 4 (inst : Std.Total fun x1 x2 => x1 ≤ x2): Bit4 (Bool × Bool componentwise, min = and): min 1 2 = 0 < 1 but ¬ 1 < 1, ¬ 2 < 1
theorem min_lt_iff.h4 : ¬ dropu% [0] Std.min_lt_iff 4 :=
  fun h => absurd (h (α := Bit4) (a := 1) (b := 2) (c := 1)) (by decide)

-- `Std.lt_max_iff`, idx 4 (inst : Std.Total fun x1 x2 => x1 ≤ x2): Bit4 (Bool × Bool componentwise, max = or): 2 < max 1 2 = 3 but ¬ 2 < 1, ¬ 2 < 2
theorem lt_max_iff.h4 : ¬ dropu% [0] Std.lt_max_iff 4 :=
  fun h => absurd (h (α := Bit4) (a := 2) (b := 1) (c := 2)) (by decide)

-- `Std.instLawfulOrderBEqOfLawfulBEqOfReflOfAntisymmLe`, idx 3 (inst : LawfulBEq α): BF2 (usual order, == constantly false): 0 ≤ 0 but ¬ 0 == 0
theorem instLawfulOrderBEqOfLawfulBEqOfReflOfAntisymmLe.h3 : ¬ dropu% [0] Std.instLawfulOrderBEqOfLawfulBEqOfReflOfAntisymmLe 3 :=
  fun h => absurd ((h (α := BF2)).beq_iff_le_and_ge 0 0) (by decide)

-- `Std.instLawfulOrderBEqOfLawfulBEqOfReflOfAntisymmLe`, idx 4 (inst : Std.Refl fun x1 x2 => x1 ≤ x2): LeF2 (≤ empty, lawful ==): 0 == 0 but ¬ 0 ≤ 0
theorem instLawfulOrderBEqOfLawfulBEqOfReflOfAntisymmLe.h4 : ¬ dropu% [0] Std.instLawfulOrderBEqOfLawfulBEqOfReflOfAntisymmLe 4 :=
  fun h => absurd ((h (α := LeF2)).beq_iff_le_and_ge 0 0) (by decide)

-- `Std.instLawfulOrderBEqOfLawfulBEqOfReflOfAntisymmLe`, idx 5 (inst : Std.Antisymm fun x1 x2 => x1 ≤ x2): Tr2 (≤ true, lawful ==): 0 ≤ 1 ≤ 0 but ¬ 0 == 1
theorem instLawfulOrderBEqOfLawfulBEqOfReflOfAntisymmLe.h5 : ¬ dropu% [0] Std.instLawfulOrderBEqOfLawfulBEqOfReflOfAntisymmLe 5 :=
  fun h => absurd ((h (α := Tr2)).beq_iff_le_and_ge 0 1) (by decide)

-- `Std.instLawfulOrderBEqOfLawfulBEqOrdOfLawfulOrderOrd`, idx 4 (inst : Std.LawfulBEqOrd α): BF2 (usual order and compare, == constantly false): 0 ≤ 0 but ¬ 0 == 0
theorem instLawfulOrderBEqOfLawfulBEqOrdOfLawfulOrderOrd.h4 : ¬ dropu% [0] Std.instLawfulOrderBEqOfLawfulBEqOrdOfLawfulOrderOrd 4 :=
  fun h => absurd ((h (α := BF2)).beq_iff_le_and_ge 0 0) (by decide)

-- `Std.instLawfulOrderBEqOfLawfulBEqOrdOfLawfulOrderOrd`, idx 5 (inst : Std.LawfulOrderOrd α): LeF2 (≤ empty, usual compare and ==): 0 == 0 but ¬ 0 ≤ 0
theorem instLawfulOrderBEqOfLawfulBEqOrdOfLawfulOrderOrd.h5 : ¬ dropu% [0] Std.instLawfulOrderBEqOfLawfulBEqOrdOfLawfulOrderOrd 5 :=
  fun h => absurd ((h (α := LeF2)).beq_iff_le_and_ge 0 0) (by decide)

-- `Std.instLawfulBEqOrdOfLawfulOrderOrdOfLawfulOrderBEq`, idx 4 (inst : Std.LawfulOrderOrd α): OrdEq2 (usual order and ==, compare constantly .eq): compare 0 1 = .eq but ¬ 0 == 1
theorem instLawfulBEqOrdOfLawfulOrderOrdOfLawfulOrderBEq.h4 : ¬ dropu% [0] Std.instLawfulBEqOrdOfLawfulOrderOrdOfLawfulOrderBEq 4 :=
  fun h => absurd ((h (α := OrdEq2)).compare_eq_iff_beq (a := 0) (b := 1)) (by decide)

-- `Std.instLawfulBEqOrdOfLawfulOrderOrdOfLawfulOrderBEq`, idx 5 (inst : Std.LawfulOrderBEq α): BF2 (usual order and compare, == constantly false): compare 0 0 = .eq but ¬ 0 == 0
theorem instLawfulBEqOrdOfLawfulOrderOrdOfLawfulOrderBEq.h5 : ¬ dropu% [0] Std.instLawfulBEqOrdOfLawfulOrderOrdOfLawfulOrderBEq 5 :=
  fun h => absurd ((h (α := BF2)).compare_eq_iff_beq (a := 0) (b := 0)) (by decide)

-- `Std.instSymmEqBoolBeqTrueOfLawfulOrderBEq`, idx 3 (inst : Std.LawfulOrderBEq α): BLe2 (a == b ↔ a ≤ b): 0 == 1 but ¬ 1 == 0
theorem instSymmEqBoolBeqTrueOfLawfulOrderBEq.h3 : ¬ dropu% [0] Std.instSymmEqBoolBeqTrueOfLawfulOrderBEq 3 :=
  fun h => absurd ((h (α := BLe2)).symm 0 1 (by decide)) (by decide)

-- `Std.instEquivBEqOfLawfulOrderBEqOfIsPreorder`, idx 3 (inst : Std.LawfulOrderBEq α): BF2 (usual order, == constantly false): ¬ 0 == 0
theorem instEquivBEqOfLawfulOrderBEqOfIsPreorder.h3 : ¬ dropu% [0] Std.instEquivBEqOfLawfulOrderBEqOfIsPreorder 3 :=
  fun h => absurd ((h (α := BF2)).toReflBEq.rfl (a := 0)) (by decide)

-- `Std.instEquivBEqOfLawfulOrderBEqOfIsPreorder`, idx 4 (inst : Std.IsPreorder α): LeFB2 (≤ empty, == constantly false, a lawful pair): ¬ 0 == 0
theorem instEquivBEqOfLawfulOrderBEqOfIsPreorder.h4 : ¬ dropu% [0] Std.instEquivBEqOfLawfulOrderBEqOfIsPreorder 4 :=
  fun h => absurd ((h (α := LeFB2)).toReflBEq.rfl (a := 0)) (by decide)

-- `Std.instLawfulBEqOfLawfulOrderBEqOfIsPartialOrder`, idx 3 (inst : Std.LawfulOrderBEq α): BF2 (usual order, == constantly false): ¬ 0 == 0
theorem instLawfulBEqOfLawfulOrderBEqOfIsPartialOrder.h3 : ¬ dropu% [0] Std.instLawfulBEqOfLawfulOrderBEqOfIsPartialOrder 3 :=
  fun h => absurd ((h (α := BF2)).toReflBEq.rfl (a := 0)) (by decide)

-- `Std.instLawfulBEqOfLawfulOrderBEqOfIsPartialOrder`, idx 4 (inst : Std.IsPartialOrder α): TrB2 (≤ true, == constantly true, a lawful pair): 0 == 1, 0 ≠ 1
theorem instLawfulBEqOfLawfulOrderBEqOfIsPartialOrder.h4 : ¬ dropu% [0] Std.instLawfulBEqOfLawfulOrderBEqOfIsPartialOrder 4 :=
  fun h => absurd ((h (α := TrB2)).eq_of_beq (a := 0) (b := 1) (by decide)) (by decide)

-- `Std.lt_iff_of_strictMono`, idx 3 (inst : Std.Trichotomous fun x1 x2 => x1 < x2): α = LtF2 (< empty), β = Nat, f = val: f 0 < f 1 but ¬ 0 < 1
theorem lt_iff_of_strictMono.h3 : ¬ dropu% [0, 0] Std.lt_iff_of_strictMono 3 :=
  fun h => absurd (h (α := LtF2) (β := Nat) (f := LtF2.val) (by intro _ _ h; exact h.elim) (x := 0) (y := 1)) (by decide)

-- `Std.inj_of_strictMono`, idx 3 (inst : Std.Trichotomous fun x1 x2 => x1 < x2): α = LtF2 (< empty), β = Nat, f constantly 0: f 0 = f 1, 0 ≠ 1
theorem inj_of_strictMono.h3 : ¬ dropu% [0, 0] Std.inj_of_strictMono 3 :=
  fun h => absurd ((h (α := LtF2) (β := Nat) (f := fun _ => 0) (by intro _ _ h; exact h.elim) (x := 0) (y := 1)).mp rfl) (by decide)

-- `Std.injective_of_strictMono`, idx 3 (inst : Std.Trichotomous fun x1 x2 => x1 < x2): α = LtF2 (< empty), β = Nat, f constantly 0: not injective
theorem injective_of_strictMono.h3 : ¬ dropu% [0, 0] Std.injective_of_strictMono 3 :=
  fun h => by
  have hi := h (α := LtF2) (β := Nat) (f := fun _ => 0) (by intro _ _ h; exact h.elim)
  exact absurd (@hi 0 1 rfl) (by decide)

-- `Std.compare_eq_of_lt_iff`, idx 3 (inst : Std.LawfulOrderLT α): LtF2 (< empty, usual compare), a = 0, b = 1, o = .eq: compare 0 1 = .lt
theorem compare_eq_of_lt_iff.h3 : ¬ dropu% [0] Std.compare_eq_of_lt_iff 3 :=
  fun h => absurd (h (α := LtF2) (a := 0) (b := 1) (o := .eq) (by decide) (by decide)) (by decide)

-- `Std.compare_eq_of_lt_iff`, idx 5 (inst : Std.LawfulOrderOrd α): OrdEq2 (usual order, compare constantly .eq), a = 0, b = 1, o = .lt
theorem compare_eq_of_lt_iff.h5 : ¬ dropu% [0] Std.compare_eq_of_lt_iff 5 :=
  fun h => absurd (h (α := OrdEq2) (a := 0) (b := 1) (o := .lt) (by decide) (by decide)) (by decide)

-- `Std.compare_eq_of_lt_iff`, idx 9 (h₁ : a < b ↔ o = Ordering.lt): usual order on Fin 2 (NatL2), a = 0, b = 1, o = .eq: compare 0 1 = .lt
theorem compare_eq_of_lt_iff.h9 : ¬ dropu% [0] Std.compare_eq_of_lt_iff 9 :=
  fun h => absurd (h (α := NatL2) (a := 0) (b := 1) (o := .eq) (by decide)) (by decide)

-- `Std.compare_eq_of_lt_iff`, idx 10 (h₂ : b < a ↔ o = Ordering.gt): usual order on Fin 2 (NatL2), a = 1, b = 0, o = .eq: compare 1 0 = .gt
theorem compare_eq_of_lt_iff.h10 : ¬ dropu% [0] Std.compare_eq_of_lt_iff 10 :=
  fun h => absurd (h (α := NatL2) (a := 1) (b := 0) (o := .eq) (by decide)) (by decide)

-- `Std.lawfulOrderOrd_compareOfLessAndEq`, idx 3 (inst : Std.Total fun x1 x2 => x1 ≤ x2): Eq2 (≤ is =, < empty): compareOfLessAndEq 0 1 = .gt but ¬ 1 ≤ 0
theorem lawfulOrderOrd_compareOfLessAndEq.h3 : ¬ dropu% [0] Std.lawfulOrderOrd_compareOfLessAndEq 3 :=
  fun h => absurd ((h (α := Eq2)).isGE_compare 0 1) (by decide)

-- `Std.lawfulOrderOrd_compareOfLessAndEq`, idx 4 (inst : Std.Antisymm fun x1 x2 => x1 ≤ x2): Tr2 (≤ true, < empty): compareOfLessAndEq 0 1 = .gt but 0 ≤ 1
theorem lawfulOrderOrd_compareOfLessAndEq.h4 : ¬ dropu% [0] Std.lawfulOrderOrd_compareOfLessAndEq 4 :=
  fun h => absurd ((h (α := Tr2)).isLE_compare 0 1) (by decide)

-- `Std.lawfulOrderOrd_compareOfLessAndEq`, idx 6 (inst : Std.LawfulOrderLT α): LtF2 (usual ≤, < empty): compareOfLessAndEq 0 1 = .gt but 0 ≤ 1
theorem lawfulOrderOrd_compareOfLessAndEq.h6 : ¬ dropu% [0] Std.lawfulOrderOrd_compareOfLessAndEq 6 :=
  fun h => absurd ((h (α := LtF2)).isLE_compare 0 1) (by decide)

-- `maxOn_assoc`, idx 4 (inst : Std.IsLinearPreorder β): Rps3 (rock–paper–scissors ≤), f = id: maxOn (maxOn 0 1) 2 = 2, maxOn 0 (maxOn 1 2) = 0
theorem maxOn_assoc.h4 : ¬ dropu% [0, 1] maxOn_assoc 4 :=
  fun h => absurd (h (β := Rps3) (α := Rps3) (f := id) (x := 0) (y := 1) (z := 2)) (by decide)

-- `minOn_assoc`, idx 4 (inst : Std.IsLinearPreorder β): Rps3 (rock–paper–scissors ≤), f = id: minOn (minOn 0 1) 2 = 2, minOn 0 (minOn 1 2) = 0
theorem minOn_assoc.h4 : ¬ dropu% [0, 1] minOn_assoc 4 :=
  fun h => absurd (h (β := Rps3) (α := Rps3) (f := id) (x := 0) (y := 1) (z := 2)) (by decide)

-- `instAssociativeMaxOnOfIsLinearPreorder`, idx 4 (inst : Std.IsLinearPreorder β): Rps3 (rock–paper–scissors ≤), f = id: as for maxOn_assoc
theorem instAssociativeMaxOnOfIsLinearPreorder.h4 : ¬ dropu% [0, 1] instAssociativeMaxOnOfIsLinearPreorder 4 :=
  fun h => absurd ((h (β := Rps3) (α := Rps3) (f := id)).assoc 0 1 2) (by decide)

-- `Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe`, idx 3 (inst : Std.LawfulOrderOrd α): OrdEq2 (usual order, compare constantly .eq): compare 0 1 = .eq, 0 ≠ 1
theorem instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe.h3 : ¬ dropu% [0] Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe 3 :=
  fun h => absurd ((h (α := OrdEq2)).eq_of_compare (a := 0) (b := 1) (by decide)) (by decide)

-- `Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe`, idx 4 (inst : Std.Antisymm fun x1 x2 => x1 ≤ x2): Tr2 (≤ true, compare constantly .eq, lawful): compare 0 1 = .eq, 0 ≠ 1
theorem instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe.h4 : ¬ dropu% [0] Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe 4 :=
  fun h => absurd ((h (α := Tr2)).eq_of_compare (a := 0) (b := 1) (by decide)) (by decide)

-- `Std.instLawfulEqOrdOfLawfulOrderOrdOfIsPartialOrder`, idx 3 (inst : Std.LawfulOrderOrd α): OrdEq2 (usual order, compare constantly .eq): compare 0 1 = .eq, 0 ≠ 1
theorem instLawfulEqOrdOfLawfulOrderOrdOfIsPartialOrder.h3 : ¬ dropu% [0] Std.instLawfulEqOrdOfLawfulOrderOrdOfIsPartialOrder 3 :=
  fun h => absurd ((h (α := OrdEq2)).eq_of_compare (a := 0) (b := 1) (by decide)) (by decide)

-- `Std.instLawfulEqOrdOfLawfulOrderOrdOfIsPartialOrder`, idx 4 (inst : Std.IsPartialOrder α): Tr2 (≤ true, compare constantly .eq, lawful): compare 0 1 = .eq, 0 ≠ 1
theorem instLawfulEqOrdOfLawfulOrderOrdOfIsPartialOrder.h4 : ¬ dropu% [0] Std.instLawfulEqOrdOfLawfulOrderOrdOfIsPartialOrder 4 :=
  fun h => absurd ((h (α := Tr2)).eq_of_compare (a := 0) (b := 1) (by decide)) (by decide)

-- `Std.instAntisymmLeOfLawfulOrderOrdOfLawfulEqOrd`, idx 3 (inst : Std.LawfulOrderOrd α): TrN2 (≤ true, usual compare): 0 ≤ 1 ≤ 0, 0 ≠ 1
theorem instAntisymmLeOfLawfulOrderOrdOfLawfulEqOrd.h3 : ¬ dropu% [0] Std.instAntisymmLeOfLawfulOrderOrdOfLawfulEqOrd 3 :=
  fun h => absurd ((h (α := TrN2)).antisymm 0 1 trivial trivial) (by decide)

-- `Std.instAntisymmLeOfLawfulOrderOrdOfLawfulEqOrd`, idx 4 (inst : Std.LawfulEqOrd α): Tr2 (≤ true, compare constantly .eq): 0 ≤ 1 ≤ 0, 0 ≠ 1
theorem instAntisymmLeOfLawfulOrderOrdOfLawfulEqOrd.h4 : ¬ dropu% [0] Std.instAntisymmLeOfLawfulOrderOrdOfLawfulEqOrd 4 :=
  fun h => absurd ((h (α := Tr2)).antisymm 0 1 trivial trivial) (by decide)

-- `Std.instOrientedOrdOfLawfulOrderOrd`, idx 3 (inst : Std.LawfulOrderOrd α): OrdLt2 (compare constantly .lt): compare 0 0 = .lt ≠ .gt
theorem instOrientedOrdOfLawfulOrderOrd.h3 : ¬ dropu% [0] Std.instOrientedOrdOfLawfulOrderOrd 3 :=
  fun h => absurd ((h (α := OrdLt2)).eq_swap (a := 0) (b := 0)) (by decide)

-- `Std.instTransOrdOfLawfulOrderOrdOfIsPreorder`, idx 3 (inst : Std.LawfulOrderOrd α): OrdLt2 (usual order, compare constantly .lt): not oriented
theorem instTransOrdOfLawfulOrderOrdOfIsPreorder.h3 : ¬ dropu% [0] Std.instTransOrdOfLawfulOrderOrdOfIsPreorder 3 :=
  fun h => absurd ((h (α := OrdLt2)).eq_swap (a := 0) (b := 0)) (by decide)

-- `Std.instTransOrdOfLawfulOrderOrdOfIsPreorder`, idx 4 (inst : Std.IsPreorder α): Rps3 (rock–paper–scissors ≤ and its lawful compare): 0 ≤ 1 ≤ 2, ¬ 0 ≤ 2
theorem instTransOrdOfLawfulOrderOrdOfIsPreorder.h4 : ¬ dropu% [0] Std.instTransOrdOfLawfulOrderOrdOfIsPreorder 4 :=
  fun h => absurd ((h (α := Rps3)).isLE_trans (a := 0) (b := 1) (c := 2) (by decide) (by decide)) (by decide)

-- `Std.instTotalLeOfLawfulOrderOrd`, idx 3 (inst : Std.LawfulOrderOrd α): LeF2 (≤ empty, usual compare): ¬ 0 ≤ 0
theorem instTotalLeOfLawfulOrderOrd.h3 : ¬ dropu% [0] Std.instTotalLeOfLawfulOrderOrd 3 :=
  fun h => absurd ((h (α := LeF2)).total 0 0) (by decide)

-- `Std.IsLinearPreorder.of_ord`, idx 3 (inst : Std.LawfulOrderOrd α): LeF2 (≤ empty, usual compare, transitive): ¬ 0 ≤ 0
theorem IsLinearPreorder.of_ord.h3 : ¬ dropu% [0] Std.IsLinearPreorder.of_ord 3 :=
  fun h => absurd ((h (α := LeF2)).le_refl 0) (by decide)

-- `Std.IsLinearPreorder.of_ord`, idx 4 (inst : Std.TransOrd α): Rps3 (rock–paper–scissors ≤ and its lawful compare): 0 ≤ 1 ≤ 2, ¬ 0 ≤ 2
theorem IsLinearPreorder.of_ord.h4 : ¬ dropu% [0] Std.IsLinearPreorder.of_ord 4 :=
  fun h => absurd ((h (α := Rps3)).le_trans 0 1 2 (by decide) (by decide)) (by decide)

-- `Std.IsLinearOrder.of_ord`, idx 3 (inst : Std.LawfulOrderOrd α): LeF2 (≤ empty, usual compare): ¬ 0 ≤ 0
theorem IsLinearOrder.of_ord.h3 : ¬ dropu% [0] Std.IsLinearOrder.of_ord 3 :=
  fun h => absurd ((h (α := LeF2)).le_refl 0) (by decide)

-- `Std.IsLinearOrder.of_ord`, idx 4 (inst : Std.TransOrd α): Rps3 (rock–paper–scissors ≤ and its lawful, LawfulEqOrd compare): 0 ≤ 1 ≤ 2, ¬ 0 ≤ 2
theorem IsLinearOrder.of_ord.h4 : ¬ dropu% [0] Std.IsLinearOrder.of_ord 4 :=
  fun h => absurd ((h (α := Rps3)).le_trans 0 1 2 (by decide) (by decide)) (by decide)

-- `Std.IsLinearOrder.of_ord`, idx 5 (inst : Std.LawfulEqOrd α): Tr2 (≤ true, compare constantly .eq): 0 ≤ 1 ≤ 0, 0 ≠ 1
theorem IsLinearOrder.of_ord.h5 : ¬ dropu% [0] Std.IsLinearOrder.of_ord 5 :=
  fun h => absurd ((h (α := Tr2)).le_antisymm 0 1 trivial trivial) (by decide)

-- `Classical.Order.instLawfulOrderOrd`, idx 2 (inst : Std.Total fun x1 x2 => x1 ≤ x2): Eq2 (≤ is =): the classical compare 0 1 = .gt but ¬ 1 ≤ 0
theorem Classical.Order.instLawfulOrderOrd.h2 : ¬ dropu% [0] Classical.Order.instLawfulOrderOrd 2 :=
  fun h => by
  have := (h (α := Eq2)).isGE_compare 0 1
  have h01 : ¬ (0 : Eq2) ≤ 1 := by decide
  simp [compare, h01] at this
  exact absurd this (by decide)

-- `Std.LawfulOrderLeftLeaningMax.of_eq`, idx 4 (min_eq : ∀ (a b : α), max a b = if b ≤ a then a else b): NatL2 (usual order, max the left projection): ¬ 1 ≤ 0 but max 0 1 = 0
theorem LawfulOrderLeftLeaningMax.of_eq.h4 : ¬ dropu% [0] Std.LawfulOrderLeftLeaningMax.of_eq 4 :=
  fun h => absurd ((h (α := NatL2)).max_eq_right 0 1 (by decide)) (by decide)

-- `Std.LawfulOrderLeftLeaningMin.of_eq`, idx 4 (min_eq : ∀ (a b : α), min a b = if a ≤ b then a else b): NatL2 (usual order, min the left projection): ¬ 1 ≤ 0 but min 1 0 = 1
theorem LawfulOrderLeftLeaningMin.of_eq.h4 : ¬ dropu% [0] Std.LawfulOrderLeftLeaningMin.of_eq 4 :=
  fun h => absurd ((h (α := NatL2)).min_eq_right 1 0 (by decide)) (by decide)

-- `Std.instLawfulOrderLeftLeaningMaxOfIsLinearOrderOfLawfulOrderSup`, idx 3 (inst : Std.IsLinearOrder α): TrC2 (≤ true, max constantly 1, LawfulOrderSup): max 0 0 = 1
theorem instLawfulOrderLeftLeaningMaxOfIsLinearOrderOfLawfulOrderSup.h3 : ¬ dropu% [0] Std.instLawfulOrderLeftLeaningMaxOfIsLinearOrderOfLawfulOrderSup 3 :=
  fun h => absurd ((h (α := TrC2)).max_eq_left 0 0 trivial) (by decide)

-- `Std.instLawfulOrderLeftLeaningMaxOfIsLinearOrderOfLawfulOrderSup`, idx 4 (inst : Std.LawfulOrderSup α): NatL2 (usual order, max the left projection): max 0 1 = 0
theorem instLawfulOrderLeftLeaningMaxOfIsLinearOrderOfLawfulOrderSup.h4 : ¬ dropu% [0] Std.instLawfulOrderLeftLeaningMaxOfIsLinearOrderOfLawfulOrderSup 4 :=
  fun h => absurd ((h (α := NatL2)).max_eq_right 0 1 (by decide)) (by decide)

-- `Std.instLawfulOrderLeftLeaningMinOfIsLinearOrderOfLawfulOrderInf`, idx 3 (inst : Std.IsLinearOrder α): TrC2 (≤ true, min constantly 1, LawfulOrderInf): min 0 0 = 1
theorem instLawfulOrderLeftLeaningMinOfIsLinearOrderOfLawfulOrderInf.h3 : ¬ dropu% [0] Std.instLawfulOrderLeftLeaningMinOfIsLinearOrderOfLawfulOrderInf 3 :=
  fun h => absurd ((h (α := TrC2)).min_eq_left 0 0 trivial) (by decide)

-- `Std.instLawfulOrderLeftLeaningMinOfIsLinearOrderOfLawfulOrderInf`, idx 4 (inst : Std.LawfulOrderInf α): NatL2 (usual order, min the left projection): min 1 0 = 1
theorem instLawfulOrderLeftLeaningMinOfIsLinearOrderOfLawfulOrderInf.h4 : ¬ dropu% [0] Std.instLawfulOrderLeftLeaningMinOfIsLinearOrderOfLawfulOrderInf 4 :=
  fun h => absurd ((h (α := NatL2)).min_eq_right 1 0 (by decide)) (by decide)

-- `Std.instLawfulOrderMaxOfIsLinearPreorderOfLawfulOrderLeftLeaningMax`, idx 3 (inst : Std.IsLinearPreorder α): Rps3 (rock–paper–scissors ≤, left-leaning max): max 0 1 = 1 ≤ 2 but ¬ 0 ≤ 2
theorem instLawfulOrderMaxOfIsLinearPreorderOfLawfulOrderLeftLeaningMax.h3 : ¬ dropu% [0] Std.instLawfulOrderMaxOfIsLinearPreorderOfLawfulOrderLeftLeaningMax 3 :=
  fun h => absurd ((h (α := Rps3)).max_le_iff 0 1 2) (by decide)

-- `Std.instLawfulOrderMaxOfIsLinearPreorderOfLawfulOrderLeftLeaningMax`, idx 4 (inst : Std.LawfulOrderLeftLeaningMax α): NatL2 (usual order, max the left projection): max 0 1 = 0 ≤ 0 but ¬ 1 ≤ 0
theorem instLawfulOrderMaxOfIsLinearPreorderOfLawfulOrderLeftLeaningMax.h4 : ¬ dropu% [0] Std.instLawfulOrderMaxOfIsLinearPreorderOfLawfulOrderLeftLeaningMax 4 :=
  fun h => absurd ((h (α := NatL2)).max_le_iff 0 1 0) (by decide)

-- `Std.instLawfulOrderMinOfIsLinearPreorderOfLawfulOrderLeftLeaningMin`, idx 3 (inst : Std.IsLinearPreorder α): Rps3 (rock–paper–scissors ≤, left-leaning min): 2 ≤ min 0 1 = 0 but ¬ 2 ≤ 1
theorem instLawfulOrderMinOfIsLinearPreorderOfLawfulOrderLeftLeaningMin.h3 : ¬ dropu% [0] Std.instLawfulOrderMinOfIsLinearPreorderOfLawfulOrderLeftLeaningMin 3 :=
  fun h => absurd ((h (α := Rps3)).le_min_iff 2 0 1) (by decide)

-- `Std.instLawfulOrderMinOfIsLinearPreorderOfLawfulOrderLeftLeaningMin`, idx 4 (inst : Std.LawfulOrderLeftLeaningMin α): NatL2 (usual order, min the left projection): 1 ≤ min 1 0 = 1 but ¬ 1 ≤ 0
theorem instLawfulOrderMinOfIsLinearPreorderOfLawfulOrderLeftLeaningMin.h4 : ¬ dropu% [0] Std.instLawfulOrderMinOfIsLinearPreorderOfLawfulOrderLeftLeaningMin 4 :=
  fun h => absurd ((h (α := NatL2)).le_min_iff 1 1 0) (by decide)

-- `Std.instCommutativeMinOfLawfulOrderLeftLeaningMinOfIsLinearOrder`, idx 3 (inst : Std.LawfulOrderLeftLeaningMin α): NatL2 (usual order, min the left projection): min 0 1 = 0 ≠ 1 = min 1 0
theorem instCommutativeMinOfLawfulOrderLeftLeaningMinOfIsLinearOrder.h3 : ¬ dropu% [0] Std.instCommutativeMinOfLawfulOrderLeftLeaningMinOfIsLinearOrder 3 :=
  fun h => absurd ((h (α := NatL2)).comm 0 1) (by decide)

-- `Std.instCommutativeMinOfLawfulOrderLeftLeaningMinOfIsLinearOrder`, idx 4 (inst : Std.IsLinearOrder α): Tr2 (≤ true, left-leaning min = left projection): min 0 1 = 0 ≠ 1 = min 1 0
theorem instCommutativeMinOfLawfulOrderLeftLeaningMinOfIsLinearOrder.h4 : ¬ dropu% [0] Std.instCommutativeMinOfLawfulOrderLeftLeaningMinOfIsLinearOrder 4 :=
  fun h => absurd ((h (α := Tr2)).comm 0 1) (by decide)

-- `Std.instAssociativeMinOfIsLinearOrderOfLawfulOrderMin`, idx 3 (inst : Std.IsLinearOrder α): TrR3 (≤ true, min the rock–paper–scissors selection): min (min 0 1) 2 = 2, min 0 (min 1 2) = 0
theorem instAssociativeMinOfIsLinearOrderOfLawfulOrderMin.h3 : ¬ dropu% [0] Std.instAssociativeMinOfIsLinearOrderOfLawfulOrderMin 3 :=
  fun h => absurd ((h (α := TrR3)).assoc 0 1 2) (by decide)

-- `Std.instAssociativeMinOfIsLinearOrderOfLawfulOrderMin`, idx 4 (inst : Std.LawfulOrderMin α): NatR3 (usual order on Fin 3, min the rock–paper–scissors selection): not associative
theorem instAssociativeMinOfIsLinearOrderOfLawfulOrderMin.h4 : ¬ dropu% [0] Std.instAssociativeMinOfIsLinearOrderOfLawfulOrderMin 4 :=
  fun h => absurd ((h (α := NatR3)).assoc 0 1 2) (by decide)

-- `Std.instAssociativeMaxOfIsLinearOrderOfLawfulOrderMax`, idx 3 (inst : Std.IsLinearOrder α): TrR3 (≤ true, max the rock–paper–scissors selection): max (max 0 1) 2 = 2, max 0 (max 1 2) = 0
theorem instAssociativeMaxOfIsLinearOrderOfLawfulOrderMax.h3 : ¬ dropu% [0] Std.instAssociativeMaxOfIsLinearOrderOfLawfulOrderMax 3 :=
  fun h => absurd ((h (α := TrR3)).assoc 0 1 2) (by decide)

-- `Std.instAssociativeMaxOfIsLinearOrderOfLawfulOrderMax`, idx 4 (inst : Std.LawfulOrderMax α): NatR3 (usual order on Fin 3, max the rock–paper–scissors selection): not associative
theorem instAssociativeMaxOfIsLinearOrderOfLawfulOrderMax.h4 : ¬ dropu% [0] Std.instAssociativeMaxOfIsLinearOrderOfLawfulOrderMax 4 :=
  fun h => absurd ((h (α := NatR3)).assoc 0 1 2) (by decide)

-- `Std.instMinEqOrOfIsLinearOrderOfLawfulOrderInf`, idx 3 (inst : Std.IsLinearOrder α): TrC2 (≤ true, min constantly 1): min 0 0 = 1
theorem instMinEqOrOfIsLinearOrderOfLawfulOrderInf.h3 : ¬ dropu% [0] Std.instMinEqOrOfIsLinearOrderOfLawfulOrderInf 3 :=
  fun h => absurd ((h (α := TrC2)).min_eq_or 0 0) (by decide)

-- `Std.instMinEqOrOfIsLinearOrderOfLawfulOrderInf`, idx 4 (inst : Std.LawfulOrderInf α): NatC2 (usual order, min constantly 1): min 0 0 = 1
theorem instMinEqOrOfIsLinearOrderOfLawfulOrderInf.h4 : ¬ dropu% [0] Std.instMinEqOrOfIsLinearOrderOfLawfulOrderInf 4 :=
  fun h => absurd ((h (α := NatC2)).min_eq_or 0 0) (by decide)

-- `Std.instMaxEqOrOfIsLinearOrderOfLawfulOrderSup`, idx 3 (inst : Std.IsLinearOrder α): TrC2 (≤ true, max constantly 1): max 0 0 = 1
theorem instMaxEqOrOfIsLinearOrderOfLawfulOrderSup.h3 : ¬ dropu% [0] Std.instMaxEqOrOfIsLinearOrderOfLawfulOrderSup 3 :=
  fun h => absurd ((h (α := TrC2)).max_eq_or 0 0) (by decide)

-- `Std.instMaxEqOrOfIsLinearOrderOfLawfulOrderSup`, idx 4 (inst : Std.LawfulOrderSup α): NatC2 (usual order, max constantly 1): max 0 0 = 1
theorem instMaxEqOrOfIsLinearOrderOfLawfulOrderSup.h4 : ¬ dropu% [0] Std.instMaxEqOrOfIsLinearOrderOfLawfulOrderSup 4 :=
  fun h => absurd ((h (α := NatC2)).max_eq_or 0 0) (by decide)

-- `Std.instMinEqOrOfLawfulOrderLeftLeaningMin`, idx 3 (inst : Std.LawfulOrderLeftLeaningMin α): NatC2 (min constantly 1): min 0 0 = 1
theorem instMinEqOrOfLawfulOrderLeftLeaningMin.h3 : ¬ dropu% [0] Std.instMinEqOrOfLawfulOrderLeftLeaningMin 3 :=
  fun h => absurd ((h (α := NatC2)).min_eq_or 0 0) (by decide)

-- `Std.instMaxEqOrOfLawfulOrderLeftLeaningMax`, idx 3 (inst : Std.LawfulOrderLeftLeaningMax α): NatC2 (max constantly 1): max 0 0 = 1
theorem instMaxEqOrOfLawfulOrderLeftLeaningMax.h3 : ¬ dropu% [0] Std.instMaxEqOrOfLawfulOrderLeftLeaningMax 3 :=
  fun h => absurd ((h (α := NatC2)).max_eq_or 0 0) (by decide)

-- `Std.lawfulOrderSup_maxOfLe`, idx 4 (inst : Std.Total fun x1 x2 => x1 ≤ x2): Eq2 (≤ is =, transitive): maxOfLe 0 1 = 0 ≤ 0 but ¬ 1 ≤ 0
theorem lawfulOrderSup_maxOfLe.h4 : ¬ dropu% [0] Std.lawfulOrderSup_maxOfLe 4 :=
  fun h => absurd ((h (α := Eq2)).max_le_iff 0 1 0) (by decide)

-- `Std.instIrreflLtOfIsPreorderOfLawfulOrderLT`, idx 3 (inst : Std.LawfulOrderLT α): LtT2 (< true): 0 < 0
theorem instIrreflLtOfIsPreorderOfLawfulOrderLT.h3 : ¬ dropu% [0] Std.instIrreflLtOfIsPreorderOfLawfulOrderLT 3 :=
  fun h => (h (α := LtT2)).irrefl 0 trivial

-- `Std.instAsymmLtOfLawfulOrderLT`, idx 3 (inst : Std.LawfulOrderLT α): LtT2 (< true): 0 < 0
theorem instAsymmLtOfLawfulOrderLT.h3 : ¬ dropu% [0] Std.instAsymmLtOfLawfulOrderLT 3 :=
  fun h => (h (α := LtT2)).asymm 0 0 trivial trivial

-- `Std.instAntisymmLtOfLawfulOrderLTOfLe`, idx 3 (inst : Std.LawfulOrderLT α): LtT2 (< true, ≤ is =): 0 < 1 < 0, 0 ≠ 1
theorem instAntisymmLtOfLawfulOrderLTOfLe.h3 : ¬ dropu% [0] Std.instAntisymmLtOfLawfulOrderLTOfLe 3 :=
  fun h => absurd ((@h LtT2 inferInstance _ _).antisymm 0 1 trivial trivial) (by decide)

-- `Std.instTotalNotLtOfLawfulOrderLTOfLe`, idx 3 (inst : Std.LawfulOrderLT α): LtT2 (< true): ¬ 0 < 0 fails
theorem instTotalNotLtOfLawfulOrderLTOfLe.h3 : ¬ dropu% [0] Std.instTotalNotLtOfLawfulOrderLTOfLe 3 :=
  fun h => absurd ((@h LtT2 inferInstance _).total 0 0) (by decide)

-- `Std.instTrichotomousLtOfLawfulOrderLTOfTotalOfAntisymmLe`, idx 3 (inst : Std.LawfulOrderLT α): LtF2 (< empty, usual ≤): ¬ 0 < 1, ¬ 1 < 0, 0 ≠ 1
theorem instTrichotomousLtOfLawfulOrderLTOfTotalOfAntisymmLe.h3 : ¬ dropu% [0] Std.instTrichotomousLtOfLawfulOrderLTOfTotalOfAntisymmLe 3 :=
  fun h => absurd ((@h LtF2 inferInstance _ _ _).trichotomous 0 1 (by decide) (by decide)) (by decide)

-- `Std.instTrichotomousLtOfLawfulOrderLTOfTotalOfAntisymmLe`, idx 4 (inst : Std.Total fun x1 x2 => x1 ≤ x2): Eq2 (≤ is =, < empty and lawful): ¬ 0 < 1, ¬ 1 < 0, 0 ≠ 1
theorem instTrichotomousLtOfLawfulOrderLTOfTotalOfAntisymmLe.h4 : ¬ dropu% [0] Std.instTrichotomousLtOfLawfulOrderLTOfTotalOfAntisymmLe 4 :=
  fun h => absurd ((@h Eq2 inferInstance _ _ _).trichotomous 0 1 (by decide) (by decide)) (by decide)

-- `Std.instTrichotomousLtOfLawfulOrderLTOfTotalOfAntisymmLe`, idx 5 (inst : Std.Antisymm fun x1 x2 => x1 ≤ x2): Tr2 (≤ true, < empty and lawful): ¬ 0 < 1, ¬ 1 < 0, 0 ≠ 1
theorem instTrichotomousLtOfLawfulOrderLTOfTotalOfAntisymmLe.h5 : ¬ dropu% [0] Std.instTrichotomousLtOfLawfulOrderLTOfTotalOfAntisymmLe 5 :=
  fun h => absurd ((@h Tr2 inferInstance _ _ _).trichotomous 0 1 (by decide) (by decide)) (by decide)

-- `Std.instAntisymmLeOfLawfulOrderLTOfTrichotomousLt`, idx 3 (inst : Std.LawfulOrderLT α): TrN2 (≤ true, usual <): 0 ≤ 1 ≤ 0, 0 ≠ 1
theorem instAntisymmLeOfLawfulOrderLTOfTrichotomousLt.h3 : ¬ dropu% [0] Std.instAntisymmLeOfLawfulOrderLTOfTrichotomousLt 3 :=
  fun h => absurd ((@h TrN2 inferInstance _ _).antisymm 0 1 trivial trivial) (by decide)

-- `Std.instAntisymmLeOfLawfulOrderLTOfTrichotomousLt`, idx 4 (inst : Std.Trichotomous fun x1 x2 => x1 < x2): Tr2 (≤ true, < empty and lawful): 0 ≤ 1 ≤ 0, 0 ≠ 1
theorem instAntisymmLeOfLawfulOrderLTOfTrichotomousLt.h4 : ¬ dropu% [0] Std.instAntisymmLeOfLawfulOrderLTOfTrichotomousLt 4 :=
  fun h => absurd ((@h Tr2 inferInstance _ _).antisymm 0 1 trivial trivial) (by decide)

-- `Std.instAntisymmLeOfIsPartialOrder`, idx 2 (inst : Std.IsPartialOrder α): Tr2 (≤ true): 0 ≤ 1 ≤ 0, 0 ≠ 1
theorem instAntisymmLeOfIsPartialOrder.h2 : ¬ dropu% [0] Std.instAntisymmLeOfIsPartialOrder 2 :=
  fun h => absurd ((h (α := Tr2)).antisymm 0 1 trivial trivial) (by decide)

-- `Std.instTotalLeOfIsLinearPreorder`, idx 2 (inst : Std.IsLinearPreorder α): LeF2 (≤ empty): ¬ 0 ≤ 0
theorem instTotalLeOfIsLinearPreorder.h2 : ¬ dropu% [0] Std.instTotalLeOfIsLinearPreorder 2 :=
  fun h => absurd ((h (α := LeF2)).total 0 0) (by decide)

-- `Std.Total.asymm_of_total_not`, idx 2 (i : Std.Total fun x1 x2 => ¬r x1 x2): r true on Bool
theorem Total.asymm_of_total_not.h2 : ¬ dropu% [1] Std.Total.asymm_of_total_not 2 :=
  fun h => (h (α := Bool) (r := fun _ _ => True)).asymm true true trivial trivial

-- `Std.instReflOfTotal`, idx 2 (inst : Std.Total r): r false on Bool
theorem instReflOfTotal.h2 : ¬ dropu% [1] Std.instReflOfTotal 2 :=
  fun h => (h (α := Bool) (fun _ _ => False)).refl true

-- `Std.total_of_not_rel_swap_imp_rel`, idx 2 (h : ∀ {a b : α}, ¬r a b → r b a): r false on Bool
theorem total_of_not_rel_swap_imp_rel.h2 : ¬ dropu% [1] Std.total_of_not_rel_swap_imp_rel 2 :=
  fun h => ((h (α := Bool) (r := fun _ _ => False)).total true true).elim id id

-- `Std.instTrichotomousOfTotal`, idx 2 (inst : Std.Total r): r false on Bool: true ≠ false
theorem instTrichotomousOfTotal.h2 : ¬ dropu% [1] Std.instTrichotomousOfTotal 2 :=
  fun h => absurd ((h (α := Bool) (fun _ _ => False)).trichotomous true false id id) (by decide)

-- `Std.Antisymm.trichotomous_of_antisymm_not`, idx 2 (i : Std.Antisymm fun x1 x2 => ¬r x1 x2): r false on Bool: true ≠ false
theorem Antisymm.trichotomous_of_antisymm_not.h2 : ¬ dropu% [1] Std.Antisymm.trichotomous_of_antisymm_not 2 :=
  fun h => absurd ((h (α := Bool) (r := fun _ _ => False)).trichotomous true false id id) (by decide)

-- `Std.trichotomous_of_rel_or_eq_or_rel_swap`, idx 2 (h : ∀ {a b : α}, r a b ∨ a = b ∨ r b a): r false on Bool: true ≠ false
theorem trichotomous_of_rel_or_eq_or_rel_swap.h2 : ¬ dropu% [1] Std.trichotomous_of_rel_or_eq_or_rel_swap 2 :=
  fun h => absurd ((h (α := Bool) (r := fun _ _ => False)).trichotomous true false id id) (by decide)

-- `Std.Trichotomous.antisymm_not`, idx 2 (i : Std.Trichotomous r): r false on Bool: ¬ r is true, true ≠ false
theorem Trichotomous.antisymm_not.h2 : ¬ dropu% [1] Std.Trichotomous.antisymm_not 2 :=
  fun h => absurd ((h (α := Bool) (r := fun _ _ => False)).antisymm true false id id) (by decide)

-- `Std.instAntisymmOfAsymm`, idx 2 (inst : Std.Asymm r): r true on Bool: true ≠ false
theorem instAntisymmOfAsymm.h2 : ¬ dropu% [1] Std.instAntisymmOfAsymm 2 :=
  fun h => absurd ((h (α := Bool) (fun _ _ => True)).antisymm true false trivial trivial) (by decide)

-- `Std.total_of_refl_of_trichotomous`, idx 2 (inst : Std.Refl r): r false on Unit (trichotomous, not reflexive)
theorem total_of_refl_of_trichotomous.h2 : ¬ dropu% [1] Std.total_of_refl_of_trichotomous 2 :=
  fun h => ((@h Unit (fun _ _ => False) ⟨fun _ _ _ _ => rfl⟩).total () ()).elim id id

-- `Std.total_of_refl_of_trichotomous`, idx 3 (inst : Std.Trichotomous r): r is = on Bool (reflexive, not total)
theorem total_of_refl_of_trichotomous.h3 : ¬ dropu% [1] Std.total_of_refl_of_trichotomous 3 :=
  fun h => absurd ((@h Bool (· = ·) ⟨fun _ => rfl⟩).total true false) (by decide)

-- `Std.asymm_of_irrefl_of_antisymm`, idx 2 (inst : Std.Irrefl r): r true on Unit (antisymmetric, not irreflexive)
theorem asymm_of_irrefl_of_antisymm.h2 : ¬ dropu% [1] Std.asymm_of_irrefl_of_antisymm 2 :=
  fun h => (@h Unit (fun _ _ => True) ⟨fun _ _ _ _ => rfl⟩).asymm () () trivial trivial

-- `Std.asymm_of_irrefl_of_antisymm`, idx 3 (inst : Std.Antisymm r): r is ≠ on Bool (irreflexive, not antisymmetric)
theorem asymm_of_irrefl_of_antisymm.h3 : ¬ dropu% [1] Std.asymm_of_irrefl_of_antisymm 3 :=
  fun h => (@h Bool (· ≠ ·) ⟨fun _ h => h rfl⟩).asymm true false (by decide) (by decide)

end OrderLemmasHand
