/-!
Hand resolution of the 50 hypotheses that `HypCheck.lean` left unresolved in the small `Init.Data`
folders `Function`, `AC`, `BEq`, `Prod`, `LawfulHashable`, `NeZero`, `Erased`, `PLift` and `ULift`.
For each hypothesis `hᵢ` of theorem `T`, this file proves `¬T'` (the theorem without `hᵢ` is
false): all 50 are necessary. Universe-polymorphic theorems are refuted at `Type`, which refutes
them at all universes. The `ac_rfl` lemmas are refuted with small contexts over `Nat`: `ctxAdd`
(`+`, commutative) and `ctxLeft` (`fun a _ => a`, associative but not commutative).

Run with the lean4 repo's stage1 binary: `lean checks/SmallHand.lean`.
-/

set_option linter.deprecated false
set_option warn.classDefReducibility false
set_option linter.unusedVariables false

namespace SmallHand
open Lean.Data.AC

/-- Context with `op = (· + ·)`, variable values `vs`, and `arbitrary = arb`. -/
def ctxAdd (vs : List Nat) (arb : Nat) : Context Nat where
  op := (· + ·)
  assoc := ⟨Nat.add_assoc⟩
  comm := none
  idem := none
  vars := vs.map fun v => ⟨v, none⟩
  arbitrary := arb

/-- Context with the left projection `op a b = a` (associative, not commutative). -/
def ctxLeft (vs : List Nat) : Context Nat where
  op := fun a _ => a
  assoc := ⟨fun _ _ _ => rfl⟩
  comm := none
  idem := none
  vars := vs.map fun v => ⟨v, none⟩
  arbitrary := 0

theorem addComm (vs : List Nat) (arb : Nat) : Std.Commutative (ctxAdd vs arb).op := ⟨Nat.add_comm⟩

/-- Never true. -/
def falseBEq : BEq Nat := ⟨fun _ _ => false⟩
/-- Always true. -/
def trueBEq : BEq Nat := ⟨fun _ _ => true⟩
/-- `≤`: reflexive and transitive, not symmetric. -/
def leBEq : BEq Nat := ⟨fun a b => decide (a ≤ b)⟩
/-- Equality of `n / 2`: an equivalence, not equality. -/
def halfBEq : BEq Nat := ⟨fun a b => a / 2 == b / 2⟩
instance halfReflBEq : @ReflBEq Nat halfBEq := @ReflBEq.mk Nat halfBEq fun {a} => by
  show (a / 2 == a / 2) = true; simp

end SmallHand

open SmallHand Lean.Data.AC

/-! # Init.Data.AC -/

-- `Lean.Data.AC.Context.evalList_sort_congr` (`h`, commutativity): left projection with values
-- `[5, 7, 5]`, `a = [0]`, `b = [2]` (both evaluate to 5), `c = [1]`: the results are the head
-- variables `0` and `1` of `[0, 1]` and `[1, 2]`, so `5 ≠ 7`.
example : ¬ ∀ {α : Type} {a b c : List Nat} (ctx : Context α),
    evalList α ctx a = evalList α ctx b → a ≠ [] → b ≠ [] →
    evalList α ctx (sort.loop a c) = evalList α ctx (sort.loop b c) := fun H =>
  absurd (H (a := [0]) (b := [2]) (c := [1]) (ctxLeft [5, 7, 5]) (by decide) (by decide)
    (by decide)) (by decide)

-- `Lean.Data.AC.Context.evalList_sort_congr` (`h₂`): `+` with values `[5, 3]`, `a = [0]`,
-- `b = [1]`, `c = []`: `5 ≠ 3`.
example : ¬ ∀ {α : Type} {a b c : List Nat} (ctx : Context α), Std.Commutative ctx.op →
    a ≠ [] → b ≠ [] →
    evalList α ctx (sort.loop a c) = evalList α ctx (sort.loop b c) := fun H =>
  absurd (H (a := [0]) (b := [1]) (c := []) (ctxAdd [5, 3] 0) (addComm _ _) (by decide)
    (by decide)) (by decide)

-- `Lean.Data.AC.Context.evalList_sort_congr` (`h₃`): `+` with values `[5, 3]`, `arbitrary = 5`,
-- `a = []`, `b = [0]` (both evaluate to 5), `c = [1]`: `3 ≠ 5 + 3`.
example : ¬ ∀ {α : Type} {a b c : List Nat} (ctx : Context α), Std.Commutative ctx.op →
    evalList α ctx a = evalList α ctx b → b ≠ [] →
    evalList α ctx (sort.loop a c) = evalList α ctx (sort.loop b c) := fun H =>
  absurd (H (a := []) (b := [0]) (c := [1]) (ctxAdd [5, 3] 5) (addComm _ _) (by decide)
    (by decide)) (by decide)

-- `Lean.Data.AC.Context.evalList_sort_congr` (`h₄`): the mirror image, `a = [0]`, `b = []`.
example : ¬ ∀ {α : Type} {a b c : List Nat} (ctx : Context α), Std.Commutative ctx.op →
    evalList α ctx a = evalList α ctx b → a ≠ [] →
    evalList α ctx (sort.loop a c) = evalList α ctx (sort.loop b c) := fun H =>
  absurd (H (a := [0]) (b := []) (c := [1]) (ctxAdd [5, 3] 5) (addComm _ _) (by decide)
    (by decide)) (by decide)

-- `Lean.Data.AC.Context.evalList_insert` (`h`): left projection with values `[0, 1]`, `x = 1`,
-- `xs = [0]`: `insert 1 [0] = [0, 1]` evaluates to 0, `[1, 0]` to 1.
example : ¬ ∀ {α : Type} (ctx : Context α) (x : Nat) (xs : List Nat),
    evalList α ctx (Lean.Data.AC.insert x xs) = evalList α ctx (x :: xs) := fun H =>
  absurd (H (ctxLeft [0, 1]) 1 [0]) (by decide)

-- `Lean.Data.AC.Context.evalList_mergeIdem` (`h`): `+` (not idempotent, `idem = none`) with value
-- `[1]`, `e = [0, 0]`: `1 ≠ 1 + 1`.
example : ¬ ∀ {α : Type} (ctx : Context α) (e : List Nat),
    evalList α ctx (mergeIdem e) = evalList α ctx e := fun H =>
  absurd (H (ctxAdd [1] 0) [0, 0]) (by decide)

-- `Lean.Data.AC.Context.evalList_sort_loop_swap` (`h`): left projection with values `[0, 1]`,
-- `y = 1`, `xs = [0]`, `ys = []`: `[0, 1]` vs `[1, 0]`.
example : ¬ ∀ {α : Type} {y : Nat} (ctx : Context α) (xs ys : List Nat),
    evalList α ctx (sort.loop xs (y :: ys)) = evalList α ctx (sort.loop (y :: xs) ys) := fun H =>
  absurd (H (y := 1) (ctxLeft [0, 1]) [0] []) (by decide)

-- `Lean.Data.AC.Context.evalList_sort_cons` (`h`): left projection with values `[0, 1]`, `x = 1`,
-- `xs = [0]`: `sort [1, 0] = [0, 1]` vs `[1, 0]`.
example : ¬ ∀ {α : Type} (ctx : Context α) (x : Nat) (xs : List Nat),
    evalList α ctx (sort (x :: xs)) = evalList α ctx (x :: sort xs) := fun H =>
  absurd (H (ctxLeft [0, 1]) 1 [0]) (by decide)

-- `Lean.Data.AC.Context.evalList_sort` (`h`): left projection (`comm = none`) with values
-- `[0, 1]`, `e = [1, 0]`: `sort [1, 0] = [0, 1]` evaluates to 0, `[1, 0]` to 1.
example : ¬ ∀ {α : Type} (ctx : Context α) (e : List Nat),
    evalList α ctx (sort e) = evalList α ctx e := fun H =>
  absurd (H (ctxLeft [0, 1]) [1, 0]) (by decide)

-- `Lean.Data.AC.Context.unwrap_isNeutral` (`a`): `+` with value `[1]`, `x = 0`: 1 is not a
-- neutral element of `+` (`1 + 0 ≠ 0`).
example : ¬ ∀ {α : Type} {ctx : Context α} {x : Nat},
    Std.LawfulIdentity (EvalInformation.evalOp ctx) (EvalInformation.evalVar (β := α) ctx x) :=
  fun H => absurd ((H (ctx := ctxAdd [1] 0) (x := 0)).toLawfulLeftIdentity.left_id 0) (by decide)

-- `Lean.Data.AC.Context.evalList_append` (`h₁`): `+` with value `[0]`, `arbitrary = 1`, `l = []`,
-- `r = [0]`: `evalList [0] = 0`, but `arbitrary + 0 = 1`.
example : ¬ ∀ {α : Type} (ctx : Context α) (l r : List Nat), r ≠ [] →
    evalList α ctx (l.append r) = ctx.op (evalList α ctx l) (evalList α ctx r) := fun H =>
  absurd (H (ctxAdd [0] 1) [] [0] (by decide)) (by decide)

-- `Lean.Data.AC.Context.evalList_append` (`h₂`): the mirror image, `l = [0]`, `r = []`.
example : ¬ ∀ {α : Type} (ctx : Context α) (l r : List Nat), l ≠ [] →
    evalList α ctx (l.append r) = ctx.op (evalList α ctx l) (evalList α ctx r) := fun H =>
  absurd (H (ctxAdd [0] 1) [0] [] (by decide)) (by decide)

-- `Lean.Data.AC.Context.eq_of_norm` (`h`): `+` with values `[0, 1]`, `a = var 0`, `b = var 1`.
example : ¬ ∀ {α : Type} (ctx : Context α) (a b : Lean.Data.AC.Expr),
    eval α ctx a = eval α ctx b := fun H =>
  absurd (H (ctxAdd [0, 1] 0) (.var 0) (.var 1)) (by decide)

/-! # Init.Data.Function -/

-- `Function.Injective.ne` (`a`): `f = id` on `Bool`, `a₁ = a₂ = true`.
example : ¬ ∀ {α β : Type} {f : α → β}, Function.Injective f → ∀ {a₁ a₂ : α}, f a₁ ≠ f a₂ :=
  fun H => H (f := @id Bool) (fun _ _ h => h) (a₁ := true) (a₂ := true) rfl

-- `Function.Surjective.comp` (`hg`): `g = fun _ => true`, `f = id` on `Bool`.
example : ¬ ∀ {α β γ : Type} {g : β → γ} {f : α → β},
    Function.Surjective f → Function.Surjective (g ∘ f) := fun H => by
  obtain ⟨a, ha⟩ := H (g := fun _ : Bool => true) (f := @id Bool) (fun b => ⟨b, rfl⟩) false
  exact Bool.noConfusion ha

-- `Function.Surjective.comp` (`hf`): `g = id` on `Bool`, `f = fun (_ : Unit) => true`.
example : ¬ ∀ {α β γ : Type} {g : β → γ} {f : α → β},
    Function.Surjective g → Function.Surjective (g ∘ f) := fun H => by
  obtain ⟨a, ha⟩ := H (g := @id Bool) (f := fun _ : Unit => true) (fun b => ⟨b, rfl⟩) false
  exact Bool.noConfusion ha

-- `Function.Injective.comp` (`hg`): `g = fun (_ : Bool) => ()`, `f = id` on `Bool`.
example : ¬ ∀ {α β γ : Type} {g : β → γ} {f : α → β},
    Function.Injective f → Function.Injective (g ∘ f) := fun H =>
  Bool.noConfusion (H (g := fun _ : Bool => ()) (f := @id Bool) (fun _ _ h => h)
    (a₁ := true) (a₂ := false) rfl)

-- `Function.Injective.comp` (`hf`): `g = id` on `Unit`, `f = fun (_ : Bool) => ()`.
example : ¬ ∀ {α β γ : Type} {g : β → γ} {f : α → β},
    Function.Injective g → Function.Injective (g ∘ f) := fun H =>
  Bool.noConfusion (H (g := @id Unit) (f := fun _ : Bool => ()) (fun _ _ h => h)
    (a₁ := true) (a₂ := false) rfl)

-- `Function.Injective.eq_iff'` (`h`): `f = id` on `Bool`, `a = b = true`, `c = false`.
example : ¬ ∀ {α β : Type} {f : α → β}, Function.Injective f → ∀ {a b : α} {c : β},
    (f a = c ↔ a = b) := fun H =>
  Bool.noConfusion ((H (f := @id Bool) (fun _ _ h => h) (a := true) (b := true) (c := false)).mpr
    rfl)

-- `Function.Injective.ne_iff'` (`h`): `f = id` on `Bool`, `x = y = true`, `z = false`.
example : ¬ ∀ {α β : Type} {f : α → β}, Function.Injective f → ∀ {x y : α} {z : β},
    (f x ≠ z ↔ x ≠ y) := fun H =>
  (H (f := @id Bool) (fun _ _ h => h) (x := true) (y := true) (z := false)).mp (by decide) rfl

-- `Function.Injective.exists_leftInverse` (`hf`): `f = fun (_ : Bool) => ()`: a left inverse
-- would send `()` to both `true` and `false`.
example : ¬ ∀ {α β : Type} {f : α → β} [hα : Nonempty α], ∃ g : β → α,
    Function.LeftInverse g f := fun H => by
  obtain ⟨g, hg⟩ := H (f := fun _ : Bool => ())
  exact Bool.noConfusion ((hg true).symm.trans (hg false))

-- `Function.Injective.exists_leftInverse` (`hα`): `α = Empty`, `β = Unit`: there is no map
-- `Unit → Empty`.
example : ¬ ∀ {α β : Type} {f : α → β}, Function.Injective f → ∃ g : β → α,
    Function.LeftInverse g f := fun H => by
  obtain ⟨g, _⟩ := H (f := fun e : Empty => nomatch e) (fun a => nomatch a)
  exact nomatch g ()

-- `Function.Injective.leftInverse` (`hf`): as for `exists_leftInverse`.
example : ¬ ∀ {α β : Type} (f : α → β) [hα : Nonempty α], ∃ g : β → α,
    Function.LeftInverse g f := fun H => by
  obtain ⟨g, hg⟩ := H (fun _ : Bool => ())
  exact Bool.noConfusion ((hg true).symm.trans (hg false))

-- `Function.Injective.leftInverse` (`hα`): as for `exists_leftInverse`.
example : ¬ ∀ {α β : Type} (f : α → β), Function.Injective f → ∃ g : β → α,
    Function.LeftInverse g f := fun H => by
  obtain ⟨g, _⟩ := H (fun e : Empty => (nomatch e : Unit)) (fun a => nomatch a)
  exact nomatch g ()

-- `Function.RightInverse.id` (`h`): `g = id`, `f = fun _ => true` on `Bool`.
example : ¬ ∀ {α β : Type} {g : β → α} {f : α → β}, f ∘ g = id := fun H =>
  Bool.noConfusion (congrFun (H (g := @id Bool) (f := fun _ : Bool => true)) false)

-- `Function.LeftInverse.id` (`h`): `f = id`, `g = fun _ => true` on `Bool`.
example : ¬ ∀ {α β : Type} {g : β → α} {f : α → β}, g ∘ f = id := fun H =>
  Bool.noConfusion (congrFun (H (g := fun _ : Bool => true) (f := @id Bool)) false)

-- `Function.HasRightInverse.surjective` (`a`): `f = fun (_ : Unit) => true` misses `false`.
example : ¬ ∀ {α β : Type} {f : α → β}, Function.Surjective f := fun H => by
  obtain ⟨_, h⟩ := H (f := fun _ : Unit => true) false
  exact Bool.noConfusion h

-- `Function.RightInverse.surjective` (`h`): `f = fun (_ : Unit) => true`, any `g`.
example : ¬ ∀ {α β : Type} {f : α → β} {g : β → α}, Function.Surjective f := fun H => by
  obtain ⟨_, h⟩ := H (f := fun _ : Unit => true) (g := fun _ => ()) false
  exact Bool.noConfusion h

-- `Function.LeftInverse.injective` (`a`): `f = fun (_ : Bool) => ()`, any `g`.
example : ¬ ∀ {α β : Type} {g : β → α} {f : α → β}, Function.Injective f := fun H =>
  Bool.noConfusion (H (g := fun _ => true) (f := fun _ : Bool => ()) (a₁ := true) (a₂ := false) rfl)

-- `Function.HasLeftInverse.injective` (`a`): `f = fun (_ : Bool) => ()`.
example : ¬ ∀ {α β : Type} {f : α → β}, Function.Injective f := fun H =>
  Bool.noConfusion (H (f := fun _ : Bool => ()) (a₁ := true) (a₂ := false) rfl)

-- `Function.leftInverse_of_surjective_of_rightInverse` (`surjf`): `f = fun (_ : Unit) => true`,
-- `g = fun _ => ()`: `g ∘ f = id` on `Unit`, but `f (g false) = true`.
example : ¬ ∀ {α β : Type} {f : α → β} {g : β → α},
    Function.RightInverse f g → Function.LeftInverse f g := fun H =>
  Bool.noConfusion (H (f := fun _ : Unit => true) (g := fun _ => ()) (fun _ => rfl) false)

-- `Function.leftInverse_of_surjective_of_rightInverse` (`rfg`): `f = id`, `g = not` on `Bool`.
example : ¬ ∀ {α β : Type} {f : α → β} {g : β → α},
    Function.Surjective f → Function.LeftInverse f g := fun H =>
  Bool.noConfusion (H (f := @id Bool) (g := not) (fun b => ⟨b, rfl⟩) true)

-- `Function.rightInverse_of_injective_of_leftInverse` (`injf`): `f = fun (_ : Bool) => ()`,
-- `g = fun _ => true`: `f ∘ g = id` on `Unit`, but `g (f false) = true`.
example : ¬ ∀ {α β : Type} {f : α → β} {g : β → α},
    Function.LeftInverse f g → Function.RightInverse f g := fun H =>
  Bool.noConfusion (H (f := fun _ : Bool => ()) (g := fun _ => true) (fun _ => rfl) false)

-- `Function.rightInverse_of_injective_of_leftInverse` (`lfg`): `f = id`, `g = not` on `Bool`.
example : ¬ ∀ {α β : Type} {f : α → β} {g : β → α},
    Function.Injective f → Function.RightInverse f g := fun H =>
  Bool.noConfusion (H (f := @id Bool) (g := not) (fun _ _ h => h) true)

/-! # Init.Data.BEq, Prod, LawfulHashable -/

-- `equivBEq_of_iff_apply_eq` (`hf`): the never-true `BEq Nat` is not reflexive.
example : ¬ ∀ {α β : Type} [inst : BEq α] (f : α → β), EquivBEq α := fun H =>
  absurd (@ReflBEq.rfl Nat falseBEq (@H Nat Nat falseBEq id).toReflBEq 0) (by decide)

-- `EquivBEq.toReflBEq` (`self`): the never-true `BEq Nat`.
example : ¬ ∀ {α : Type} {inst : BEq α}, ReflBEq α := fun H =>
  absurd (@ReflBEq.rfl Nat falseBEq (@H Nat falseBEq) 0) (by decide)

-- `instEquivBEqOfLawfulBEq` (`inst`): the never-true `BEq Nat`.
example : ¬ ∀ {α : Type} [inst : BEq α], EquivBEq α := fun H =>
  absurd (@ReflBEq.rfl Nat falseBEq (@H Nat falseBEq).toReflBEq 0) (by decide)

-- `EquivBEq.toPartialEquivBEq` (`self`): `BEq Nat` by `≤` is not symmetric (`0 ≤ 1`, not `1 ≤ 0`).
example : ¬ ∀ {α : Type} {inst : BEq α}, PartialEquivBEq α := fun H =>
  absurd (@PartialEquivBEq.symm Nat leBEq (@H Nat leBEq) 0 1 (by decide)) (by decide)

-- `instSymmEqBoolBeqTrueOfPartialEquivBEq` (`inst`): `BEq Nat` by `≤`.
example : ¬ ∀ {α : Type} [inst : BEq α], Std.Symm fun (x1 x2 : α) => (x1 == x2) = true :=
  fun H => absurd ((@H Nat leBEq).symm 0 1 (by decide)) (by decide)

-- `Prod.instReflBEq` (`inst`, `ReflBEq α`): never-true `BEq` on `α = Nat`, `β = Bool`.
example : ¬ ∀ {α β : Type} [inst : BEq α] [inst_1 : BEq β] [ReflBEq β], ReflBEq (α × β) :=
  fun H => absurd (@ReflBEq.rfl (Nat × Bool) _ (@H Nat Bool falseBEq _ _) (0, true)) (by decide)

-- `Prod.instReflBEq` (`inst`, `ReflBEq β`): never-true `BEq` on `β = Nat`, `α = Bool`.
example : ¬ ∀ {α β : Type} [inst : BEq α] [inst_1 : BEq β] [ReflBEq α], ReflBEq (α × β) :=
  fun H => absurd (@ReflBEq.rfl (Bool × Nat) _ (@H Bool Nat _ falseBEq _) (true, 0)) (by decide)

-- `Prod.instLawfulBEq` (`inst`, `LawfulBEq α`): `α = Nat` with `a / 2 == b / 2`, `β = Bool`:
-- `(0, true) == (1, true)` but they differ.
example : ¬ ∀ {α β : Type} [inst : BEq α] [inst_1 : BEq β] [LawfulBEq β], LawfulBEq (α × β) :=
  fun H => absurd (@LawfulBEq.eq_of_beq (Nat × Bool) _ (@H Nat Bool halfBEq _ _) (0, true)
    (1, true) (by decide)) (by decide)

-- `Prod.instLawfulBEq` (`inst`, `LawfulBEq β`): `β = Nat` with `a / 2 == b / 2`, `α = Bool`.
example : ¬ ∀ {α β : Type} [inst : BEq α] [inst_1 : BEq β] [LawfulBEq α], LawfulBEq (α × β) :=
  fun H => absurd (@LawfulBEq.eq_of_beq (Bool × Nat) _ (@H Bool Nat _ halfBEq _) (true, 0)
    (true, 1) (by decide)) (by decide)

-- `LawfulHashable.hash_eq` (`self`): always-true `BEq Nat` with the usual hash: `hash 0 ≠ hash 1`.
example : ¬ ∀ {α : Type} {inst : BEq α} {inst_1 : Hashable α} (a b : α),
    (a == b) = true → hash a = hash b := fun H =>
  absurd (@H Nat trueBEq instHashableNat 0 1 rfl) (by decide)

-- `LawfulHashable.hash_eq` (`a`): usual `BEq Nat` and hash (lawful), `a = 0`, `b = 1`.
example : ¬ ∀ {α : Type} {inst : BEq α} {inst_1 : Hashable α} [self : LawfulHashable α]
    (a b : α), hash a = hash b := fun H =>
  absurd (@H Nat inferInstance instHashableNat inferInstance 0 1) (by decide)

-- `instLawfulHashableOfLawfulBEq` (`inst`): always-true `BEq Nat` with the usual hash.
example : ¬ ∀ {α : Type} [inst : BEq α] [inst_1 : Hashable α], LawfulHashable α := fun H =>
  absurd (@LawfulHashable.hash_eq Nat trueBEq _ (@H Nat trueBEq _) 0 1 rfl) (by decide)

/-! # Init.Data.NeZero, Erased, PLift, ULift -/

-- `NeZero.out` (`self`): `n = (0 : Nat)`.
example : ¬ ∀ {R : Type} {inst : Zero R} {n : R}, n ≠ 0 := fun H => H (n := (0 : Nat)) rfl

-- `Erased.out_inj` (`h`): `Erased.mk true ≠ Erased.mk false`.
example : ¬ ∀ {α : Type} {a b : Erased α}, a = b := fun H => by
  have h := congrArg Erased.out (H (a := Erased.mk true) (b := Erased.mk false))
  rw [Erased.out_mk, Erased.out_mk] at h
  exact Bool.noConfusion h

-- `instSubsingletonPLift` (`inst`): `PLift Bool` has two elements.
example : ¬ ∀ {α : Type}, Subsingleton (PLift α) := fun H =>
  Bool.noConfusion (congrArg PLift.down (@Subsingleton.elim _ (@H Bool) ⟨true⟩ ⟨false⟩))

-- `instSubsingletonULift` (`inst`): `ULift Bool` has two elements.
example : ¬ ∀ {α : Type}, Subsingleton (ULift.{0} α) := fun H =>
  Bool.noConfusion (congrArg ULift.down (@Subsingleton.elim _ (@H Bool) ⟨true⟩ ⟨false⟩))
