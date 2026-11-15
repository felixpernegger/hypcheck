
/-!
Hand resolution of the 76 hypotheses that `HypCheck.lean` left unresolved (after the v5 model
recheck) in the smallest `Init.Data` subfolders: `Sum`, `Dyadic`, `Subtype`, `Char`, `Float`,
`ByteArray` and `FloatArray`. For each hypothesis `hᵢ` of theorem `T`, this file proves either
`T'` (the theorem without `hᵢ`: removable) or `¬T'` (necessary). For dependent hypotheses
necessity means `¬ ∀ indep, Hᵢ` (see `Methods.md`). Universe-polymorphic theorems are refuted
at universe 0, which refutes them at all universes.

Run with the lean4 repo's stage1 binary: `lean checks/DataSmallHand.lean`.
-/

namespace DataSmallHand

theorem not_acc_of_refl {γ : Sort _} {R : γ → γ → Prop} {x : γ} (hx : R x x) : ¬ Acc R x := by
  intro h
  induction h with
  | intro y _ ih => exact ih y hx hx

end DataSmallHand

open DataSmallHand

/-! # Removable (6) -/

/-! ## Dyadic (4) -/

namespace DataSmallHand.Dyadic
open _root_.Dyadic

theorem ofIntWithPrec_one_pos (prec : Int) : (0 : Rat) < (ofIntWithPrec 1 prec).toRat := by
  rw [toRat_ofIntWithPrec_eq_mul_two_pow, Rat.intCast_one, Rat.one_mul]
  exact Rat.zpow_pos (by decide)

-- `Dyadic.eq_divAtPrec` (`hb : 0 < b`), derivable: for `b ≤ 0`, `h1` and `h2` give
-- `y * b ≤ a < y * b + 2^(-prec) * b ≤ y * b`.
theorem eq_divAtPrec_derivable {a b : _root_.Dyadic} {prec : Int} {y : _root_.Dyadic}
    (h1 : y * b ≤ a) (h2 : a < (y + ofIntWithPrec 1 prec) * b) : 0 < b := by
  refine Classical.byContradiction fun hb => ?_
  rw [_root_.Dyadic.not_lt, ← toRat_le_toRat_iff, toRat_zero] at hb
  rw [← toRat_le_toRat_iff, toRat_mul] at h1
  rw [← toRat_lt_toRat_iff, toRat_mul, toRat_add, Rat.add_mul] at h2
  have : 0 ≤ (ofIntWithPrec 1 prec).toRat * -b.toRat :=
    Rat.mul_nonneg (Rat.le_of_lt (ofIntWithPrec_one_pos prec)) (by grind)
  grind

theorem eq_divAtPrec {a b : _root_.Dyadic} {prec : Int} {y : _root_.Dyadic}
    (hp : y.precision ≤ some prec) (h1 : y * b ≤ a)
    (h2 : a < (y + ofIntWithPrec 1 prec) * b) :
    y = divAtPrec a b prec :=
  _root_.Dyadic.eq_divAtPrec (eq_divAtPrec_derivable h1 h2) hp h1 h2

-- `Dyadic.eq_invAtPrec` (`hx : 0 < x`), derivable: the special case `a = 1` of
-- `eq_divAtPrec`.
theorem eq_invAtPrec_derivable {x : _root_.Dyadic} {prec : Int} {y : _root_.Dyadic}
    (h1 : y * x ≤ 1) (h2 : 1 < (y + ofIntWithPrec 1 prec) * x) : 0 < x :=
  eq_divAtPrec_derivable h1 h2

theorem eq_invAtPrec {x : _root_.Dyadic} {prec : Int} {y : _root_.Dyadic}
    (hp : y.precision ≤ some prec) (h1 : y * x ≤ 1)
    (h2 : 1 < (y + ofIntWithPrec 1 prec) * x) :
    y = invAtPrec x prec := by
  rw [invAtPrec_eq_divAtPrec_one]
  exact eq_divAtPrec hp h1 h2

-- `Dyadic.mul_invAtPrec_lt_divAtPrec_add` (`hb : 0 < b`): for `b = 0` both sides are
-- `0 < 2^(-prec)`; the library's proof never uses `b > 0` otherwise.
theorem mul_invAtPrec_lt_divAtPrec_add {a b : _root_.Dyadic} (ha : 0 ≤ a) (prec : Int) :
    a * invAtPrec b prec < divAtPrec a b prec + ofIntWithPrec 1 prec := by
  have har : (0 : Rat) ≤ a.toRat := by rwa [← toRat_le_toRat_iff, toRat_zero] at ha
  rw [← toRat_lt_toRat_iff, toRat_mul]
  unfold invAtPrec divAtPrec
  cases b with
  | zero =>
    simp only [_root_.Dyadic.zero_eq, toRat_add, toRat_zero, Rat.mul_zero, Rat.zero_add]
    exact ofIntWithPrec_one_pos prec
  | ofOdd n k hn =>
    simp only
    have h_le : a.toRat * ((ofOdd n k hn).toRat.inv.toDyadic prec).toRat
              ≤ a.toRat / (ofOdd n k hn).toRat := by
      rw [Rat.div_def]
      exact Rat.mul_le_mul_of_nonneg_left Rat.toRat_toDyadic_le har
    exact Rat.not_le.mp fun h =>
      Rat.not_le.mpr Rat.lt_toRat_toDyadic_add (Rat.le_trans h h_le)

-- `Dyadic.divAtPrec_sub_mul_lt_mul_invAtPrec` (`hb : 0 < b`): for `b = 0` it reads
-- `0 - a * 2^(-prec) < 0`; the library's proof never uses `b > 0` otherwise.
theorem divAtPrec_sub_mul_lt_mul_invAtPrec {a b : _root_.Dyadic} (ha : 0 < a) (prec : Int) :
    divAtPrec a b prec - a * ofIntWithPrec 1 prec < a * invAtPrec b prec := by
  have har : (0 : Rat) < a.toRat := by rwa [← toRat_lt_toRat_iff, toRat_zero] at ha
  rw [← toRat_lt_toRat_iff, toRat_sub, toRat_mul, toRat_mul,
      toRat_ofIntWithPrec_eq_mul_two_pow, Rat.intCast_one, Rat.one_mul, Rat.sub_lt_iff]
  unfold invAtPrec divAtPrec
  cases b with
  | zero =>
    simp only [_root_.Dyadic.zero_eq, toRat_zero, Rat.mul_zero, Rat.zero_add]
    exact Rat.mul_pos har (Rat.zpow_pos (by decide))
  | ofOdd n k hn =>
    simp only
    have h_le : ((a.toRat / (ofOdd n k hn).toRat).toDyadic prec).toRat
              ≤ a.toRat * (ofOdd n k hn).toRat⁻¹ := by
      rw [← Rat.div_def]
      exact Rat.toRat_toDyadic_le
    have h_lt : a.toRat * (ofOdd n k hn).toRat⁻¹
              < a.toRat * ((ofOdd n k hn).toRat.inv.toDyadic prec).toRat
                  + a.toRat * (2 : Rat) ^ (-prec) := by
      calc a.toRat * (ofOdd n k hn).toRat⁻¹
          < a.toRat *
              ((ofOdd n k hn).toRat.inv.toDyadic prec + ofIntWithPrec 1 prec).toRat :=
            Rat.mul_lt_mul_of_pos_left Rat.lt_toRat_toDyadic_add har
        _ = a.toRat * ((ofOdd n k hn).toRat.inv.toDyadic prec).toRat
                + a.toRat * (2 : Rat) ^ (-prec) := by
              rw [toRat_add, toRat_ofIntWithPrec_eq_mul_two_pow,
                  Rat.intCast_one, Rat.one_mul, Rat.mul_add]
    exact Rat.not_le.mp fun h =>
      Rat.not_le.mpr h_lt (Rat.le_trans h h_le)

end DataSmallHand.Dyadic

/-! ## ByteArray (2) -/

-- `ByteArray.getElem_set!` (`h : i < data.size`): out of bounds `set!` does nothing, and then
-- `i ≠ j` because `j < data.size`.
theorem DataSmallHand.ByteArray.getElem_set! (data : ByteArray) (i j : Nat) (v : UInt8)
    (hj : j < data.size) :
    (data.set! i v)[j]'(by rw [ByteArray.size_set!]; exact hj) = if i = j then v else data[j] := by
  by_cases h : i < data.size
  · exact _root_.ByteArray.getElem_set! data i j v h hj
  · split
    · omega
    · exact ByteArray.getElem_set!_ne data i j v (by omega) hj

-- `ByteArray.lt_iff_extract_lt_of_size_le` (`h : b.size ≤ a.size`): if `a.size < b.size`, then
-- `a.extract 0 b.size = a` and both sides agree.
theorem DataSmallHand.ByteArray.lt_iff_extract_lt_of_size_le {a b : ByteArray} :
    a < b ↔ a.extract 0 b.size < b := by
  by_cases h : b.size ≤ a.size
  · exact _root_.ByteArray.lt_iff_extract_lt_of_size_le h
  · have : a.extract 0 b.size = a := by
      apply ByteArray.ext
      simp only [ByteArray.data_extract]
      exact Array.extract_eq_self_of_le (Nat.le_of_lt (Nat.not_le.mp h))
    rw [this]

/-! # Necessary (70) -/

/-! ## Sum (31) -/

-- All counterexamples use `Unit ⊕ Unit` with the constant relations `True`/`False`.

-- `Sum.LiftRel.mono` (`hr`)
example : ¬ ∀ {α α' : Type} {r₁ r₂ : α → α' → Prop} {β β' : Type} {s₁ s₂ : β → β' → Prop}
    {x : α ⊕ β} {y : α' ⊕ β'},
    (∀ a b, s₁ a b → s₂ a b) → Sum.LiftRel r₁ s₁ x y → Sum.LiftRel r₂ s₂ x y := fun h => by
  have := @h Unit Unit (fun _ _ => True) (fun _ _ => False) Unit Unit (fun _ _ => True)
    (fun _ _ => True) (.inl ()) (.inl ()) (fun _ _ h => h) (.inl trivial)
  cases this with | inl h => exact h

-- `Sum.LiftRel.mono` (`hs`)
example : ¬ ∀ {α α' : Type} {r₁ r₂ : α → α' → Prop} {β β' : Type} {s₁ s₂ : β → β' → Prop}
    {x : α ⊕ β} {y : α' ⊕ β'},
    (∀ a b, r₁ a b → r₂ a b) → Sum.LiftRel r₁ s₁ x y → Sum.LiftRel r₂ s₂ x y := fun h => by
  have := @h Unit Unit (fun _ _ => True) (fun _ _ => True) Unit Unit (fun _ _ => True)
    (fun _ _ => False) (.inr ()) (.inr ()) (fun _ _ h => h) (.inr trivial)
  cases this with | inr h => exact h

-- `Sum.LiftRel.mono` (`h`)
example : ¬ ∀ {α α' : Type} {r₁ r₂ : α → α' → Prop} {β β' : Type} {s₁ s₂ : β → β' → Prop}
    {x : α ⊕ β} {y : α' ⊕ β'},
    (∀ a b, r₁ a b → r₂ a b) → (∀ a b, s₁ a b → s₂ a b) → Sum.LiftRel r₂ s₂ x y := fun h => by
  have := @h Unit Unit (fun _ _ => False) (fun _ _ => False) Unit Unit (fun _ _ => False)
    (fun _ _ => False) (.inl ()) (.inl ()) (fun _ _ h => h) (fun _ _ h => h)
  cases this with | inl h => exact h

-- `Sum.LiftRel.mono_left` (`hr`)
example : ¬ ∀ {α α' : Type} {r₁ r₂ : α → α' → Prop} {β β' : Type} {s : β → β' → Prop}
    {x : α ⊕ β} {y : α' ⊕ β'}, Sum.LiftRel r₁ s x y → Sum.LiftRel r₂ s x y := fun h => by
  have := @h Unit Unit (fun _ _ => True) (fun _ _ => False) Unit Unit (fun _ _ => True)
    (.inl ()) (.inl ()) (.inl trivial)
  cases this with | inl h => exact h

-- `Sum.LiftRel.mono_left` (`h`)
example : ¬ ∀ {α α' : Type} {r₁ r₂ : α → α' → Prop} {β β' : Type} {s : β → β' → Prop}
    {x : α ⊕ β} {y : α' ⊕ β'}, (∀ a b, r₁ a b → r₂ a b) → Sum.LiftRel r₂ s x y := fun h => by
  have := @h Unit Unit (fun _ _ => False) (fun _ _ => False) Unit Unit (fun _ _ => False)
    (.inl ()) (.inl ()) (fun _ _ h => h)
  cases this with | inl h => exact h

-- `Sum.LiftRel.mono_right` (`hs`)
example : ¬ ∀ {β β' : Type} {s₁ s₂ : β → β' → Prop} {α α' : Type} {r : α → α' → Prop}
    {x : α ⊕ β} {y : α' ⊕ β'}, Sum.LiftRel r s₁ x y → Sum.LiftRel r s₂ x y := fun h => by
  have := @h Unit Unit (fun _ _ => True) (fun _ _ => False) Unit Unit (fun _ _ => True)
    (.inr ()) (.inr ()) (.inr trivial)
  cases this with | inr h => exact h

-- `Sum.LiftRel.mono_right` (`h`)
example : ¬ ∀ {β β' : Type} {s₁ s₂ : β → β' → Prop} {α α' : Type} {r : α → α' → Prop}
    {x : α ⊕ β} {y : α' ⊕ β'}, (∀ a b, s₁ a b → s₂ a b) → Sum.LiftRel r s₂ x y := fun h => by
  have := @h Unit Unit (fun _ _ => False) (fun _ _ => False) Unit Unit (fun _ _ => False)
    (.inr ()) (.inr ()) (fun _ _ h => h)
  cases this with | inr h => exact h

-- `Sum.LiftRel.swap` (`h`)
example : ¬ ∀ {α α' : Type} {r : α → α' → Prop} {β β' : Type} {s : β → β' → Prop}
    {x : α ⊕ β} {y : α' ⊕ β'}, Sum.LiftRel s r x.swap y.swap := fun h => by
  have := @h Unit Unit (fun _ _ => False) Unit Unit (fun _ _ => False) (.inl ()) (.inl ())
  cases this with | inr h => exact h

-- `Sum.LiftRel.lex` (`h`)
example : ¬ ∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop} {a b : α ⊕ β},
    Sum.Lex r s a b := fun h => by
  have := @h Unit Unit (fun _ _ => False) (fun _ _ => False) (.inl ()) (.inl ())
  cases this with | inl h => exact h

-- `Sum.Lex.mono` (`hr`)
example : ¬ ∀ {α : Type} {r₁ r₂ : α → α → Prop} {β : Type} {s₁ s₂ : β → β → Prop} {x y : α ⊕ β},
    (∀ a b, s₁ a b → s₂ a b) → Sum.Lex r₁ s₁ x y → Sum.Lex r₂ s₂ x y := fun h => by
  have := @h Unit (fun _ _ => True) (fun _ _ => False) Unit (fun _ _ => True) (fun _ _ => True)
    (.inl ()) (.inl ()) (fun _ _ h => h) (.inl trivial)
  cases this with | inl h => exact h

-- `Sum.Lex.mono` (`hs`)
example : ¬ ∀ {α : Type} {r₁ r₂ : α → α → Prop} {β : Type} {s₁ s₂ : β → β → Prop} {x y : α ⊕ β},
    (∀ a b, r₁ a b → r₂ a b) → Sum.Lex r₁ s₁ x y → Sum.Lex r₂ s₂ x y := fun h => by
  have := @h Unit (fun _ _ => True) (fun _ _ => True) Unit (fun _ _ => True) (fun _ _ => False)
    (.inr ()) (.inr ()) (fun _ _ h => h) (.inr trivial)
  cases this with | inr h => exact h

-- `Sum.Lex.mono` (`h`)
example : ¬ ∀ {α : Type} {r₁ r₂ : α → α → Prop} {β : Type} {s₁ s₂ : β → β → Prop} {x y : α ⊕ β},
    (∀ a b, r₁ a b → r₂ a b) → (∀ a b, s₁ a b → s₂ a b) → Sum.Lex r₂ s₂ x y := fun h => by
  have := @h Unit (fun _ _ => False) (fun _ _ => False) Unit (fun _ _ => False)
    (fun _ _ => False) (.inl ()) (.inl ()) (fun _ _ h => h) (fun _ _ h => h)
  cases this with | inl h => exact h

-- `Sum.Lex.mono_left` (`hr`)
example : ¬ ∀ {α : Type} {r₁ r₂ : α → α → Prop} {β : Type} {s : β → β → Prop} {x y : α ⊕ β},
    Sum.Lex r₁ s x y → Sum.Lex r₂ s x y := fun h => by
  have := @h Unit (fun _ _ => True) (fun _ _ => False) Unit (fun _ _ => True)
    (.inl ()) (.inl ()) (.inl trivial)
  cases this with | inl h => exact h

-- `Sum.Lex.mono_left` (`h`)
example : ¬ ∀ {α : Type} {r₁ r₂ : α → α → Prop} {β : Type} {s : β → β → Prop} {x y : α ⊕ β},
    (∀ a b, r₁ a b → r₂ a b) → Sum.Lex r₂ s x y := fun h => by
  have := @h Unit (fun _ _ => False) (fun _ _ => False) Unit (fun _ _ => False)
    (.inl ()) (.inl ()) (fun _ _ h => h)
  cases this with | inl h => exact h

-- `Sum.Lex.mono_right` (`hs`)
example : ¬ ∀ {β : Type} {s₁ s₂ : β → β → Prop} {α : Type} {r : α → α → Prop} {x y : α ⊕ β},
    Sum.Lex r s₁ x y → Sum.Lex r s₂ x y := fun h => by
  have := @h Unit (fun _ _ => True) (fun _ _ => False) Unit (fun _ _ => True)
    (.inr ()) (.inr ()) (.inr trivial)
  cases this with | inr h => exact h

-- `Sum.Lex.mono_right` (`h`)
example : ¬ ∀ {β : Type} {s₁ s₂ : β → β → Prop} {α : Type} {r : α → α → Prop} {x y : α ⊕ β},
    (∀ a b, s₁ a b → s₂ a b) → Sum.Lex r s₂ x y := fun h => by
  have := @h Unit (fun _ _ => False) (fun _ _ => False) Unit (fun _ _ => False)
    (.inr ()) (.inr ()) (fun _ _ h => h)
  cases this with | inr h => exact h

-- `Sum.lex_acc_inl` (`aca`): `r := True` makes `inl ()` its own predecessor.
example : ¬ ∀ {α : Type} {r : α → α → Prop} {a : α} {β : Type} {s : β → β → Prop},
    Acc (Sum.Lex r s) (Sum.inl a) := fun h =>
  not_acc_of_refl (.inl trivial) (@h Unit (fun _ _ => True) () Unit (fun _ _ => False))

-- `Sum.lex_acc_inr` (`aca`): `r := True`, `s := False`; `inl () < inr ()` by `Lex.sep`.
example : ¬ ∀ {α : Type} {r : α → α → Prop} {β : Type} {s : β → β → Prop} {b : β},
    Acc s b → Acc (Sum.Lex r s) (Sum.inr b) := fun h => by
  have := @h Unit (fun _ _ => True) Unit (fun _ _ => False) () ⟨_, fun _ h => h.elim⟩
  exact not_acc_of_refl (.inl trivial) (this.inv (.sep () ()))

-- `Sum.lex_acc_inr` (`acb`): `r := False`, `s := True`.
example : ¬ ∀ {α : Type} {r : α → α → Prop} {β : Type} {s : β → β → Prop},
    (∀ a, Acc (Sum.Lex r s) (Sum.inl a)) → ∀ {b : β}, Acc (Sum.Lex r s) (Sum.inr b) :=
  fun h => not_acc_of_refl (.inr trivial)
    (@h Unit (fun _ _ => False) Unit (fun _ _ => True)
      (fun _ => ⟨_, fun _ h => by cases h with | inl h => exact h.elim⟩) ())

-- `Sum.lex_wf` (`ha`): `r := True`, `s := False`.
example : ¬ ∀ {α : Type} {r : α → α → Prop} {α' : Type} {s : α' → α' → Prop},
    WellFounded s → WellFounded (Sum.Lex r s) := fun h =>
  not_acc_of_refl (.inl trivial)
    ((@h Unit (fun _ _ => True) Unit (fun _ _ => False) ⟨fun _ => ⟨_, fun _ h => h.elim⟩⟩).apply
      (.inl ()))

-- `Sum.lex_wf` (`hb`): `r := False`, `s := True`.
example : ¬ ∀ {α : Type} {r : α → α → Prop} {α' : Type} {s : α' → α' → Prop},
    WellFounded r → WellFounded (Sum.Lex r s) := fun h =>
  not_acc_of_refl (.inr trivial)
    ((@h Unit (fun _ _ => False) Unit (fun _ _ => True) ⟨fun _ => ⟨_, fun _ h => h.elim⟩⟩).apply
      (.inr ()))

-- `Sum.instReflBEq` (`[ReflBEq α]`): `α := Nat` with `==` constantly `false`.
example : ¬ ∀ {α β : Type} [BEq α] [BEq β] [ReflBEq β], ReflBEq (α ⊕ β) := fun h => by
  have := (@h Nat Nat ⟨fun _ _ => false⟩ _ _).rfl (a := .inl 0)
  revert this; decide

-- `Sum.instReflBEq` (`[ReflBEq β]`)
example : ¬ ∀ {α β : Type} [BEq α] [BEq β] [ReflBEq α], ReflBEq (α ⊕ β) := fun h => by
  have := (@h Nat Nat _ ⟨fun _ _ => false⟩ _).rfl (a := .inr 0)
  revert this; decide

-- `Sum.instLawfulBEq` (`[LawfulBEq α]`): `α := Nat` with `==` constantly `true`.
example : ¬ ∀ {α β : Type} [BEq α] [BEq β] [LawfulBEq β], LawfulBEq (α ⊕ β) := fun h => by
  have := (@h Nat Nat ⟨fun _ _ => true⟩ _ _).eq_of_beq (a := .inl 0) (b := .inl 1) rfl
  cases this

-- `Sum.instLawfulBEq` (`[LawfulBEq β]`)
example : ¬ ∀ {α β : Type} [BEq α] [BEq β] [LawfulBEq α], LawfulBEq (α ⊕ β) := fun h => by
  have := (@h Nat Nat _ ⟨fun _ _ => true⟩ _).eq_of_beq (a := .inr 0) (b := .inr 1) rfl
  cases this

-- `Sum.inl_getLeft`, `Sum.eq_left_getLeft_of_isLeft`, `Sum.getLeft_eq_iff` (`h`, dependent):
-- independent parameters `α`, `β`, `x` (and `a`); `x := inr ()`.
example : ¬ ∀ {α : Type} (_a : α) {β : Type} (x : α ⊕ β), x.isLeft = true := fun h => by
  have := h () (Sum.inr () : Unit ⊕ Unit)
  cases this

-- `Sum.inr_getRight`, `Sum.eq_right_getRight_of_isRight`, `Sum.getRight_eq_iff` (`h`,
-- dependent): `x := inl ()`.
example : ¬ ∀ {β : Type} (_b : β) {α : Type} (x : α ⊕ β), x.isRight = true := fun h => by
  have := h () (Sum.inl () : Unit ⊕ Unit)
  cases this

/-! ## Dyadic (20) -/

namespace DataSmallHand.Dyadic
open _root_.Dyadic

/-- `1/2`. -/
abbrev half : _root_.Dyadic := ofIntWithPrec 1 1

theorem precision_one : (1 : _root_.Dyadic).precision ≤ some 0 :=
  precision_ofIntWithPrec_le (i := 1) (by decide) 0

theorem precision_two : (2 : _root_.Dyadic).precision ≤ some 0 :=
  precision_ofIntWithPrec_le (i := 2) (by decide) 0

theorem precision_zero : (0 : _root_.Dyadic).precision ≤ some 0 := by simp

-- `Dyadic.le_antisymm` (`h`): `x = 1`, `y = 0`.
example : ¬ ∀ {x y : _root_.Dyadic}, y ≤ x → x = y := fun h =>
  absurd (@h 1 0 (by decide)) (by decide)

-- `Dyadic.le_antisymm` (`h'`): `x = 0`, `y = 1`.
example : ¬ ∀ {x y : _root_.Dyadic}, x ≤ y → x = y := fun h =>
  absurd (@h 0 1 (by decide)) (by decide)

-- `Dyadic.le_trans` (`h`): `x = 1`, `y = z = 0`.
example : ¬ ∀ {x y z : _root_.Dyadic}, y ≤ z → x ≤ z := fun h =>
  absurd (@h 1 0 0 (by decide)) (by decide)

-- `Dyadic.le_trans` (`h'`): `x = y = 0`, `z = -1`.
example : ¬ ∀ {x y z : _root_.Dyadic}, x ≤ y → x ≤ z := fun h =>
  absurd (@h 0 0 (-1) (by decide)) (by decide)

-- `Dyadic.roundDown_eq_self_of_le` (`h`): `x = 1/2`, `prec = 0`.
example : ¬ ∀ {x : _root_.Dyadic} {prec : Int}, x.roundDown prec = x := fun h =>
  absurd (@h half 0) (by decide +kernel)

-- `Dyadic.eq_toDyadic_of_precision_le` (`hp`): `q = 1/2`, `y = 1/2`, `prec = 0`.
example : ¬ ∀ {q : Rat} {y : _root_.Dyadic} {prec : Int},
    y.toRat ≤ q → q < y.toRat + 2 ^ (-prec) → y = q.toDyadic prec := fun h =>
  absurd (@h (1/2) half 0 (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Dyadic.eq_toDyadic_of_precision_le` (`h1`): `q = 0`, `y = 1`, `prec = 0`.
example : ¬ ∀ {q : Rat} {y : _root_.Dyadic} {prec : Int},
    y.precision ≤ some prec → q < y.toRat + 2 ^ (-prec) → y = q.toDyadic prec := fun h =>
  absurd (@h 0 1 0 precision_one (by decide +kernel)) (by decide +kernel)

-- `Dyadic.eq_toDyadic_of_precision_le` (`h2`): `q = 1`, `y = 0`, `prec = 0`.
example : ¬ ∀ {q : Rat} {y : _root_.Dyadic} {prec : Int},
    y.precision ≤ some prec → y.toRat ≤ q → y = q.toDyadic prec := fun h =>
  absurd (@h 1 0 0 precision_zero (by decide +kernel)) (by decide +kernel)

-- `Dyadic.divAtPrec_mul_le` (`hb`): `a = -1`, `b = 0`.
example : ¬ ∀ {a b : _root_.Dyadic} (prec : Int), a.divAtPrec b prec * b ≤ a := fun h =>
  absurd (@h (-1) 0 0) (by decide +kernel)

-- `Dyadic.lt_divAtPrec_add_inc_mul` (`hb`): `a = b = 0`.
example : ¬ ∀ {a b : _root_.Dyadic} (prec : Int),
    a < (a.divAtPrec b prec + ofIntWithPrec 1 prec) * b := fun h =>
  absurd (@h 0 0 0) (by decide +kernel)

-- `Dyadic.eq_divAtPrec` (`hp`): `a = 1/2`, `b = 1`, `y = 1/2`, `prec = 0`.
example : ¬ ∀ {a b : _root_.Dyadic}, 0 < b → ∀ {prec : Int} {y : _root_.Dyadic},
    y * b ≤ a → a < (y + ofIntWithPrec 1 prec) * b → y = a.divAtPrec b prec := fun h =>
  absurd (@h half 1 (by decide) 0 half (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Dyadic.eq_divAtPrec` (`h1`): `a = 0`, `b = 1`, `y = 1`, `prec = 0`.
example : ¬ ∀ {a b : _root_.Dyadic}, 0 < b → ∀ {prec : Int} {y : _root_.Dyadic},
    y.precision ≤ some prec → a < (y + ofIntWithPrec 1 prec) * b → y = a.divAtPrec b prec :=
  fun h => absurd (@h 0 1 (by decide) 0 1 precision_one (by decide +kernel))
    (by decide +kernel)

-- `Dyadic.eq_divAtPrec` (`h2`): `a = b = 1`, `y = 0`, `prec = 0`.
example : ¬ ∀ {a b : _root_.Dyadic}, 0 < b → ∀ {prec : Int} {y : _root_.Dyadic},
    y.precision ≤ some prec → y * b ≤ a → y = a.divAtPrec b prec := fun h =>
  absurd (@h 1 1 (by decide) 0 0 precision_zero (by decide +kernel)) (by decide +kernel)

-- `Dyadic.eq_invAtPrec` (`hp`): `x = 2`, `y = 1/2`, `prec = 0`.
example : ¬ ∀ {x : _root_.Dyadic}, 0 < x → ∀ {prec : Int} {y : _root_.Dyadic},
    y * x ≤ 1 → 1 < (y + ofIntWithPrec 1 prec) * x → y = x.invAtPrec prec := fun h =>
  absurd (@h 2 (by decide) 0 half (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Dyadic.eq_invAtPrec` (`h1`): `x = 1`, `y = 2`, `prec = 0`.
example : ¬ ∀ {x : _root_.Dyadic}, 0 < x → ∀ {prec : Int} {y : _root_.Dyadic},
    y.precision ≤ some prec → 1 < (y + ofIntWithPrec 1 prec) * x → y = x.invAtPrec prec :=
  fun h => absurd (@h 1 (by decide) 0 2 precision_two (by decide +kernel))
    (by decide +kernel)

-- `Dyadic.eq_invAtPrec` (`h2`): `x = 1`, `y = 0`, `prec = 0`.
example : ¬ ∀ {x : _root_.Dyadic}, 0 < x → ∀ {prec : Int} {y : _root_.Dyadic},
    y.precision ≤ some prec → y * x ≤ 1 → y = x.invAtPrec prec := fun h =>
  absurd (@h 1 (by decide) 0 0 precision_zero (by decide +kernel)) (by decide +kernel)

-- `Dyadic.invAtPrec_mul_le_one` (`hx`): `x = -3`, `prec = 0`: `⌊-1/3⌋ * -3 = 3`.
example : ¬ ∀ {x : _root_.Dyadic} (prec : Int), x.invAtPrec prec * x ≤ 1 := fun h =>
  absurd (@h (-3) 0) (by decide +kernel)

-- `Dyadic.one_lt_invAtPrec_add_inc_mul` (`hx`): `x = 0`.
example : ¬ ∀ {x : _root_.Dyadic} (prec : Int),
    1 < (x.invAtPrec prec + ofIntWithPrec 1 prec) * x := fun h =>
  absurd (@h 0 0) (by decide +kernel)

-- `Dyadic.mul_invAtPrec_lt_divAtPrec_add` (`ha`): `a = -1`, `b = 3`, `prec = 0`:
-- `-1 * ⌊1/3⌋ = 0` and `⌊-1/3⌋ + 1 = 0`.
example : ¬ ∀ {a b : _root_.Dyadic}, 0 < b → ∀ (prec : Int),
    a * b.invAtPrec prec < a.divAtPrec b prec + ofIntWithPrec 1 prec := fun h =>
  absurd (@h (-1) 3 (by decide) 0) (by decide +kernel)

-- `Dyadic.divAtPrec_sub_mul_lt_mul_invAtPrec` (`ha`): `a = 0`, `b = 1`.
example : ¬ ∀ {a b : _root_.Dyadic}, 0 < b → ∀ (prec : Int),
    a.divAtPrec b prec - a * ofIntWithPrec 1 prec < a * b.invAtPrec prec := fun h =>
  absurd (@h 0 1 (by decide) 0) (by decide +kernel)

end DataSmallHand.Dyadic

/-! ## Subtype (12) -/

-- The non-dependent ones: `α := Unit` (or `Bool`) with a bad order, `P := fun _ => True`.

-- `Subtype.instReflLE` (`i`): `≤` is `False`.
example : ¬ ∀ {α : Type} [LE α] {P : α → Prop}, Std.Refl (α := Subtype P) (· ≤ ·) := fun h =>
  (@h Unit ⟨fun _ _ => False⟩ (fun _ => True)).refl ⟨(), trivial⟩

-- `Subtype.instAntisymmLE` (`i`): `≤` is `True` on `Bool`.
example : ¬ ∀ {α : Type} [LE α] {P : α → Prop}, Std.Antisymm (α := Subtype P) (· ≤ ·) :=
  fun h => by
    have := (@h Bool ⟨fun _ _ => True⟩ (fun _ => True)).antisymm ⟨true, trivial⟩ ⟨false, trivial⟩
      trivial trivial
    cases this

-- `Subtype.instTotalLE` (`i`): `≤` is `False`.
example : ¬ ∀ {α : Type} [LE α] {P : α → Prop}, Std.Total (α := Subtype P) (· ≤ ·) := fun h =>
  ((@h Unit ⟨fun _ _ => False⟩ (fun _ => True)).total ⟨(), trivial⟩ ⟨(), trivial⟩).elim id id

-- `Subtype.instIsPreorder` (`inst`): `≤` is `False`.
example : ¬ ∀ {α : Type} [LE α] {P : α → Prop}, Std.IsPreorder (Subtype P) := fun h =>
  (@h Unit ⟨fun _ _ => False⟩ (fun _ => True)).le_refl ⟨(), trivial⟩

-- `Subtype.instIsLinearPreorder` (`inst`)
example : ¬ ∀ {α : Type} [LE α] {P : α → Prop}, Std.IsLinearPreorder (Subtype P) := fun h =>
  (@h Unit ⟨fun _ _ => False⟩ (fun _ => True)).le_refl ⟨(), trivial⟩

-- `Subtype.instIsPartialOrder` (`inst`)
example : ¬ ∀ {α : Type} [LE α] {P : α → Prop}, Std.IsPartialOrder (Subtype P) := fun h =>
  (@h Unit ⟨fun _ _ => False⟩ (fun _ => True)).le_refl ⟨(), trivial⟩

-- `Subtype.instIsLinearOrder` (`inst`)
example : ¬ ∀ {α : Type} [LE α] {P : α → Prop}, Std.IsLinearOrder (Subtype P) := fun h =>
  (@h Unit ⟨fun _ _ => False⟩ (fun _ => True)).le_refl ⟨(), trivial⟩

-- `Subtype.instLawfulOrderLT` (`inst`): `<` is `True`, `≤` is `False`.
example : ¬ ∀ {α : Type} [LT α] [LE α] {P : α → Prop}, Std.LawfulOrderLT (Subtype P) :=
  fun h => (((@h Unit ⟨fun _ _ => True⟩ ⟨fun _ _ => False⟩ (fun _ => True)).lt_iff
    ⟨(), trivial⟩ ⟨(), trivial⟩).mp trivial).1

-- The dependent ones (the `Min`/`Max` instance on `Subtype P` needs `MinEqOr α`/`MaxEqOr α`):
-- independent parameters `α`, `[LE α]`, `[Min α]`/`[Max α]`; `α := Bool`,
-- `min`/`max` constantly `true`, so `min false false ∉ {false}`.

-- `Subtype.instMinEqOr` (`inst`)
example : ¬ ∀ {α : Type} [Min α], Std.MinEqOr α := fun h => by
  have := (@h Bool ⟨fun _ _ => true⟩).min_eq_or false false
  revert this; decide

-- `Subtype.instMaxEqOr` (`inst`)
example : ¬ ∀ {α : Type} [Max α], Std.MaxEqOr α := fun h => by
  have := (@h Bool ⟨fun _ _ => true⟩).max_eq_or false false
  revert this; decide

-- `Subtype.instLawfulOrderMin` (`inst_2`)
example : ¬ ∀ {α : Type} [LE α] [Min α], Std.LawfulOrderMin α := fun h => by
  have := (@h Bool ⟨fun _ _ => True⟩ ⟨fun _ _ => true⟩).min_eq_or false false
  revert this; decide

-- `Subtype.instLawfulOrderMax` (`inst_2`)
example : ¬ ∀ {α : Type} [LE α] [Max α], Std.LawfulOrderMax α := fun h => by
  have := (@h Bool ⟨fun _ _ => True⟩ ⟨fun _ _ => true⟩).max_eq_or false false
  revert this; decide

/-! ## Char (3) -/

-- `Char.ofOrdinal_le_of_le` (`h`): `f = 1`, `g = 0`.
example : ¬ ∀ {f g : Fin Char.numCodePoints}, Char.ofOrdinal f ≤ Char.ofOrdinal g := fun h =>
  absurd (@h 1 0) (by decide)

-- `Char.isValidChar_of_isValidCharNat` (`h`, dependent): independent parameter `n`;
-- `n = 0xD800` is a surrogate.
example : ¬ ∀ n : Nat, Char.isValidCharNat n := fun h =>
  absurd (h 0xD800) (by unfold Char.isValidCharNat; decide)

-- `Char.toNat_mk` (`h`, dependent): independent parameter `val`; `val = 0xD800`.
example : ¬ ∀ {val : UInt32}, val.isValidChar := fun h =>
  absurd (@h 0xD800) (by unfold UInt32.isValidChar Nat.isValidChar; decide)

/-! ## Float (3) -/

namespace DataSmallHand.Float
open Float.Model Float.Model.UnpackedFloat

/-- A 4-bit format: sign, 2 exponent bits, 1 mantissa bit. -/
abbrev tiny : Format where
  mantissaBitsWithoutImplicit := 1
  exponentBits := 2

-- `Float.Model.Format.Valid.eq_packedNaN` (`self : spec.Valid b`): the NaN that is not the
-- canonical one.
example : ¬ ∀ {spec : Format} {b : BitVec spec.numBits},
    unpackExponent b = -1#spec.exponentBits →
      unpackMantissa b ≠ 0#spec.mantissaBitsWithoutImplicit → b = packedNaN spec := fun h =>
  absurd (@h tiny 0b1111#4 (by decide) (by decide)) (by decide)

-- `Float.Model.Format.Valid.eq_packedNaN` (exponent `= -1`): the smallest subnormal, which is
-- valid because it is not a NaN.
example : ¬ ∀ {spec : Format} {b : BitVec spec.numBits}, spec.Valid b →
    unpackMantissa b ≠ 0#spec.mantissaBitsWithoutImplicit → b = packedNaN spec := fun h =>
  absurd (@h tiny 0b0001#4 ⟨fun e => absurd e (by decide)⟩ (by decide)) (by decide)

-- `Float.Model.Format.Valid.eq_packedNaN` (mantissa `≠ 0`): `+∞`, valid because it is not a NaN.
example : ¬ ∀ {spec : Format} {b : BitVec spec.numBits}, spec.Valid b →
    unpackExponent b = -1#spec.exponentBits → b = packedNaN spec := fun h =>
  absurd (@h tiny 0b0110#4 ⟨fun _ m => absurd m (by decide)⟩ (by decide)) (by decide)

end DataSmallHand.Float

/-! ## FloatArray (1) -/

-- `FloatArray.ext` (`data`): two arrays of different sizes.
example : ¬ ∀ {x y : FloatArray}, x = y := fun h => by
  have := congrArg (·.data.size) (@h ⟨#[]⟩ ⟨#[0.0]⟩)
  simp at this

/-! # Consistency: each removable restatement implies the original theorem -/

example : type_of% @Dyadic.eq_divAtPrec := fun _ => DataSmallHand.Dyadic.eq_divAtPrec
example : type_of% @Dyadic.eq_invAtPrec := fun _ => DataSmallHand.Dyadic.eq_invAtPrec
example : type_of% @Dyadic.mul_invAtPrec_lt_divAtPrec_add := fun ha _ =>
  DataSmallHand.Dyadic.mul_invAtPrec_lt_divAtPrec_add ha
example : type_of% @Dyadic.divAtPrec_sub_mul_lt_mul_invAtPrec := fun ha _ =>
  DataSmallHand.Dyadic.divAtPrec_sub_mul_lt_mul_invAtPrec ha
example : type_of% @ByteArray.getElem_set! := fun data i j v _ hj =>
  DataSmallHand.ByteArray.getElem_set! data i j v hj
example : type_of% @ByteArray.lt_iff_extract_lt_of_size_le := fun _ =>
  DataSmallHand.ByteArray.lt_iff_extract_lt_of_size_le

#print axioms DataSmallHand.Dyadic.eq_divAtPrec
#print axioms DataSmallHand.Dyadic.eq_invAtPrec_derivable
#print axioms DataSmallHand.Dyadic.mul_invAtPrec_lt_divAtPrec_add
#print axioms DataSmallHand.Dyadic.divAtPrec_sub_mul_lt_mul_invAtPrec
#print axioms DataSmallHand.ByteArray.getElem_set!
#print axioms DataSmallHand.ByteArray.lt_iff_extract_lt_of_size_le
