/-!
Hand proofs for the 8 verdicts (found automatically before v6) that still had no stored proof after
the v7.1 printer fix and `--redo` run of 2026-11-06: in each, the statement or the counterexample
needs a proof that the generic hole tactic does not find, or the counterexample's `decide` does not
go through as printed. The witnesses are the recorded ones. All 8 are necessary.

Run with the lean4 repo's stage1 binary: `lean checks/Redo2Hand.lean`.
-/

-- `LE Nat` by parity: a linear preorder, but `<` (the usual one) is not its strict part.
def parityLE : LE Nat := ⟨fun a b => a % 2 ≤ b % 2⟩
instance parityDecLE : @DecidableLE Nat parityLE := fun a b => (a % 2).decLe (b % 2)
theorem parityLinear : @Std.IsLinearPreorder Nat parityLE :=
  @Std.IsLinearPreorder.mk Nat parityLE
    (@Std.IsPreorder.mk Nat parityLE (fun a => Nat.le_refl (a % 2))
      (fun _ _ _ h₁ h₂ => Nat.le_trans h₁ h₂))
    (fun a b => Nat.le_total (a % 2) (b % 2))

-- `List.apply_minOn_lt_apply_getElem_of_lt_minIdxOn` (`[LawfulOrderLT β]`): parity order with the
-- usual `<`, `f = (· + 1)`, `xs = [0, 1]`, `k = 0`: the minimum by parity is at index 1 (`f 1 = 2`),
-- and `2 < f 0 = 1` fails.
example : ¬ ∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β]
    [inst_3 : Std.IsLinearPreorder β] {f : α → β} {xs : List α} (h : xs ≠ []) {k : Nat}
    (hk : k < xs.minIdxOn f h),
    f (xs.minOn f h) < f (xs[k]'(by haveI := List.minIdxOn_lt_length (f := f) h; omega)) :=
  fun H => absurd (@H Nat Nat parityLE parityDecLE instLTNat parityLinear (· + 1) [0, 1]
    (by decide) 0 (by decide)) (by decide)

-- `List.apply_maxOn_lt_apply_getElem_of_lt_maxIdxOn` (`[LawfulOrderLT β]`): same order and `f`,
-- `xs = [1, 0]`, `k = 0`: the maximum by parity is at index 1 (`f 0 = 1`), and `f 1 = 2 < 1` fails.
example : ¬ ∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β]
    [inst_3 : Std.IsLinearPreorder β] {f : α → β} {xs : List α} (h : xs ≠ []) {k : Nat}
    (hk : k < xs.maxIdxOn f h),
    f (xs[k]'(by haveI := List.maxIdxOn_lt_length (f := f) h; omega)) < f (xs.maxOn f h) :=
  fun H => absurd (@H Nat Nat parityLE parityDecLE instLTNat parityLinear (· + 1) [1, 0]
    (by decide) 0 (by decide)) (by decide)

-- `List.maxIdxOn_eq_iff` (`[LawfulOrderLT β]`): usual `≤`, `<` replaced by `≤`, `f = fun _ => 0`,
-- `xs = [0, 1]`, `i = 1`: `maxIdxOn` of a constant function is 0, but the right side holds for 1
-- (with `<` being `≤`, `f xs[0] < f xs[1]` is `0 ≤ 0`).
example : ¬ ∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β]
    [inst_3 : Std.IsLinearPreorder β] {f : α → β} {xs : List α} (h : xs ≠ []) {i : Nat},
    xs.maxIdxOn f h = i ↔ ∃ (h : i < xs.length),
      (∀ j, (_ : j < xs.length) → f xs[j] ≤ f xs[i]) ∧
      (∀ j, (_ : j < i) → f xs[j] < f xs[i]) := fun H => by
  have hlin : Std.IsLinearPreorder Nat := inferInstance
  have := (@H Nat Nat instLENat Nat.decLe ⟨fun a b => a ≤ b⟩ hlin (fun _ => 0) [0, 1]
    (by decide) 1).mpr ⟨by decide, fun j hj => Nat.le_refl _, fun j hj => Nat.le_refl _⟩
  revert this; decide

-- `List.min?_eq_some_iff_subtype` (`[IsLinearOrder (Subtype (· ∈ xs))]`): `α = Bool` with the usual
-- `min` and the empty `≤`, `xs = [false]`, `a = false`: `[false].min? = some false`, but
-- `false ≤ false` is false. `LawfulOrderMin` holds since every `≤` is false.
example : ¬ ∀ {α : Type} {a : α} [inst : Min α] [inst_1 : LE α] {xs : List α}
    [inst_2 : Std.MinEqOr α] [inst_4 : Std.LawfulOrderMin (Subtype (· ∈ xs))],
    xs.min? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → a ≤ b := fun H => by
  have hMin : @Std.MinEqOr Bool Bool.instMin := ⟨by decide⟩
  letI falseLE : LE Bool := ⟨fun _ _ => False⟩
  have := (@H Bool false Bool.instMin falseLE [false] hMin
    (@Std.LawfulOrderMin.mk _ _ _ ⟨fun a b => by
        rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩
        simp only [List.mem_singleton] at ha hb; subst ha hb; exact .inl rfl⟩
      ⟨fun _ _ _ => ⟨False.elim, fun h => h.1⟩⟩)).mp rfl
  exact this.2 false (by simp)

-- `List.max?_eq_some_iff_subtype` (`[IsLinearOrder (Subtype (· ∈ xs))]`): same with `max`.
example : ¬ ∀ {α : Type} {a : α} [inst : Max α] [inst_1 : LE α] {xs : List α}
    [inst_2 : Std.MaxEqOr α] [inst_4 : Std.LawfulOrderMax (Subtype (· ∈ xs))],
    xs.max? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → b ≤ a := fun H => by
  have hMax : @Std.MaxEqOr Bool Bool.instMax := ⟨by decide⟩
  letI falseLE : LE Bool := ⟨fun _ _ => False⟩
  have := (@H Bool false Bool.instMax falseLE [false] hMax
    (@Std.LawfulOrderMax.mk _ _ _ ⟨fun a b => by
        rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩
        simp only [List.mem_singleton] at ha hb; subst ha hb; exact .inl rfl⟩
      ⟨fun _ _ _ => ⟨False.elim, fun h => h.1⟩⟩)).mp rfl
  exact this.2 false (by simp)

-- `Vector.replace_replicate_self` (`[LawfulBEq α]`): `BEq Nat` by `!=`, `n = 1`, `a = 1`, `b = 0`:
-- `replicate 1 1` contains no element `== 1`, so `replace` leaves `#v[1]`, while the right side is
-- `#v[0]`.
example : ¬ ∀ {α : Type} [inst : BEq α] {n : Nat} {b a : α} (h : 0 < n),
    (Vector.replicate n a).replace a b = (#v[b] ++ Vector.replicate (n - 1) a).cast (by omega) :=
  fun H => absurd (@H Nat ⟨fun a b => a != b⟩ 1 0 1 (by decide)) (by decide +kernel)

-- `Array.insertIdx_eraseIdx_of_ge` (`h : i ≤ j`): `as = #[0, 1]`, `i = 1`, `j = 0`, `a = 0`: the
-- left side is `#[0, 0]`, the right side `#[0, 0, 1].eraseIdx 1 = #[0, 1]`.
example : ¬ ∀ {α : Type} {a : α} {i j : Nat} {as : Array α} (w₁ : i < as.size)
    (w₂ : j ≤ (as.eraseIdx i).size),
    (as.eraseIdx i).insertIdx j a =
      (as.insertIdx (j + 1) a (by simp at w₂; omega)).eraseIdx i (by simp_all; omega) :=
  fun H => absurd (@H Nat 0 1 0 #[0, 1] (by decide) (by decide)) (by decide +kernel)

-- `String.Pos.Splits.exists_eq_singleton_append` (`hp : p ≠ s.endPos`, used by the conclusion):
-- `∀ indep, hp` fails at `s = ""`, `p = "".endPos`, which splits `""` into `""` and `""`.
example : ¬ ∀ {t₁ t₂ s : String} {p : s.Pos}, p.Splits t₁ t₂ → p ≠ s.endPos :=
  fun H => H (String.splits_endPos "") rfl
