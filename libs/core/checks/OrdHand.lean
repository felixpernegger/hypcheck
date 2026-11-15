/-!
Hand resolution of the 42 hypotheses in `Init.Data.Ord.Basic` and `Init.Data.Ord.Vector` that
`HypCheck.lean` (with the v8 models) left unresolved. For each hypothesis `hᵢ` of theorem `T`, this
file proves `T'` (removable), `¬T'` (necessary), or, for a dependent hypothesis, `¬∀ indep, Hᵢ`.

Removable (8):
* `isGE_compareOfLessAndEq` needs only `not_le`: `compareOfLessAndEq x y` is `.lt` iff `x < y`,
  and `¬ x < y ↔ y ≤ x` by `not_le` alone, so `antisymm` and `total` are both removable.
* `Vector.compareLex_flatMap_flatMap` and `Vector.compare_flatMap_flatMap` hold with no instance
  hypotheses and no `0 < m`: all blocks `f a` have the same length `m`, so the lexicographic
  comparison of the concatenations is the `then`-fold of the block comparisons, which by `hf` is the
  `then`-fold of the element comparisons (the `Array` version needs them because lengths vary).

All others are necessary: the `Ordering` lemmas fail at a single value, the `compareOfLessAndEq`
lemmas on `Bool` with `<` everywhere true and `≤` everywhere false (or true), and the `Vector`
instances at `n = 1` with a constant comparison.

Run with the lean4 repo's stage1 binary: `lean checks/OrdHand.lean`.
-/

universe u v

/-! # Removable (8) -/

-- `isGE_compareOfLessAndEq` (`antisymm`): `isGE ↔ ¬ x < y ↔ y ≤ x` by `not_le` alone.
theorem isGE_compareOfLessAndEq_antisymm {α : Type u} [LT α] [LE α] [DecidableLT α] [DecidableEq α]
    (not_le : ∀ {x y : α}, ¬ x ≤ y ↔ y < x) (total : ∀ (x y : α), x ≤ y ∨ y ≤ x) {x y : α} :
    (compareOfLessAndEq x y).isGE ↔ y ≤ x := by
  rw [Ordering.isGE_iff_ne_lt, compareOfLessAndEq_eq_lt]
  exact ⟨fun h => Classical.byContradiction fun h' => h (not_le.mp h'),
    fun h h' => (not_le.mpr h') h⟩

-- `isGE_compareOfLessAndEq` (`total`): `isGE ↔ ¬ x < y ↔ y ≤ x` by `not_le` alone.
theorem isGE_compareOfLessAndEq_total {α : Type u} [LT α] [LE α] [DecidableLT α] [DecidableEq α]
    (antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y)
    (not_le : ∀ {x y : α}, ¬ x ≤ y ↔ y < x) {x y : α} :
    (compareOfLessAndEq x y).isGE ↔ y ≤ x := by
  rw [Ordering.isGE_iff_ne_lt, compareOfLessAndEq_eq_lt]
  exact ⟨fun h => Classical.byContradiction fun h' => h (not_le.mp h'),
    fun h h' => (not_le.mpr h') h⟩

theorem list_compareLex_flatMap {α : Type u} {β : Type v} {cmp : α → α → Ordering}
    {cmp' : β → β → Ordering} {m : Nat} (g : α → List β) (hg : ∀ a, (g a).length = m)
    (hc : ∀ a b, List.compareLex cmp' (g a) (g b) = cmp a b) :
    ∀ (l₁ l₂ : List α), l₁.length = l₂.length →
      List.compareLex cmp' (l₁.flatMap g) (l₂.flatMap g) = List.compareLex cmp l₁ l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    rw [List.flatMap_cons, List.flatMap_cons, List.compareLex_append_append_of_length_eq
      ((hg a).trans (hg b).symm), hc, List.compareLex_cons_cons,
      list_compareLex_flatMap g hg hc l₁ l₂ (by simpa using h)]

/-- `Vector.compareLex_flatMap_flatMap` without any of its hypotheses except `hf`. -/
theorem vector_compareLex_flatMap {α : Type u} {cmp : α → α → Ordering} {n m : Nat} {β : Type v}
    {cmp' : β → β → Ordering} (f : α → Vector β m)
    (hf : ∀ a b, (f a).compareLex cmp' (f b) = cmp a b) {xs ys : Vector α n} :
    (xs.flatMap f).compareLex cmp' (ys.flatMap f) = xs.compareLex cmp ys := by
  rw [Vector.compareLex_eq_compareLex_toList, Vector.compareLex_eq_compareLex_toList]
  have e : ∀ zs : Vector α n, (zs.flatMap f).toList = zs.toList.flatMap fun a => (f a).toList := by
    intro zs
    rw [← Vector.toList_toArray, ← Vector.flatMap_toArray, Array.toList_flatMap]
    simp only [Vector.toList_toArray]
  rw [e, e]
  exact list_compareLex_flatMap (m := m) _ (fun a => (f a).length_toList)
    (fun a b => (Vector.compareLex_eq_compareLex_toList).symm.trans (hf a b)) _ _ (by simp)

-- `Vector.compareLex_flatMap_flatMap` (`[LawfulEqCmp cmp]`): holds without any hypothesis except
-- `hf` (`vector_compareLex_flatMap`), since all blocks have the same length.
theorem compareLex_flatMap_flatMap_h6 {α : Type u} {cmp : α → α → Ordering} {n m : Nat}
    {β : Type v} {cmp' : β → β → Ordering} [Std.LawfulEqCmp cmp'] (f : α → Vector β m)
    (hf : ∀ a b, (f a).compareLex cmp' (f b) = cmp a b) (_hm : 0 < m) {xs ys : Vector α n} :
    (xs.flatMap f).compareLex cmp' (ys.flatMap f) = xs.compareLex cmp ys :=
  vector_compareLex_flatMap f hf

-- `Vector.compareLex_flatMap_flatMap` (`[LawfulEqCmp cmp']`): same argument.
theorem compareLex_flatMap_flatMap_h7 {α : Type u} {cmp : α → α → Ordering} {n m : Nat}
    {β : Type v} {cmp' : β → β → Ordering} [Std.LawfulEqCmp cmp] (f : α → Vector β m)
    (hf : ∀ a b, (f a).compareLex cmp' (f b) = cmp a b) (_hm : 0 < m) {xs ys : Vector α n} :
    (xs.flatMap f).compareLex cmp' (ys.flatMap f) = xs.compareLex cmp ys :=
  vector_compareLex_flatMap f hf

-- `Vector.compareLex_flatMap_flatMap` (`hm`): same argument (it covers `m = 0`).
theorem compareLex_flatMap_flatMap_h10 {α : Type u} {cmp : α → α → Ordering} {n m : Nat}
    {β : Type v} {cmp' : β → β → Ordering} [Std.LawfulEqCmp cmp] [Std.LawfulEqCmp cmp']
    (f : α → Vector β m) (hf : ∀ a b, (f a).compareLex cmp' (f b) = cmp a b)
    {xs ys : Vector α n} :
    (xs.flatMap f).compareLex cmp' (ys.flatMap f) = xs.compareLex cmp ys :=
  vector_compareLex_flatMap f hf

-- `Vector.compare_flatMap_flatMap` (`[LawfulEqOrd α]`): `compare` on vectors is
-- `Vector.compareLex compare`, so `vector_compareLex_flatMap` applies.
theorem compare_flatMap_flatMap_h2 {α : Type u} [Ord α] {n m : Nat} {β : Type v} [Ord β]
    [Std.LawfulEqOrd β] (f : α → Vector β m) (hf : ∀ a b, compare (f a) (f b) = compare a b)
    (_hm : 0 < m) {xs ys : Vector α n} :
    compare (xs.flatMap f) (ys.flatMap f) = compare xs ys :=
  vector_compareLex_flatMap f hf

-- `Vector.compare_flatMap_flatMap` (`[LawfulEqOrd β]`): same argument.
theorem compare_flatMap_flatMap_h7 {α : Type u} [Ord α] [Std.LawfulEqOrd α] {n m : Nat}
    {β : Type v} [Ord β] (f : α → Vector β m) (hf : ∀ a b, compare (f a) (f b) = compare a b)
    (_hm : 0 < m) {xs ys : Vector α n} :
    compare (xs.flatMap f) (ys.flatMap f) = compare xs ys :=
  vector_compareLex_flatMap f hf

-- `Vector.compare_flatMap_flatMap` (`hm`): same argument.
theorem compare_flatMap_flatMap_h10 {α : Type u} [Ord α] [Std.LawfulEqOrd α] {n m : Nat}
    {β : Type v} [Ord β] [Std.LawfulEqOrd β] (f : α → Vector β m)
    (hf : ∀ a b, compare (f a) (f b) = compare a b) {xs ys : Vector α n} :
    compare (xs.flatMap f) (ys.flatMap f) = compare xs ys :=
  vector_compareLex_flatMap f hf

/-! # Necessary: `Ordering` lemmas (19) -/

-- `Ordering.then_eq_eq_of_eq_eq` (`a`, first): `o₁ = .lt`, `o₂ = .eq`.
example : ¬ ∀ {o₁ o₂ : Ordering}, o₂ = .eq → o₁.then o₂ = .eq :=
  fun H => absurd (@H .lt .eq rfl) (by decide)

-- `Ordering.then_eq_eq_of_eq_eq` (`a`, second): `o₁ = .eq`, `o₂ = .lt`.
example : ¬ ∀ {o₁ o₂ : Ordering}, o₁ = .eq → o₁.then o₂ = .eq :=
  fun H => absurd (@H .eq .lt rfl) (by decide)

-- `Ordering.left_eq_eq_of_then_eq_eq` (`a`): `o₁ = .lt`.
example : ¬ ∀ {o₁ o₂ : Ordering}, o₁ = .eq :=
  fun H => absurd (@H .lt .eq) (by decide)

-- `Ordering.right_eq_eq_of_then_eq_eq` (`a`): `o₂ = .lt`.
example : ¬ ∀ {o₁ o₂ : Ordering}, o₂ = .eq :=
  fun H => absurd (@H .eq .lt) (by decide)

-- `Ordering.eq_eq_of_eq_swap` (`a`): `o = .lt`.
example : ¬ ∀ {o : Ordering}, o = .eq :=
  fun H => absurd (@H .lt) (by decide)

-- `Ordering.eq_eq_of_isLE_of_isGE` (`a`, first): `o = .gt`.
example : ¬ ∀ {o : Ordering}, o.isGE = true → o = .eq :=
  fun H => absurd (@H .gt rfl) (by decide)

-- `Ordering.eq_eq_of_isLE_of_isGE` (`a`, second): `o = .lt`.
example : ¬ ∀ {o : Ordering}, o.isLE = true → o = .eq :=
  fun H => absurd (@H .lt rfl) (by decide)

-- `Ordering.eq_eq_of_isGE_of_isGE_swap` (`a`, first): `o = .lt`.
example : ¬ ∀ {o : Ordering}, o.swap.isGE = true → o = .eq :=
  fun H => absurd (@H .lt rfl) (by decide)

-- `Ordering.eq_eq_of_isGE_of_isGE_swap` (`a`, second): `o = .gt`.
example : ¬ ∀ {o : Ordering}, o.isGE = true → o = .eq :=
  fun H => absurd (@H .gt rfl) (by decide)

-- `Ordering.eq_eq_of_isLE_of_isLE_swap` (`a`, first): `o = .gt`.
example : ¬ ∀ {o : Ordering}, o.swap.isLE = true → o = .eq :=
  fun H => absurd (@H .gt rfl) (by decide)

-- `Ordering.eq_eq_of_isLE_of_isLE_swap` (`a`, second): `o = .lt`.
example : ¬ ∀ {o : Ordering}, o.isLE = true → o = .eq :=
  fun H => absurd (@H .lt rfl) (by decide)

-- `Ordering.dthen_congr` (`hx`, dependent: `hy` mentions it): `x = .lt`, `x' = .gt`.
example : ¬ ∀ {x x' : Ordering}, x = x' :=
  fun H => absurd (@H .lt .gt) (by decide)

-- `Ordering.dthen_congr` (`hy`): `x = x' = .eq`, `y = fun _ => .lt`, `y' = fun _ => .gt`.
example : ¬ ∀ {x x' : Ordering} {y : x = .eq → Ordering} {y' : x' = .eq → Ordering}
    (hx : x = x'), x.dthen y = x'.dthen y' :=
  fun H => absurd (@H .eq .eq (fun _ => .lt) (fun _ => .gt) rfl) (by decide)

-- `Ordering.dthen_eq_eq_of_eq_eq` (`h₁`, dependent: the next hypothesis mentions it): `o₁ = .lt`.
example : ¬ ∀ {o₁ : Ordering}, o₁ = .eq :=
  fun H => absurd (@H .lt) (by decide)

-- `Ordering.dthen_eq_eq_of_eq_eq` (`a`): `o₁ = .eq`, `o₂ = fun _ => .lt`.
example : ¬ ∀ {o₁ : Ordering} {o₂ : o₁ = .eq → Ordering} (h₁ : o₁ = .eq), o₁.dthen o₂ = .eq :=
  fun H => absurd (@H .eq (fun _ => .lt) rfl) (by decide)

-- `Ordering.left_eq_eq_of_dthen_eq_eq` (`a`): `o₁ = .lt`.
example : ¬ ∀ {o₁ : Ordering} {o₂ : o₁ = .eq → Ordering}, o₁ = .eq :=
  fun H => absurd (@H .lt (fun _ => .eq)) (by decide)

-- `Ordering.right_eq_eq_of_dthen_eq_eq` (`h`, dependent: the conclusion mentions it): `o₁ = .lt`.
example : ¬ ∀ {o₁ : Ordering} {o₂ : o₁ = .eq → Ordering}, o₁.dthen o₂ = .eq :=
  fun H => absurd (@H .lt (fun _ => .eq)) (by decide)

-- `Ord.ext` (`compare`): two different `Ord Bool` instances.
example : ¬ ∀ {α : Type} {x y : Ord α}, x = y := fun H =>
  absurd (congrArg (fun o => @compare Bool o true true)
    (@H Bool ⟨fun _ _ => .lt⟩ ⟨fun _ _ => .gt⟩)) (by decide)

/-! # Necessary: `compareOfLessAndEq` lemmas (6) -/

/-- `<` everywhere true. -/
def allLT : LT Bool := ⟨fun _ _ => True⟩
instance allLTDec : @DecidableLT Bool allLT := fun _ _ => (isTrue trivial : Decidable True)
/-- `≤` everywhere false. -/
def noLE : LE Bool := ⟨fun _ _ => False⟩
/-- `≤` everywhere true. -/
def allLE : LE Bool := ⟨fun _ _ => True⟩

theorem noLE_antisymm : ∀ {x y : Bool}, @LE.le Bool noLE x y → @LE.le Bool noLE y x → x = y :=
  fun h _ => False.elim h
theorem noLE_not_le : ∀ {x y : Bool}, ¬ @LE.le Bool noLE x y ↔ @LT.lt Bool allLT y x :=
  ⟨fun _ => trivial, fun _ h => h⟩

-- `compareOfLessAndEq_eq_eq` (`refl`): `Bool`, `<` true, `≤` false (`not_le` holds):
-- `compareOfLessAndEq true true = .lt`.
example : ¬ ∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : DecidableLT α]
    [inst_3 : DecidableEq α] (not_le : ∀ {x y : α}, ¬ x ≤ y ↔ y < x) {x y : α},
    compareOfLessAndEq x y = .eq ↔ x = y :=
  fun H => absurd (@H Bool allLT noLE allLTDec instDecidableEqBool noLE_not_le true true)
    (by decide)

-- `compareOfLessAndEq_eq_eq` (`not_le`): `Bool`, `<` and `≤` true (`refl` holds):
-- `compareOfLessAndEq true true = .lt`.
example : ¬ ∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : DecidableLT α]
    [inst_3 : DecidableEq α] (refl : ∀ (x : α), x ≤ x) {x y : α},
    compareOfLessAndEq x y = .eq ↔ x = y :=
  fun H => absurd (@H Bool allLT allLE allLTDec instDecidableEqBool (fun _ => trivial) true true)
    (by decide)

-- `lt_iff_not_gt_and_ne_of_antisymm_of_total_of_not_le` (`total`): `Bool`, `<` true, `≤` false
-- (`antisymm`, `not_le` hold), `x = y = true`: `True ↔ False`.
example : ¬ ∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : DecidableLT α]
    [inst_3 : DecidableEq α] (antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y)
    (not_le : ∀ {x y : α}, ¬ x ≤ y ↔ y < x) (x y : α), x < y ↔ ¬ y < x ∧ x ≠ y :=
  fun H => absurd (@H Bool allLT noLE allLTDec instDecidableEqBool noLE_antisymm noLE_not_le
    true true) (by decide)

-- `compareOfLessAndEq_eq_swap` (`total`): same model: `.lt = .lt.swap` fails.
example : ¬ ∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : DecidableLT α]
    [inst_3 : DecidableEq α] (antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y)
    (not_le : ∀ {x y : α}, ¬ x ≤ y ↔ y < x) {x y : α},
    compareOfLessAndEq x y = (compareOfLessAndEq y x).swap :=
  fun H => absurd (@H Bool allLT noLE allLTDec instDecidableEqBool noLE_antisymm noLE_not_le
    true true) (by decide)

-- `compareOfLessAndEq_eq_gt` (`total`): same model: `.lt = .gt ↔ true < true` is `False ↔ True`.
example : ¬ ∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : DecidableLT α]
    [inst_3 : DecidableEq α] (antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y)
    (not_le : ∀ {x y : α}, ¬ x ≤ y ↔ y < x) (x y : α),
    compareOfLessAndEq x y = .gt ↔ y < x :=
  fun H => absurd (@H Bool allLT noLE allLTDec instDecidableEqBool noLE_antisymm noLE_not_le
    true true) (by decide)

-- `isLE_compareOfLessAndEq` (`total`): same model: `Ordering.lt.isLE ↔ true ≤ true` is
-- `True ↔ False`.
example : ¬ ∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : DecidableLT α]
    [inst_3 : DecidableEq α] (antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y)
    (not_le : ∀ {x y : α}, ¬ x ≤ y ↔ y < x) {x y : α},
    (compareOfLessAndEq x y).isLE ↔ x ≤ y :=
  fun H => absurd (@H Bool allLT noLE allLTDec instDecidableEqBool noLE_antisymm noLE_not_le
    true true) (fun h => (h.mp rfl : False))

/-! # Necessary: `Vector` instances (10) -/

/-- `compare` constantly `.lt`. -/
def ltOrd : Ord Bool := ⟨fun _ _ => .lt⟩
/-- `compare` constantly `.eq`. -/
def eqOrd : Ord Bool := ⟨fun _ _ => .eq⟩
/-- `==` constantly `false`. -/
def falseBEq : BEq Bool := ⟨fun _ _ => false⟩

-- `Vector.instReflCmpCompareLex` (`[ReflCmp cmp]`): `cmp = fun _ _ => .lt`, `n = 1`:
-- `compareLex cmp #v[true] #v[true] = .lt`.
example : ¬ ∀ {α : Type} {cmp : α → α → Ordering} {n : Nat},
    Std.ReflCmp (Vector.compareLex cmp (n := n)) := fun H =>
  absurd (@Std.ReflCmp.compare_self _ _ (@H Bool (fun _ _ => .lt) 1) #v[true]) (by decide)

-- `Vector.instLawfulEqCmpCompareLex` (`[LawfulEqCmp cmp]`): `cmp = fun _ _ => .eq`, `n = 1`:
-- `#v[true]` and `#v[false]` compare `Ordering.eq`.
example : ¬ ∀ {α : Type} {cmp : α → α → Ordering} {n : Nat},
    Std.LawfulEqCmp (Vector.compareLex cmp (n := n)) := fun H =>
  absurd (@Std.LawfulEqCmp.eq_of_compare _ _ (@H Bool (fun _ _ => .eq) 1) #v[true] #v[false]
    (by decide)) (by decide)

-- `Vector.instLawfulBEqCmpCompareLex` (`[LawfulBEqCmp cmp]`): `cmp = fun _ _ => .eq`,
-- `==` constantly `false`, `n = 1`.
example : ¬ ∀ {α : Type} {cmp : α → α → Ordering} [inst : BEq α] {n : Nat},
    Std.LawfulBEqCmp (Vector.compareLex cmp (n := n)) := fun H =>
  absurd ((@Std.LawfulBEqCmp.compare_eq_iff_beq _ _ _ (@H Bool (fun _ _ => .eq) falseBEq 1)
    #v[true] #v[true]).mp (by decide)) (by decide)

-- `Vector.instOrientedCmpCompareLex` (`[OrientedCmp cmp]`): `cmp = fun _ _ => .lt`, `n = 1`:
-- `.lt = .lt.swap` fails.
example : ¬ ∀ {α : Type} {cmp : α → α → Ordering} {n : Nat},
    Std.OrientedCmp (Vector.compareLex cmp (n := n)) := fun H =>
  absurd (@Std.OrientedCmp.eq_swap _ _ (@H Bool (fun _ _ => .lt) 1) #v[true] #v[true])
    (by decide)

-- `Vector.instTransCmpCompareLex` (`[TransCmp cmp]`): `cmp = fun _ _ => .lt`, `n = 1`: not even
-- oriented.
example : ¬ ∀ {α : Type} {cmp : α → α → Ordering} {n : Nat},
    Std.TransCmp (Vector.compareLex cmp (n := n)) := fun H =>
  absurd (@Std.OrientedCmp.eq_swap _ _ (@H Bool (fun _ _ => .lt) 1).toOrientedCmp
    #v[true] #v[true]) (by decide)

-- `Vector.instReflOrd` (`[ReflOrd α]`): `Ord Bool` with `compare` constantly `Ordering.lt`, `n = 1`.
example : ¬ ∀ {α : Type} [inst : Ord α] {n : Nat}, Std.ReflOrd (Vector α n) := fun H =>
  absurd (@Std.ReflCmp.compare_self _ _ (@H Bool ltOrd 1) #v[true]) (by decide)

-- `Vector.instLawfulEqOrd` (`[LawfulEqOrd α]`): `compare` constantly `Ordering.eq`, `n = 1`.
example : ¬ ∀ {α : Type} [inst : Ord α] {n : Nat}, Std.LawfulEqOrd (Vector α n) := fun H =>
  absurd (@Std.LawfulEqCmp.eq_of_compare _ _ (@H Bool eqOrd 1) #v[true] #v[false] (by decide))
    (by decide)

-- `Vector.instLawfulBEqOrd` (`[LawfulBEqOrd α]`): `compare` constantly `Ordering.eq`, `==` constantly
-- `false`, `n = 1`.
example : ¬ ∀ {α : Type} [inst : Ord α] [inst_1 : BEq α] {n : Nat},
    Std.LawfulBEqOrd (Vector α n) := fun H =>
  absurd ((@Std.LawfulBEqCmp.compare_eq_iff_beq _ _ _ (@H Bool eqOrd falseBEq 1)
    #v[true] #v[true]).mp (by decide)) (by decide)

-- `Vector.instOrientedOrd` (`[OrientedOrd α]`): `compare` constantly `Ordering.lt`, `n = 1`.
example : ¬ ∀ {α : Type} [inst : Ord α] {n : Nat}, Std.OrientedOrd (Vector α n) := fun H =>
  absurd (@Std.OrientedCmp.eq_swap _ _ (@H Bool ltOrd 1) #v[true] #v[true]) (by decide)

-- `Vector.instTransOrd` (`[TransOrd α]`): `compare` constantly `Ordering.lt`, `n = 1`: not even oriented.
example : ¬ ∀ {α : Type} [inst : Ord α] {n : Nat}, Std.TransOrd (Vector α n) := fun H =>
  absurd (@Std.OrientedCmp.eq_swap _ _ (@H Bool ltOrd 1).toOrientedCmp #v[true] #v[true])
    (by decide)

