/-!
Hand resolution of the 93 instance hypotheses in `Init.Data.Array.*` (cluster `OrderArray`) that
`HypCheck.lean` (with the v8.1 lawfulness models) left unresolved. For each hypothesis `hᵢ` of
theorem `T`, this file proves `T'` (removable), `¬T'` (necessary), or, for a dependent hypothesis,
`¬∀ indep, Hᵢ`. Universe-polymorphic theorems are refuted at `Type`.

Removable (11):
* `[LawfulBEq α]` in `replace_extract`, `count_erase_self`, `count_replicate`, `le_size_erase` and
  `erase_eq_eraseIdx_of_idxOf`: `replace`, `erase`, `count`, `idxOf` and `finIdxOf?` all test
  `x == a` (element on the left), so these hold for any `BEq`. Proofs go through `List` with a
  `List` model `repL` of `Array.replace` (`List.replace` tests `a == x`, so it can't be used).
* `[IdempotentOp min]` in `foldl_min_eq_min` (and `max`): `xs.min h` is `foldl min xs[0]` over the
  rest, so the claim is `List.foldl_assoc`, which needs only associativity.
* `[LawfulLeftIdentity (· + ·) 0]` in `sum_reverse` (and `(· * ·) 1` in `prod_reverse`): `foldr`
  of a commutative associative operation doesn't depend on the order, whatever the start value.
* `[Asymm (<) α]` and `[Trichotomous (<) β]` in `map_le`: it follows from `map_le_map_iff`, which
  needs only `Trichotomous α` and `Asymm β`. (`Asymm α` even follows from `w` and `Asymm β`.)

Necessary (82, 9 of them dependent): models below, all on `Nat` (one on `Bool`).
* `BEq Nat`: `beqTrue` (equivalence, not lawful), `beqFalse` (not reflexive), `beqNe` (`!=`, not
  reflexive), `beqLe` (`≤`, reflexive and transitive, not symmetric), `beqNear` (`|a-b| ≤ 1`,
  reflexive and symmetric, not transitive); `BEq Bool`: `beqGe` (`a || !b`, not symmetric).
* The 9 dependent `LawfulBEq` hypotheses (the statement decides `a ∈ xs` with
  `instDecidableMemOfLawfulBEq`): `¬∀ α [BEq α], LawfulBEq α` (`beqFalse`).
* `LT Nat`: `ltAll` (everything, trichotomous, not irreflexive/asymmetric), `ltNone` (nothing,
  asymmetric, not trichotomous), `ltTwo` (`b = a + 2`: asymmetric, but `¬ <` is not transitive, so
  the lexicographic `≤` on arrays is not transitive or antisymmetric) with `LE := ltTwo` (then
  `LawfulOrderLT` holds) or the standard `LE Nat` (then `IsLinearOrder` holds); `ltHalf`/`leHalf`/
  `ordHalf` (compare `a / 2`: a lawful total preorder, not antisymmetric); `ordEq` (constant `.eq`).
* Operations on `Nat`: `addDist` (`|a - b|`: commutative, identity `0`, not associative),
  `addFirst` (first nonzero argument: associative, identity `0`, not commutative), `addSucc`
  (`a + b + 1`: associative, commutative, no identity), `addLeft` (`fun a _ => a`: associative,
  right identity only); the same as `Mul` with `One := 0`; `min`/`max := (a + b) / 2` (idempotent,
  not associative) and `min`/`max := a + b` (not `MinEqOr`/`MaxEqOr`).

Run with the lean4 repo's stage1 binary: `lean checks/OrderArrayHand.lean`.
-/

set_option warn.classDefReducibility false
set_option linter.unusedVariables false

universe u v

/-! # Removable (11) -/

namespace OrderArrayHand

/-- `Array.replace` on lists: replace the first `x` with `x == a`. -/
def repL {α : Type u} [BEq α] (a b : α) : List α → List α
  | [] => []
  | x :: xs => if x == a then b :: xs else x :: repL a b xs

theorem match_finIdxOf?_eq_repL {α : Type u} [BEq α] (a b : α) : ∀ l : List α,
    (match l.finIdxOf? a with | none => l | some i => l.set i b) = repL a b l
  | [] => rfl
  | x :: xs => by
    have ih := match_finIdxOf?_eq_repL a b xs
    rw [List.finIdxOf?_cons]
    cases hx : x == a
    · simp only [Bool.false_eq_true, ↓reduceIte, repL, hx]
      revert ih
      cases xs.finIdxOf? a <;> simp
    · simp [repL, hx]

theorem toArray_replace_eq_repL {α : Type u} [BEq α] (a b : α) (l : List α) :
    l.toArray.replace a b = (repL a b l).toArray := by
  rw [Array.replace, List.finIdxOf?_toArray, ← match_finIdxOf?_eq_repL]
  cases l.finIdxOf? a <;> simp

theorem repL_take {α : Type u} [BEq α] (a b : α) : ∀ (l : List α) (i : Nat),
    repL a b (l.take i) = (repL a b l).take i
  | [], _ => by simp [repL]
  | _ :: _, 0 => by simp [repL]
  | x :: xs, i + 1 => by
    simp only [List.take_succ_cons, repL]
    split <;> simp [repL_take a b xs i]

theorem list_count_erase_self {α : Type u} [BEq α] (a : α) : ∀ l : List α,
    (l.erase a).count a = l.count a - 1
  | [] => rfl
  | c :: l => by
    rw [List.erase_cons]
    cases h : c == a
    · simp [List.count_cons, h, list_count_erase_self a l]
    · simp [List.count_cons, h]

theorem list_erase_eq_eraseIdx_of_idxOf {α : Type u} [BEq α] (a : α) : ∀ (l : List α) (i : Nat),
    l.idxOf a = i → i < l.length → l.erase a = l.eraseIdx i
  | [], _, _, h => by simp at h
  | x :: l, i, w, h => by
    rw [List.idxOf_cons] at w
    rw [List.erase_cons]
    cases hx : x == a
    · simp only [hx, Bool.false_eq_true, ↓reduceIte] at w ⊢
      subst w
      simp only [List.eraseIdx_cons_succ]
      rw [list_erase_eq_eraseIdx_of_idxOf a l _ rfl (by simpa using h)]
    · simp only [hx, ↓reduceIte] at w ⊢
      subst w; rfl

theorem foldr_op_comm {α : Type u} {op : α → α → α} [Std.Associative op] [Std.Commutative op]
    (x i : α) : ∀ l : List α, l.foldr op (op x i) = op x (l.foldr op i)
  | [] => rfl
  | y :: l => by
    simp only [List.foldr_cons]
    rw [foldr_op_comm x i l, ← Std.Associative.assoc (op := op), Std.Commutative.comm (op := op) y x,
      Std.Associative.assoc (op := op)]

theorem foldr_reverse_comm {α : Type u} {op : α → α → α} [Std.Associative op] [Std.Commutative op]
    (i : α) : ∀ l : List α, l.reverse.foldr op i = l.foldr op i
  | [] => rfl
  | y :: l => by
    rw [List.reverse_cons, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_op_comm,
      foldr_reverse_comm i l, List.foldr_cons]

-- `Array.replace_extract` (`LawfulBEq α`): both sides replace the first `j < i` with `xs[j] == a`.
theorem replace_extract_h2 {α : Type u} [inst : BEq α] {a b : α} {xs : Array α} {i : Nat} :
    (xs.extract 0 i).replace a b = (xs.replace a b).extract 0 i := by
  rcases xs with ⟨l⟩
  simp only [List.extract_toArray, List.extract_eq_take_drop, Nat.sub_zero, List.drop_zero,
    toArray_replace_eq_repL, repL_take]

-- `Array.count_erase_self` (`LawfulBEq α`): `erase a` drops the first `x` with `x == a`, which is
-- one of the elements `count a` counts.
theorem count_erase_self_h2 {α : Type u} [inst : BEq α] (a : α) (xs : Array α) :
    Array.count a (xs.erase a) = Array.count a xs - 1 := by
  rcases xs with ⟨l⟩
  simp [List.erase_toArray, list_count_erase_self]

-- `Array.count_replicate` (`LawfulBEq α`): `count a` tests `b == a` on every element.
theorem count_replicate_h2 {α : Type u} [inst : BEq α] {a b : α} {n : Nat} :
    Array.count a (Array.replicate n b) = if (b == a) = true then n else 0 := by
  simp only [Array.count, Array.countP_replicate]

-- `Array.le_size_erase` (`LawfulBEq α`): `erase` removes at most one element.
theorem le_size_erase_h2 {α : Type u} [inst : BEq α] {a : α} {xs : Array α} :
    xs.size - 1 ≤ (xs.erase a).size := by
  rw [Array.erase_eq_eraseP']; exact Array.le_size_eraseP

-- `Array.erase_eq_eraseIdx_of_idxOf` (`LawfulBEq α`): `idxOf a` and `erase a` look for the same
-- first `x == a`.
theorem erase_eq_eraseIdx_of_idxOf_h2 {α : Type u} [inst : BEq α] {xs : Array α} {a : α} {i : Nat}
    (w : Array.idxOf a xs = i) (h : i < xs.size) : xs.erase a = xs.eraseIdx i h := by
  rcases xs with ⟨l⟩
  simp only [List.idxOf_toArray] at w
  simp only [List.erase_toArray, List.eraseIdx_toArray]
  rw [list_erase_eq_eraseIdx_of_idxOf a l i w (by simpa using h)]

-- `Array.foldl_min_eq_min` (`IdempotentOp min`): `foldl min a (x :: l) = min a (foldl min x l)`
-- by associativity alone.
theorem foldl_min_eq_min_h2 {α : Type u} [inst : Min α] [Std.Associative (min : α → α → α)]
    {xs : Array α} (h : xs ≠ #[]) {a : α} : Array.foldl min a xs = min a (xs.min h) := by
  rcases xs with ⟨_ | ⟨x, l⟩⟩
  · simp at h
  · simp only [List.foldl_toArray, List.min_toArray, List.foldl_cons, List.min]
    exact List.foldl_assoc

-- `Array.foldl_max_eq_max` (`IdempotentOp max`): same argument.
theorem foldl_max_eq_max_h2 {α : Type u} [inst : Max α] [Std.Associative (max : α → α → α)]
    {xs : Array α} (h : xs ≠ #[]) {a : α} : Array.foldl max a xs = max a (xs.max h) := by
  rcases xs with ⟨_ | ⟨x, l⟩⟩
  · simp at h
  · simp only [List.foldl_toArray, List.max_toArray, List.foldl_cons, List.max]
    exact List.foldl_assoc

-- `Array.sum_reverse` (`LawfulLeftIdentity (· + ·) 0`): `foldr` of a commutative associative
-- operation is invariant under reversal for any start value.
theorem sum_reverse_h5 {α : Type u} [inst : Zero α] [inst_1 : Add α]
    [Std.Associative fun (x1 x2 : α) => x1 + x2] [Std.Commutative fun (x1 x2 : α) => x1 + x2]
    (xs : Array α) : xs.reverse.sum = xs.sum := by
  rcases xs with ⟨l⟩
  simp only [List.reverse_toArray, Array.sum, List.foldr_toArray]
  exact foldr_reverse_comm (op := fun x1 x2 : α => x1 + x2) 0 l

-- `Array.prod_reverse` (`LawfulLeftIdentity (· * ·) 1`): same argument.
theorem prod_reverse_h5 {α : Type u} [inst : One α] [inst_1 : Mul α]
    [Std.Associative fun (x1 x2 : α) => x1 * x2] [Std.Commutative fun (x1 x2 : α) => x1 * x2]
    (xs : Array α) : xs.reverse.prod = xs.prod := by
  rcases xs with ⟨l⟩
  simp only [List.reverse_toArray, Array.prod, List.foldr_toArray]
  exact foldr_reverse_comm (op := fun x1 x2 : α => x1 * x2) 1 l

-- `Array.map_le` (`Asymm (<) α`): follows from `map_le_map_iff` (`Trichotomous α`, `Asymm β`).
theorem map_le_h4 {α : Type u} {β : Type v} [inst : LT α] [inst_1 : LT β]
    [Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [Std.Asymm fun (x1 x2 : β) => x1 < x2]
    [Std.Trichotomous fun (x1 x2 : β) => x1 < x2] {xs ys : Array α} {f : α → β}
    (w : ∀ (x y : α), x < y → f x < f y) (h : xs ≤ ys) : Array.map f xs ≤ Array.map f ys :=
  (Array.map_le_map_iff f w).mpr h

-- Derivability of `Asymm (<) α` in `Array.map_le` from `w` and `Asymm (<) β` (helper).
theorem map_le_asymm_derivable {α : Type u} {β : Type v} [inst : LT α] [inst_1 : LT β]
    [Std.Asymm fun (x1 x2 : β) => x1 < x2] {f : α → β}
    (w : ∀ (x y : α), x < y → f x < f y) : Std.Asymm fun (x1 x2 : α) => x1 < x2 :=
  ⟨fun a b hab hba => Std.Asymm.asymm _ _ (w a b hab) (w b a hba)⟩

-- `Array.map_le` (`Trichotomous (<) β`): follows from `map_le_map_iff` (`Trichotomous α`,
-- `Asymm β`).
theorem map_le_h7 {α : Type u} {β : Type v} [inst : LT α] [inst_1 : LT β]
    [Std.Asymm fun (x1 x2 : α) => x1 < x2] [Std.Trichotomous fun (x1 x2 : α) => x1 < x2]
    [Std.Asymm fun (x1 x2 : β) => x1 < x2] {xs ys : Array α} {f : α → β}
    (w : ∀ (x y : α), x < y → f x < f y) (h : xs ≤ ys) : Array.map f xs ≤ Array.map f ys :=
  (Array.map_le_map_iff f w).mpr h

end OrderArrayHand

/-! # Models -/

namespace OrderArrayModels

/-- Equivalence, not lawful. -/
def beqTrue : BEq Nat := ⟨fun _ _ => true⟩
/-- Not reflexive. -/
def beqFalse : BEq Nat := ⟨fun _ _ => false⟩
/-- `!=`: not reflexive. -/
def beqNe : BEq Nat := ⟨fun a b => a != b⟩
/-- `≤`: reflexive, transitive, not symmetric. -/
def beqLe : BEq Nat := ⟨fun a b => decide (a ≤ b)⟩
/-- `|a - b| ≤ 1`: reflexive, symmetric, not transitive. -/
def beqNear : BEq Nat := ⟨fun a b => decide (a ≤ b + 1 ∧ b ≤ a + 1)⟩
/-- `b → a`: reflexive, transitive, not symmetric. -/
def beqGe : BEq Bool := ⟨fun a b => a || !b⟩

/-- Total relation: trichotomous, not irreflexive. -/
def ltAll : LT Nat := ⟨fun _ _ => True⟩
/-- Empty relation: asymmetric, not trichotomous. -/
def ltNone : LT Nat := ⟨fun _ _ => False⟩
/-- `b = a + 2`: asymmetric; `¬ <` is not transitive (`¬ 1 < 2`, `¬ 0 < 1`, `0 < 2`). -/
def ltTwo : LT Nat := ⟨fun a b => b = a + 2⟩
def leTwo : LE Nat := ⟨fun a b => b = a + 2⟩
def ltHalf : LT Nat := ⟨fun a b => a / 2 < b / 2⟩
/-- Total preorder, not antisymmetric. -/
def leHalf : LE Nat := ⟨fun a b => a / 2 ≤ b / 2⟩
def ordHalf : Ord Nat := ⟨fun a b => compare (a / 2) (b / 2)⟩
def ordEq : Ord Nat := ⟨fun _ _ => .eq⟩

instance decLtAll : DecidableRel (@LT.lt Nat ltAll) := fun _ _ => instDecidableTrue
instance decLtNone : DecidableRel (@LT.lt Nat ltNone) := fun _ _ => instDecidableFalse
instance decLtTwo : DecidableRel (@LT.lt Nat ltTwo) := fun a b => Nat.decEq b (a + 2)
instance decLtHalf : DecidableRel (@LT.lt Nat ltHalf) := fun a b => Nat.decLt (a / 2) (b / 2)

theorem lawfulLT_two : @Std.LawfulOrderLT Nat ltTwo leTwo :=
  @Std.LawfulOrderLT.mk Nat ltTwo leTwo
    (fun a b => by show b = a + 2 ↔ b = a + 2 ∧ ¬ a = b + 2; omega)
theorem lawfulLT_half : @Std.LawfulOrderLT Nat ltHalf leHalf :=
  @Std.LawfulOrderLT.mk Nat ltHalf leHalf
    (fun a b => by show a / 2 < b / 2 ↔ a / 2 ≤ b / 2 ∧ ¬ b / 2 ≤ a / 2; omega)
theorem lawfulOrd_half : @Std.LawfulOrderOrd Nat ordHalf leHalf :=
  @Std.LawfulOrderOrd.mk Nat ordHalf leHalf
    (fun a b => Std.isLE_compare (a := a / 2) (b := b / 2))
    (fun a b => Std.isGE_compare (a := a / 2) (b := b / 2))

/-- `|a - b|`: commutative, identity `0`, not associative. -/
def addDist : Add Nat := ⟨fun a b => (a - b) + (b - a)⟩
/-- First nonzero argument: associative, identity `0`, not commutative. -/
def addFirst : Add Nat := ⟨fun a b => if a = 0 then b else a⟩
/-- `a + b + 1`: associative, commutative, no identity. -/
def addSucc : Add Nat := ⟨fun a b => a + b + 1⟩
/-- Left projection: associative, right identity only. -/
def addLeft : Add Nat := ⟨fun a _ => a⟩
def mulDist : Mul Nat := ⟨fun a b => (a - b) + (b - a)⟩
def mulFirst : Mul Nat := ⟨fun a b => if a = 0 then b else a⟩
def mulSucc : Mul Nat := ⟨fun a b => a + b + 1⟩
def mulLeft : Mul Nat := ⟨fun a _ => a⟩
def zero0 : Zero Nat := ⟨0⟩
def one0 : One Nat := ⟨0⟩
/-- Idempotent, not associative. -/
def minAvg : Min Nat := ⟨fun a b => (a + b) / 2⟩
def maxAvg : Max Nat := ⟨fun a b => (a + b) / 2⟩
/-- Not `MinEqOr`. -/
def minAdd : Min Nat := ⟨fun a b => a + b⟩
def maxAdd : Max Nat := ⟨fun a b => a + b⟩

theorem addDist_comm : Std.Commutative (fun x1 x2 : Nat => @HAdd.hAdd Nat Nat Nat (@instHAdd Nat addDist) x1 x2) :=
  ⟨fun a b => by show (a - b) + (b - a) = (b - a) + (a - b); omega⟩
theorem addDist_lid : Std.LawfulLeftIdentity (fun x1 x2 : Nat => @HAdd.hAdd Nat Nat Nat (@instHAdd Nat addDist) x1 x2) (@OfNat.ofNat Nat 0 (@Zero.toOfNat0 Nat zero0)) :=
  { left_id := fun a => by show (0 - a) + (a - 0) = a; omega }
theorem addDist_id : Std.LawfulIdentity (fun x1 x2 : Nat => @HAdd.hAdd Nat Nat Nat (@instHAdd Nat addDist) x1 x2) (@OfNat.ofNat Nat 0 (@Zero.toOfNat0 Nat zero0)) :=
  { left_id := fun a => by show (0 - a) + (a - 0) = a; omega
    right_id := fun a => by show (a - 0) + (0 - a) = a; omega }
theorem addFirst_assoc : Std.Associative (fun x1 x2 : Nat => @HAdd.hAdd Nat Nat Nat (@instHAdd Nat addFirst) x1 x2) :=
  ⟨fun a b c => by
    show (if (if a = 0 then b else a) = 0 then c else (if a = 0 then b else a)) =
      (if a = 0 then (if b = 0 then c else b) else a)
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]⟩
theorem addFirst_lid : Std.LawfulLeftIdentity (fun x1 x2 : Nat => @HAdd.hAdd Nat Nat Nat (@instHAdd Nat addFirst) x1 x2) (@OfNat.ofNat Nat 0 (@Zero.toOfNat0 Nat zero0)) :=
  { left_id := fun a => by show (if 0 = 0 then a else 0) = a; simp }
theorem addSucc_assoc : Std.Associative (fun x1 x2 : Nat => @HAdd.hAdd Nat Nat Nat (@instHAdd Nat addSucc) x1 x2) :=
  ⟨fun a b c => by show a + b + 1 + c + 1 = a + (b + c + 1) + 1; omega⟩
theorem addLeft_assoc : Std.Associative (fun x1 x2 : Nat => @HAdd.hAdd Nat Nat Nat (@instHAdd Nat addLeft) x1 x2) :=
  ⟨fun _ _ _ => rfl⟩

theorem mulDist_comm : Std.Commutative (fun x1 x2 : Nat => @HMul.hMul Nat Nat Nat (@instHMul Nat mulDist) x1 x2) :=
  ⟨fun a b => by show (a - b) + (b - a) = (b - a) + (a - b); omega⟩
theorem mulDist_lid : Std.LawfulLeftIdentity (fun x1 x2 : Nat => @HMul.hMul Nat Nat Nat (@instHMul Nat mulDist) x1 x2) (@OfNat.ofNat Nat 1 (@One.toOfNat1 Nat one0)) :=
  { left_id := fun a => by show (0 - a) + (a - 0) = a; omega }
theorem mulDist_id : Std.LawfulIdentity (fun x1 x2 : Nat => @HMul.hMul Nat Nat Nat (@instHMul Nat mulDist) x1 x2) (@OfNat.ofNat Nat 1 (@One.toOfNat1 Nat one0)) :=
  { left_id := fun a => by show (0 - a) + (a - 0) = a; omega
    right_id := fun a => by show (a - 0) + (0 - a) = a; omega }
theorem mulFirst_assoc : Std.Associative (fun x1 x2 : Nat => @HMul.hMul Nat Nat Nat (@instHMul Nat mulFirst) x1 x2) :=
  ⟨fun a b c => by
    show (if (if a = 0 then b else a) = 0 then c else (if a = 0 then b else a)) =
      (if a = 0 then (if b = 0 then c else b) else a)
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]⟩
theorem mulFirst_lid : Std.LawfulLeftIdentity (fun x1 x2 : Nat => @HMul.hMul Nat Nat Nat (@instHMul Nat mulFirst) x1 x2) (@OfNat.ofNat Nat 1 (@One.toOfNat1 Nat one0)) :=
  { left_id := fun a => by show (if 0 = 0 then a else 0) = a; simp }
theorem mulSucc_assoc : Std.Associative (fun x1 x2 : Nat => @HMul.hMul Nat Nat Nat (@instHMul Nat mulSucc) x1 x2) :=
  ⟨fun a b c => by show a + b + 1 + c + 1 = a + (b + c + 1) + 1; omega⟩
theorem mulLeft_assoc : Std.Associative (fun x1 x2 : Nat => @HMul.hMul Nat Nat Nat (@instHMul Nat mulLeft) x1 x2) :=
  ⟨fun _ _ _ => rfl⟩

theorem minAvg_idem : Std.IdempotentOp (@Min.min Nat minAvg) :=
  ⟨fun a => by show (a + a) / 2 = a; omega⟩
theorem maxAvg_idem : Std.IdempotentOp (@Max.max Nat maxAvg) :=
  ⟨fun a => by show (a + a) / 2 = a; omega⟩

/-- No non-lawful `BEq` instance is lawful (used for the dependent `LawfulBEq` hypotheses). -/
theorem not_all_lawfulBEq : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq α := by
  intro h
  have := @ReflBEq.rfl Nat beqFalse (@LawfulBEq.toReflBEq Nat beqFalse (@h Nat beqFalse)) 0
  revert this; decide

end OrderArrayModels

open OrderArrayModels

/-! # Necessary: `LawfulBEq`, `ReflBEq`, `PartialEquivBEq` -/

-- `Array.replace_append_right` (`LawfulBEq α`): `beqTrue`, `0 ∉ #[1]` but `1 == 0`.
example : ¬ ∀ {α : Type} [inst : BEq α] {a b : α} {xs ys : Array α},
    ¬a ∈ xs → (xs ++ ys).replace a b = xs ++ ys.replace a b := by
  intro h
  have := @h Nat beqTrue 0 5 #[1] #[] (by decide +kernel)
  revert this; decide +kernel

-- `Array.replace_replicate_ne` (`LawfulBEq α`): `beqLe`, `n = 1`, `a = 0`, `b = 1`: `b == a` is
-- false but `a == b` is true.
example : ¬ ∀ {α : Type} [inst : BEq α] {n : Nat} {a b c : α},
    (!b == a) = true → (Array.replicate n a).replace b c = Array.replicate n a := by
  intro h
  have := @h Nat beqLe 1 0 1 5 (by decide +kernel)
  revert this; decide +kernel

-- `Array.getElem?_replace_of_ne` (`LawfulBEq α`): `beqTrue`, `xs = #[1]`, `a = 0`, `i = 0`.
example : ¬ ∀ {α : Type} [inst : BEq α] {a b : α} {xs : Array α} {i : Nat},
    xs[i]? ≠ some a → (xs.replace a b)[i]? = xs[i]? := by
  intro h
  have := @h Nat beqTrue 0 5 #[1] 0 (by decide +kernel)
  revert this; decide +kernel

-- `Array.replace_append_left` (`LawfulBEq α`): `beqNe`, `xs = #[0]`, `ys = #[1]`, `a = 0`: the first
-- `x == 0` is in `ys`.
example : ¬ ∀ {α : Type} [inst : BEq α] {a b : α} {xs ys : Array α},
    a ∈ xs → (xs ++ ys).replace a b = xs.replace a b ++ ys := by
  intro h
  have := @h Nat beqNe 0 5 #[0] #[1] (by decide +kernel)
  revert this; decide +kernel

-- `Array.replace_replicate_self` (`LawfulBEq α`): `beqFalse`, `n = 1`.
example : ¬ ∀ {α : Type} [inst : BEq α] {n : Nat} {b a : α},
    0 < n → (Array.replicate n a).replace a b = #[b] ++ Array.replicate (n - 1) a := by
  intro h
  have := @h Nat beqFalse 1 1 0 (by decide)
  revert this; decide +kernel

-- `Array.count_replace` (`LawfulBEq α`): `beqNear`, `xs = #[1]`, `a = 0`, `b = 5`, `c = 2`.
example : ¬ ∀ {α : Type} [inst : BEq α] {a b c : α} {xs : Array α},
    Array.count c (xs.replace a b) =
      if xs.contains a = true then
        (Array.count c xs + if (b == c) = true then 1 else 0) - if (a == c) = true then 1 else 0
      else Array.count c xs := by
  intro h
  have := @h Nat beqNear 0 5 2 #[1]
  revert this; decide +kernel

-- `Array.countP_replace` (`LawfulBEq α`): `beqTrue`, `xs = #[1]`, `a = b = 0`, `p = (· = 1)`.
example : ¬ ∀ {α : Type} [inst : BEq α] {a b : α} {xs : Array α} {p : α → Bool},
    Array.countP p (xs.replace a b) =
      if xs.contains a = true then (Array.countP p xs + if p b = true then 1 else 0) - if p a = true then 1 else 0
      else Array.countP p xs := by
  intro h
  have := @h Nat beqTrue 0 0 #[1] (fun x => decide (x = 1))
  revert this; decide +kernel

-- `Array.erase_replicate_self` (`LawfulBEq α`): `beqFalse`, `n = 1`.
example : ¬ ∀ {α : Type} [inst : BEq α] {n : Nat} {a : α},
    (Array.replicate n a).erase a = Array.replicate (n - 1) a := by
  intro h
  have := @h Nat beqFalse 1 0
  revert this; decide +kernel

-- `Array.erase_append_left` (`LawfulBEq α`): `beqNe`, `xs = #[0]`, `ys = #[1]`, `a = 0`.
example : ¬ ∀ {α : Type} [inst : BEq α] {a : α} {xs : Array α} (ys : Array α),
    a ∈ xs → (xs ++ ys).erase a = xs.erase a ++ ys := by
  intro h
  have := @h Nat beqNe 0 #[0] #[1] (by decide +kernel)
  revert this; decide +kernel

-- `Array.size_erase_of_mem` (`LawfulBEq α`): `beqFalse`, `xs = #[0]`.
example : ¬ ∀ {α : Type} [inst : BEq α] {a : α} {xs : Array α},
    a ∈ xs → (xs.erase a).size = xs.size - 1 := by
  intro h
  have := @h Nat beqFalse 0 #[0] (by decide +kernel)
  revert this; decide +kernel

-- `Array.erase_filter` (`LawfulBEq α`): `beqTrue`, `xs = #[0, 1]`, `f = (· = 1)`.
example : ¬ ∀ {α : Type} [inst : BEq α] {a : α} {f : α → Bool} {xs : Array α},
    (Array.filter f xs).erase a = Array.filter f (xs.erase a) := by
  intro h
  have := @h Nat beqTrue 0 (fun x => decide (x = 1)) #[0, 1]
  revert this; decide +kernel

-- `Array.erase_comm` (`LawfulBEq α`): `beqLe`, `xs = #[0, 1]`, `a = 0`, `b = 1`.
example : ¬ ∀ {α : Type} [inst : BEq α] (a b : α) {xs : Array α},
    (xs.erase a).erase b = (xs.erase b).erase a := by
  intro h
  have := @h Nat beqLe 0 1 #[0, 1]
  revert this; decide +kernel

-- `Array.count_erase` (`LawfulBEq α`): `beqNear`, `xs = #[1]`, `a = 2`, `b = 0`.
example : ¬ ∀ {α : Type} [inst : BEq α] (a b : α) (xs : Array α),
    Array.count a (xs.erase b) = Array.count a xs - if (b == a) = true then 1 else 0 := by
  intro h
  have := @h Nat beqNear 2 0 #[1]
  revert this; decide +kernel

-- `Array.findIdx_eq_getD_bind_find?_idxOf?` (`LawfulBEq α`): `beqTrue`, `xs = #[0, 1]`,
-- `p = (· = 1)`.
example : ¬ ∀ {α : Type} [inst : BEq α] {xs : Array α} {p : α → Bool},
    Array.findIdx p xs = ((Array.find? p xs).bind fun (x : α) => xs.idxOf? x).getD xs.size := by
  intro h
  have := @h Nat beqTrue #[0, 1] (fun x => decide (x = 1))
  revert this; decide +kernel

-- `Array.findIdx?_eq_bind_find?_idxOf?` (`LawfulBEq α`): same values.
example : ¬ ∀ {α : Type} [inst : BEq α] {xs : Array α} {p : α → Bool},
    Array.findIdx? p xs = (Array.find? p xs).bind fun (x : α) => xs.idxOf? x := by
  intro h
  have := @h Nat beqTrue #[0, 1] (fun x => decide (x = 1))
  revert this; decide +kernel

-- `Array.findFinIdx?_eq_bind_find?_finIdxOf?` (`LawfulBEq α`): same values.
example : ¬ ∀ {α : Type} [inst : BEq α] {xs : Array α} {p : α → Bool},
    Array.findFinIdx? p xs = (Array.find? p xs).bind fun (x : α) => xs.finIdxOf? x := by
  intro h
  have := @h Nat beqTrue #[0, 1] (fun x => decide (x = 1))
  revert this; decide +kernel

-- `Array.instLawfulBEq` (`LawfulBEq α`): `beqFalse`, `#[0] == #[0]` is false.
example : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq (Array α) := by
  intro h
  have := @ReflBEq.rfl (Array Nat) _ (@LawfulBEq.toReflBEq _ _ (@h Nat beqFalse)) #[0]
  revert this; decide +kernel

-- `Array.exists_erase_eq` (`LawfulBEq α`): `beqFalse`, `xs = #[0]`, `a = 0`: `erase` keeps the
-- element, so the sizes don't add up.
example : ¬ ∀ {α : Type} [inst : BEq α] {a : α} {xs : Array α},
    a ∈ xs → ∃ (ys : Array α), ∃ (zs : Array α), ¬a ∈ ys ∧ xs = ys.push a ++ zs ∧ xs.erase a = ys ++ zs := by
  intro h
  obtain ⟨ys, zs, -, h1, h2⟩ := @h Nat beqFalse 0 #[0] (by decide +kernel)
  have e : @Array.erase Nat beqFalse #[0] 0 = #[0] := by decide +kernel
  rw [e] at h2
  have s1 := congrArg Array.size h1
  have s2 := congrArg Array.size h2
  simp only [Array.size_append, Array.size_push, List.size_toArray, List.length_cons,
    List.length_nil] at s1 s2
  omega

-- `Array.not_mem_of_count_eq_zero` (`LawfulBEq α`): `beqFalse`, `xs = #[0]`, `a = 0`.
example : ¬ ∀ {α : Type} [inst : BEq α] {a : α} {xs : Array α},
    Array.count a xs = 0 → ¬a ∈ xs := by
  intro h
  exact @h Nat beqFalse 0 #[0] (by decide +kernel) (by decide +kernel)

-- `Array.finIdxOf?_eq_some_iff` (`LawfulBEq α`): `beqFalse`, `xs = #[0]`, `a = 0`, `i = 0`.
example : ¬ ∀ {α : Type} [inst : BEq α] {xs : Array α} {a : α} {i : Fin xs.size},
    xs.finIdxOf? a = some i ↔ xs[i] = a ∧ ∀ (j : Fin xs.size), j < i → ¬xs[j] = a := by
  intro h
  have := @h Nat beqFalse #[0] 0 ⟨0, by decide⟩
  revert this; decide +kernel

-- `Array.erase_replicate` (`LawfulBEq α`): `beqLe`, `n = 1`, `a = 0`, `b = 1`: `erase` tests
-- `a == b`, the statement `b == a`.
example : ¬ ∀ {α : Type} [inst : BEq α] {n : Nat} {a b : α},
    (Array.replicate n a).erase b = if (b == a) = true then Array.replicate (n - 1) a else Array.replicate n a := by
  intro h
  have := @h Nat beqLe 1 0 1
  revert this; decide +kernel

-- `Array.erase_replicate_ne` (`LawfulBEq α`): same values.
example : ¬ ∀ {α : Type} [inst : BEq α] {n : Nat} {a b : α},
    (!b == a) = true → (Array.replicate n a).erase b = Array.replicate n a := by
  intro h
  have := @h Nat beqLe 1 0 1 (by decide +kernel)
  revert this; decide +kernel

-- `Array.getElem_replace` (`LawfulBEq α`, dependent: `a ∈ xs.take i` is decided with it).
example : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq α := not_all_lawfulBEq

-- `Array.getElem?_replace` (`LawfulBEq α`, dependent: decides `a ∈ xs.take i`).
example : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq α := not_all_lawfulBEq

-- `Array.replace_push` (`LawfulBEq α`, dependent: decides `b ∈ xs`).
example : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq α := not_all_lawfulBEq

-- `Array.replace_append` (`LawfulBEq α`, dependent: decides `a ∈ xs`).
example : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq α := not_all_lawfulBEq

-- `Array.contains_eq_mem` (`LawfulBEq α`, dependent: `decide (a ∈ xs)`).
example : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq α := not_all_lawfulBEq

-- `Array.elem_eq_mem` (`LawfulBEq α`, dependent: `decide (a ∈ xs)`).
example : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq α := not_all_lawfulBEq

-- `Array.idxOf_append` (`LawfulBEq α`, dependent: decides `a ∈ xs`).
example : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq α := not_all_lawfulBEq

-- `Array.erase_append` (`LawfulBEq α`, dependent: decides `a ∈ xs`).
example : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq α := not_all_lawfulBEq

-- `Array.size_erase` (`LawfulBEq α`, dependent: decides `a ∈ xs`).
example : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq α := not_all_lawfulBEq

-- `Array.contains_eq_true_of_mem` (`ReflBEq α`): `beqFalse`, `as = #[0]`.
example : ¬ ∀ {α : Type} [inst : BEq α] {a : α} {as : Array α}, a ∈ as → as.contains a = true := by
  intro h
  have := @h Nat beqFalse 0 #[0] (by decide +kernel)
  revert this; decide +kernel

-- `Array.instReflBEq` (`ReflBEq α`): `beqFalse`.
example : ¬ ∀ {α : Type} [inst : BEq α], ReflBEq (Array α) := by
  intro h
  have := @ReflBEq.rfl (Array Nat) _ (@h Nat beqFalse) #[0]
  revert this; decide +kernel

-- `Array.lex_eq_false_iff_exists` (`PartialEquivBEq α`): `Bool` with `beqGe` (`true == false`, not
-- `false == true`) and `lt = (!x && y)`; `l₁ = #[false]`, `l₂ = #[true]`: `lex` is true, but
-- `l₂` is `==` to `l₁.take 1`.
example : ¬ ∀ {α : Type} {l₁ l₂ : Array α} [inst : BEq α]
    (lt : α → α → Bool),
    (∀ (x y : α), (x == y) = true → lt x y = false) →
      (∀ (x y : α), lt x y = true → lt y x = false) →
        (∀ (x y : α), lt x y = false → lt y x = false → (x == y) = true) →
          (l₁.lex l₂ lt = false ↔
            (l₂.isEqv (l₁.take l₂.size) fun (x1 x2 : α) => x1 == x2) = true ∨
              ∃ (i : Nat),
                ∃ (h₁ : i < l₁.size),
                  ∃ (h₂ : i < l₂.size), (∀ (j : Nat) (hj : j < i), (l₁[j] == l₂[j]) = true) ∧
                    lt l₂[i] l₁[i] = true) := by
  intro h
  have := (@h Bool #[false] #[true] beqGe (fun x y => !x && y) (by decide) (by decide)
    (by decide)).mpr (Or.inl (by decide +kernel))
  revert this; decide +kernel

/-! # Necessary: lexicographic order -/

-- `Array.le_trans` (`LawfulOrderLT α`): standard `LE Nat`, `ltTwo`: `#[2] ≤ #[1] ≤ #[0]`, not
-- `#[2] ≤ #[0]`.
example : ¬ ∀ {α : Type} [inst : LE α] [inst_1 : LT α] [Std.IsLinearOrder α]
    {xs ys zs : Array α}, xs ≤ ys → ys ≤ zs → xs ≤ zs := by
  intro h
  have := @h Nat inferInstance ltTwo inferInstance #[2] #[1] #[0] (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Array.le_trans` (`IsLinearOrder α`): `leTwo`, `ltTwo`, same arrays.
example : ¬ ∀ {α : Type} [inst : LE α] [inst_1 : LT α] [Std.LawfulOrderLT α]
    {xs ys zs : Array α}, xs ≤ ys → ys ≤ zs → xs ≤ zs := by
  intro h
  have := @h Nat leTwo ltTwo lawfulLT_two #[2] #[1] #[0] (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Array.lt_of_le_of_lt` (`LawfulOrderLT α`): standard `LE Nat`, `ltTwo`: `#[1] ≤ #[0] < #[2]`.
example : ¬ ∀ {α : Type} [inst : LE α] [inst_1 : LT α] [Std.IsLinearOrder α]
    {xs ys zs : Array α}, xs ≤ ys → ys < zs → xs < zs := by
  intro h
  have := @h Nat inferInstance ltTwo inferInstance #[1] #[0] #[2] (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Array.lt_of_le_of_lt` (`IsLinearOrder α`): `leTwo`, `ltTwo`, same arrays.
example : ¬ ∀ {α : Type} [inst : LE α] [inst_1 : LT α] [Std.LawfulOrderLT α]
    {xs ys zs : Array α}, xs ≤ ys → ys < zs → xs < zs := by
  intro h
  have := @h Nat leTwo ltTwo lawfulLT_two #[1] #[0] #[2] (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Array.le_antisymm` (`IsLinearOrder α`): `leTwo`, `ltTwo`: `#[0] ≤ #[1] ≤ #[0]`.
example : ¬ ∀ {α : Type} [inst : LT α] [inst_1 : LE α] [Std.LawfulOrderLT α]
    {xs ys : Array α}, xs ≤ ys → ys ≤ xs → xs = ys := by
  intro h
  have := @h Nat ltTwo leTwo lawfulLT_two #[0] #[1] (by decide +kernel) (by decide +kernel)
  revert this; decide +kernel

-- `Array.instIsLinearOrderOfLawfulOrderLT` (`LawfulOrderLT α`): standard `LE Nat`, `ltTwo`;
-- `≤` on arrays is not transitive.
example : ¬ ∀ {α : Type} [inst : LT α] [inst_1 : LE α] [Std.IsLinearOrder α],
    Std.IsLinearOrder (Array α) := by
  intro h
  have := (@h Nat ltTwo inferInstance inferInstance).le_trans #[2] #[1] #[0] (by decide +kernel)
    (by decide +kernel)
  revert this; decide +kernel

-- `Array.instIsLinearOrderOfLawfulOrderLT` (`IsLinearOrder α`): `leTwo`, `ltTwo`.
example : ¬ ∀ {α : Type} [inst : LT α] [inst_1 : LE α] [Std.LawfulOrderLT α],
    Std.IsLinearOrder (Array α) := by
  intro h
  have := (@h Nat ltTwo leTwo lawfulLT_two).le_trans #[2] #[1] #[0] (by decide +kernel)
    (by decide +kernel)
  revert this; decide +kernel

-- `Array.instLawfulOrderOrd` (`IsLinearOrder α`): `leHalf`, `ltHalf`, `ordHalf`; `compare #[0, 3]
-- #[1, 0] = .gt` (`0 ≈ 1`), but `#[0, 3] ≤ #[1, 0]` (the lexicographic `<` needs `0 = 1`).
example : ¬ ∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Ord α]
    [Std.LawfulOrderLT α] [Std.LawfulOrderOrd α], Std.LawfulOrderOrd (Array α) := by
  intro h
  have := (@h Nat leHalf ltHalf ordHalf lawfulLT_half lawfulOrd_half).isLE_compare #[0, 3] #[1, 0]
  revert this; decide +kernel

-- `Array.instLawfulOrderOrd` (`LawfulOrderLT α`): standard `LE`, `Ord`, `ltTwo`; `#[1] ≤ #[0]`.
example : ¬ ∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Ord α] [Std.IsLinearOrder α]
    [Std.LawfulOrderOrd α], Std.LawfulOrderOrd (Array α) := by
  intro h
  have := (@h Nat inferInstance ltTwo inferInstance inferInstance inferInstance).isLE_compare #[1] #[0]
  revert this; decide +kernel

-- `Array.instLawfulOrderOrd` (`LawfulOrderOrd α`): standard `LE`, `LT`, `ordEq`.
example : ¬ ∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Ord α] [Std.IsLinearOrder α]
    [Std.LawfulOrderLT α], Std.LawfulOrderOrd (Array α) := by
  intro h
  have := (@h Nat inferInstance inferInstance ordEq inferInstance inferInstance).isLE_compare #[1] #[0]
  revert this; decide +kernel

-- `Array.ltIrrefl` (`Irrefl (<) α`): `ltAll`, `#[0] < #[0]`.
example : ¬ ∀ {α : Type} [inst : LT α], Std.Irrefl fun (x1 x2 : Array α) => x1 < x2 := by
  intro h
  exact (@h Nat ltAll).irrefl #[0] (by decide +kernel)

-- `Array.instReflLeOfIrreflLt` (`Irrefl (<) α`): `ltAll`, `¬ #[0] ≤ #[0]`.
example : ¬ ∀ {α : Type} [inst : LT α], Std.Refl fun (x1 x2 : Array α) => x1 ≤ x2 := by
  intro h
  have := (@h Nat ltAll).refl #[0]
  revert this; decide +kernel

-- `Array.instAsymmLt` (`Asymm (<) α`): `ltAll`, `#[0] < #[0]`.
example : ¬ ∀ {α : Type} [inst : LT α], Std.Asymm fun (x1 x2 : Array α) => x1 < x2 := by
  intro h
  exact (@h Nat ltAll).asymm #[0] #[0] (by decide +kernel) (by decide +kernel)

-- `Array.instTotalLeOfAsymmLt` (`Asymm (<) α`): `ltAll`, neither `#[0] ≤ #[0]`.
example : ¬ ∀ {α : Type} [inst : LT α], Std.Total fun (x1 x2 : Array α) => x1 ≤ x2 := by
  intro h
  have := (@h Nat ltAll).total #[0] #[0]
  revert this; decide +kernel

-- `Array.le_iff_exists` (`Trichotomous (<) α`): `ltNone`, `#[0] ≤ #[1]`, but neither disjunct.
example : ¬ ∀ {α : Type} [inst : LT α] [Std.Asymm fun (x1 x2 : α) => x1 < x2] {xs ys : Array α},
    xs ≤ ys ↔
      xs = ys.take xs.size ∨
        ∃ (i : Nat), ∃ (h₁ : i < xs.size), ∃ (h₂ : i < ys.size),
          (∀ (j : Nat) (hj : j < i), xs[j] = ys[j]) ∧ xs[i] < ys[i] := by
  intro h
  have := (@h Nat ltNone ⟨fun _ _ h => h.elim⟩ #[0] #[1]).mp (by decide +kernel)
  rcases this with h1 | ⟨i, h1, h2, -, hlt⟩
  · revert h1; decide +kernel
  · exact hlt

-- `Array.append_le_append_iff_of_size_eq` (`Trichotomous (<) α`): `ltNone`, `xs₁ = #[0]`,
-- `xs₂ = #[1]`, `ys₁ = ys₂ = #[]`.
example : ¬ ∀ {α : Type} [inst : LT α] [Std.Asymm fun (x1 x2 : α) => x1 < x2] {xs₁ xs₂ ys₁ ys₂ : Array α},
    xs₁.size = xs₂.size → (xs₁ ++ ys₁ ≤ xs₂ ++ ys₂ ↔ xs₁ < xs₂ ∨ xs₁ = xs₂ ∧ ys₁ ≤ ys₂) := by
  intro h
  have := @h Nat ltNone ⟨fun _ _ h => h.elim⟩ #[0] #[1] #[] #[] rfl
  revert this; decide +kernel

-- `Array.map_le_map_iff` (`Trichotomous (<) α`): `ltNone` on `α`, standard `β = Nat`,
-- `f = (1 - ·)`, `xs = #[0]`, `ys = #[1]`.
example : ¬ ∀ {α β : Type} [inst : LT α] [inst_2 : LT β] [Std.Asymm fun (x1 x2 : β) => x1 < x2]
    (f : α → β), (∀ (a b : α), a < b → f a < f b) → ∀ {xs ys : Array α},
      Array.map f xs ≤ Array.map f ys ↔ xs ≤ ys := by
  intro h
  have := @h Nat Nat ltNone inferInstance inferInstance (fun x => 1 - x) (fun _ _ h => h.elim) #[0] #[1]
  revert this; decide +kernel

-- `Array.map_lt_map_iff` (`Trichotomous (<) α`): same, `xs = #[1]`, `ys = #[0]`.
example : ¬ ∀ {α β : Type} [inst : LT α] [inst_2 : LT β] [Std.Asymm fun (x1 x2 : β) => x1 < x2]
    (f : α → β), (∀ (a b : α), a < b → f a < f b) → ∀ {xs ys : Array α},
      Array.map f xs < Array.map f ys ↔ xs < ys := by
  intro h
  have := @h Nat Nat ltNone inferInstance inferInstance (fun x => 1 - x) (fun _ _ h => h.elim) #[1] #[0]
  revert this; decide +kernel

-- `Array.map_le` (`Trichotomous (<) α`): `ltNone` on `α`, standard `β = Nat`, `f = (1 - ·)`,
-- `xs = #[0]`, `ys = #[1]`.
example : ¬ ∀ {α β : Type} [inst : LT α] [inst_1 : LT β] [Std.Asymm fun (x1 x2 : α) => x1 < x2]
    [Std.Asymm fun (x1 x2 : β) => x1 < x2] [Std.Trichotomous fun (x1 x2 : β) => x1 < x2]
    {xs ys : Array α} {f : α → β},
    (∀ (x y : α), x < y → f x < f y) → xs ≤ ys → Array.map f xs ≤ Array.map f ys := by
  intro h
  have := @h Nat Nat ltNone inferInstance ⟨fun _ _ h => h.elim⟩ inferInstance inferInstance
    #[0] #[1] (fun x => 1 - x) (fun _ _ h => h.elim) (by decide +kernel)
  revert this; decide +kernel

theorem singleton_append_eq {a b : Nat} {zs : Array Nat} (h : #[a] ++ zs = #[b]) : a = b := by
  have := congrArg (·[0]?) h
  rw [Array.getElem?_append_left (by simp)] at this
  simpa using this

-- `Array.flatMap_lt_flatMap_iff` (`Trichotomous (<) α`): `ltNone` on `α`, standard `β`,
-- `f a = #[a]`, `xs = #[0]`, `ys = #[1]`.
example : ¬ ∀ {α β : Type} [inst : LT α] [inst_2 : LT β] [Std.Asymm fun (x1 x2 : β) => x1 < x2]
    (f : α → Array β),
    (∀ (a b : α), a < b → f a < f b) →
      (∀ (a b : α) (zs : Array β), f a ++ zs = f b → a = b) →
        (∀ (a : α), f a ≠ #[]) → ∀ {xs ys : Array α}, Array.flatMap f xs < Array.flatMap f ys ↔ xs < ys := by
  intro h
  have := @h Nat Nat ltNone inferInstance inferInstance (fun a => #[a]) (fun _ _ h => h.elim)
    (fun _ _ _ h => singleton_append_eq h) (fun _ => by simp) #[0] #[1]
  revert this; decide +kernel

-- `Array.flatMap_lt_flatMap_iff` (`Asymm (<) β`): standard `α`, `ltAll` on `β`, `f a = #[a]`,
-- `xs = ys = #[0]`.
example : ¬ ∀ {α β : Type} [inst : LT α] [Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
    (f : α → Array β),
    (∀ (a b : α), a < b → f a < f b) →
      (∀ (a b : α) (zs : Array β), f a ++ zs = f b → a = b) →
        (∀ (a : α), f a ≠ #[]) → ∀ {xs ys : Array α}, Array.flatMap f xs < Array.flatMap f ys ↔ xs < ys := by
  intro h
  have := @h Nat Nat inferInstance inferInstance ltAll (fun a => #[a])
    (fun _ _ _ => List.Lex.rel True.intro) (fun _ _ _ h => singleton_append_eq h) (fun _ => by simp)
    #[0] #[0]
  revert this; decide +kernel

-- `Array.flatMap_le_flatMap_iff` (`Trichotomous (<) α`): `ltNone` on `α`, standard `β`,
-- `f a = #[a]`, `xs = #[1]`, `ys = #[0]`.
example : ¬ ∀ {α β : Type} [inst : LT α] [inst_2 : LT β] [Std.Asymm fun (x1 x2 : β) => x1 < x2]
    (f : α → Array β),
    (∀ (a b : α), a < b → f a < f b) →
      (∀ (a b : α) (zs : Array β), f a ++ zs = f b → a = b) →
        (∀ (a : α), f a ≠ #[]) → ∀ {xs ys : Array α}, Array.flatMap f xs ≤ Array.flatMap f ys ↔ xs ≤ ys := by
  intro h
  have := @h Nat Nat ltNone inferInstance inferInstance (fun a => #[a]) (fun _ _ h => h.elim)
    (fun _ _ _ h => singleton_append_eq h) (fun _ => by simp) #[1] #[0]
  revert this; decide +kernel

-- `Array.flatMap_le_flatMap_iff` (`Asymm (<) β`): standard `α`, `ltAll` on `β`, `f a = #[a]`,
-- `xs = ys = #[0]`.
example : ¬ ∀ {α β : Type} [inst : LT α] [Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
    (f : α → Array β),
    (∀ (a b : α), a < b → f a < f b) →
      (∀ (a b : α) (zs : Array β), f a ++ zs = f b → a = b) →
        (∀ (a : α), f a ≠ #[]) → ∀ {xs ys : Array α}, Array.flatMap f xs ≤ Array.flatMap f ys ↔ xs ≤ ys := by
  intro h
  have := @h Nat Nat inferInstance inferInstance ltAll (fun a => #[a])
    (fun _ _ _ => List.Lex.rel True.intro) (fun _ _ _ h => singleton_append_eq h) (fun _ => by simp)
    #[0] #[0]
  revert this; decide +kernel

/-! # Necessary: algebraic laws -/

-- `Array.foldl_min_eq_min` (`Associative min`): `min := (a + b) / 2`, `xs = #[0, 4]`, `a = 8`.
example : ¬ ∀ {α : Type} [inst : Min α] [Std.IdempotentOp (min : α → α → α)] {xs : Array α}
    (h : xs ≠ #[]) {a : α}, Array.foldl min a xs = min a (xs.min h) := by
  intro h
  have := @h Nat minAvg minAvg_idem #[0, 4] (by decide) 8
  revert this; decide +kernel

-- `Array.foldl_max_eq_max` (`Associative max`): `max := (a + b) / 2`, same values.
example : ¬ ∀ {α : Type} [inst : Max α] [Std.IdempotentOp (max : α → α → α)] {xs : Array α}
    (h : xs ≠ #[]) {a : α}, Array.foldl max a xs = max a (xs.max h) := by
  intro h
  have := @h Nat maxAvg maxAvg_idem #[0, 4] (by decide) 8
  revert this; decide +kernel

-- `Array.foldl_min` (`Associative min`): same values.
example : ¬ ∀ {α : Type} [inst : Min α] [Std.IdempotentOp (min : α → α → α)] {xs : Array α} {a : α},
    Array.foldl min a xs = min a (xs.min?.getD a) := by
  intro h
  have := @h Nat minAvg minAvg_idem #[0, 4] 8
  revert this; decide +kernel

-- `Array.foldl_max` (`Associative max`): same values.
example : ¬ ∀ {α : Type} [inst : Max α] [Std.IdempotentOp (max : α → α → α)] {xs : Array α} {a : α},
    Array.foldl max a xs = max a (xs.max?.getD a) := by
  intro h
  have := @h Nat maxAvg maxAvg_idem #[0, 4] 8
  revert this; decide +kernel

-- `Array.min?_mem` (`MinEqOr α`): `min := (· + ·)`, `#[1, 2].min? = some 3`.
example : ¬ ∀ {α : Type} {a : α} [inst : Min α] (xs : Array α), xs.min? = some a → a ∈ xs := by
  intro h
  have := @h Nat 3 minAdd #[1, 2] (by decide +kernel)
  revert this; decide +kernel

-- `Array.max?_mem` (`MaxEqOr α`): `max := (· + ·)`, `#[1, 2].max? = some 3`.
example : ¬ ∀ {α : Type} {a : α} [inst : Max α] (xs : Array α), xs.max? = some a → a ∈ xs := by
  intro h
  have := @h Nat 3 maxAdd #[1, 2] (by decide +kernel)
  revert this; decide +kernel

-- `Array.foldr_eq_foldl` (`Associative f`): `f = |a - b|`, `init = 0`, `xs = #[1, 2, 3]`.
example : ¬ ∀ {α : Type} {init : α} {xs : Array α} {f : α → α → α}
    [Std.LawfulIdentity f init], Array.foldr f init xs = Array.foldl f init xs := by
  intro h
  have := @h Nat 0 #[1, 2, 3] (fun a b => (a - b) + (b - a))
    { left_id := fun a => by omega, right_id := fun a => by omega }
  revert this; decide +kernel

-- `Array.sum_reverse` (`Associative (· + ·)`): `addDist`, `xs = #[1, 2, 3]`.
example : ¬ ∀ {α : Type} [inst : Zero α] [inst_1 : Add α]
    [Std.Commutative fun (x1 x2 : α) => x1 + x2] [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 + x2) 0]
    (xs : Array α), xs.reverse.sum = xs.sum := by
  intro h
  have := @h Nat zero0 addDist addDist_comm addDist_lid #[1, 2, 3]
  revert this; decide +kernel

-- `Array.sum_reverse` (`Commutative (· + ·)`): `addFirst`, `xs = #[1, 2]`.
example : ¬ ∀ {α : Type} [inst : Zero α] [inst_1 : Add α] [Std.Associative fun (x1 x2 : α) => x1 + x2]
    [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 + x2) 0]
    (xs : Array α), xs.reverse.sum = xs.sum := by
  intro h
  have := @h Nat zero0 addFirst addFirst_assoc addFirst_lid #[1, 2]
  revert this; decide +kernel

-- `Array.prod_reverse` (`Associative (· * ·)`): `mulDist`, `one0`, `xs = #[1, 2, 3]`.
example : ¬ ∀ {α : Type} [inst : One α] [inst_1 : Mul α]
    [Std.Commutative fun (x1 x2 : α) => x1 * x2] [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 * x2) 1]
    (xs : Array α), xs.reverse.prod = xs.prod := by
  intro h
  have := @h Nat one0 mulDist mulDist_comm mulDist_lid #[1, 2, 3]
  revert this; decide +kernel

-- `Array.prod_reverse` (`Commutative (· * ·)`): `mulFirst`, `one0`, `xs = #[1, 2]`.
example : ¬ ∀ {α : Type} [inst : One α] [inst_1 : Mul α] [Std.Associative fun (x1 x2 : α) => x1 * x2]
    [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 * x2) 1]
    (xs : Array α), xs.reverse.prod = xs.prod := by
  intro h
  have := @h Nat one0 mulFirst mulFirst_assoc mulFirst_lid #[1, 2]
  revert this; decide +kernel

-- `Array.sum_eq_foldl` (`Associative (· + ·)`): `addDist`, `xs = #[1, 2, 3]`.
example : ¬ ∀ {α : Type} [inst : Zero α] [inst_1 : Add α]
    [Std.LawfulIdentity (fun (x1 x2 : α) => x1 + x2) 0] {xs : Array α},
    xs.sum = Array.foldl (fun (x1 x2 : α) => x1 + x2) 0 xs := by
  intro h
  have := @h Nat zero0 addDist addDist_id #[1, 2, 3]
  revert this; decide +kernel

-- `Array.sum_eq_foldl` (`LawfulIdentity (· + ·) 0`): `addLeft`, `xs = #[1]`.
example : ¬ ∀ {α : Type} [inst : Zero α] [inst_1 : Add α] [Std.Associative fun (x1 x2 : α) => x1 + x2]
    {xs : Array α}, xs.sum = Array.foldl (fun (x1 x2 : α) => x1 + x2) 0 xs := by
  intro h
  have := @h Nat zero0 addLeft addLeft_assoc #[1]
  revert this; decide +kernel

-- `Array.prod_eq_foldl` (`Associative (· * ·)`): `mulDist`, `one0`, `xs = #[1, 2, 3]`.
example : ¬ ∀ {α : Type} [inst : One α] [inst_1 : Mul α]
    [Std.LawfulIdentity (fun (x1 x2 : α) => x1 * x2) 1] {xs : Array α},
    xs.prod = Array.foldl (fun (x1 x2 : α) => x1 * x2) 1 xs := by
  intro h
  have := @h Nat one0 mulDist mulDist_id #[1, 2, 3]
  revert this; decide +kernel

-- `Array.prod_eq_foldl` (`LawfulIdentity (· * ·) 1`): `mulLeft`, `one0`, `xs = #[1]`.
example : ¬ ∀ {α : Type} [inst : One α] [inst_1 : Mul α] [Std.Associative fun (x1 x2 : α) => x1 * x2]
    {xs : Array α}, xs.prod = Array.foldl (fun (x1 x2 : α) => x1 * x2) 1 xs := by
  intro h
  have := @h Nat one0 mulLeft mulLeft_assoc #[1]
  revert this; decide +kernel

-- `Array.sum_append` (`Associative (· + ·)`): `addDist`, `#[1, 2] ++ #[3]`.
example : ¬ ∀ {α : Type} [inst : Zero α] [inst_1 : Add α]
    [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 + x2) 0] {as₁ as₂ : Array α},
    (as₁ ++ as₂).sum = as₁.sum + as₂.sum := by
  intro h
  have := @h Nat zero0 addDist addDist_lid #[1, 2] #[3]
  revert this; decide +kernel

-- `Array.sum_append` (`LawfulLeftIdentity (· + ·) 0`): `addSucc`, `#[] ++ #[]`.
example : ¬ ∀ {α : Type} [inst : Zero α] [inst_1 : Add α] [Std.Associative fun (x1 x2 : α) => x1 + x2]
    {as₁ as₂ : Array α}, (as₁ ++ as₂).sum = as₁.sum + as₂.sum := by
  intro h
  have := @h Nat zero0 addSucc addSucc_assoc #[] #[]
  revert this; decide +kernel

-- `Array.prod_append` (`Associative (· * ·)`): `mulDist`, `one0`, `#[1, 2] ++ #[3]`.
example : ¬ ∀ {α : Type} [inst : One α] [inst_1 : Mul α]
    [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 * x2) 1] {as₁ as₂ : Array α},
    (as₁ ++ as₂).prod = as₁.prod * as₂.prod := by
  intro h
  have := @h Nat one0 mulDist mulDist_lid #[1, 2] #[3]
  revert this; decide +kernel

-- `Array.prod_append` (`LawfulLeftIdentity (· * ·) 1`): `mulSucc`, `one0`, `#[] ++ #[]`.
example : ¬ ∀ {α : Type} [inst : One α] [inst_1 : Mul α] [Std.Associative fun (x1 x2 : α) => x1 * x2]
    {as₁ as₂ : Array α}, (as₁ ++ as₂).prod = as₁.prod * as₂.prod := by
  intro h
  have := @h Nat one0 mulSucc mulSucc_assoc #[] #[]
  revert this; decide +kernel

-- `Array.sum_push` (`Associative (· + ·)`): `addDist`, `xs = #[1, 2]`, `x = 3`.
example : ¬ ∀ {α : Type} [inst : Add α] [inst_1 : Zero α]
    [Std.LawfulIdentity (fun (x1 x2 : α) => x1 + x2) 0] {xs : Array α} {x : α},
    (xs.push x).sum = xs.sum + x := by
  intro h
  have := @h Nat addDist zero0 addDist_id #[1, 2] 3
  revert this; decide +kernel

-- `Array.sum_push` (`LawfulIdentity (· + ·) 0`): `addLeft`, `xs = #[]`, `x = 1`.
example : ¬ ∀ {α : Type} [inst : Add α] [inst_1 : Zero α] [Std.Associative fun (x1 x2 : α) => x1 + x2]
    {xs : Array α} {x : α}, (xs.push x).sum = xs.sum + x := by
  intro h
  have := @h Nat addLeft zero0 addLeft_assoc #[] 1
  revert this; decide +kernel

-- `Array.prod_push` (`Associative (· * ·)`): `mulDist`, `one0`, `xs = #[1, 2]`, `x = 3`.
example : ¬ ∀ {α : Type} [inst : Mul α] [inst_1 : One α]
    [Std.LawfulIdentity (fun (x1 x2 : α) => x1 * x2) 1] {xs : Array α} {x : α},
    (xs.push x).prod = xs.prod * x := by
  intro h
  have := @h Nat mulDist one0 mulDist_id #[1, 2] 3
  revert this; decide +kernel

-- `Array.prod_push` (`LawfulIdentity (· * ·) 1`): `mulLeft`, `one0`, `xs = #[]`, `x = 1`.
example : ¬ ∀ {α : Type} [inst : Mul α] [inst_1 : One α] [Std.Associative fun (x1 x2 : α) => x1 * x2]
    {xs : Array α} {x : α}, (xs.push x).prod = xs.prod * x := by
  intro h
  have := @h Nat mulLeft one0 mulLeft_assoc #[] 1
  revert this; decide +kernel

-- `Array.sum_singleton` (`LawfulRightIdentity (· + ·) 0`): `addSucc`, `#[0].sum = 1`.
example : ¬ ∀ {α : Type} [inst : Add α] [inst_1 : Zero α] {x : α}, #[x].sum = x := by
  intro h
  have := @h Nat addSucc zero0 0
  revert this; decide +kernel

-- `Array.prod_singleton` (`LawfulRightIdentity (· * ·) 1`): `mulSucc`, `one0`, `#[0].prod = 1`.
example : ¬ ∀ {α : Type} [inst : Mul α] [inst_1 : One α] {x : α}, #[x].prod = x := by
  intro h
  have := @h Nat mulSucc one0 0
  revert this; decide +kernel
