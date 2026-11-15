/-!
Hand resolution of the 71 instance hypotheses in `Init.Data.Vector.*` (cluster `OrderVector`) that
`HypCheck.lean` left unresolved. For each hypothesis `hᵢ` of theorem `T`, this file proves `T'`
(removable), `¬T'` (necessary), or, for a dependent hypothesis, `¬∀ indep, Hᵢ`.

Removable (6):
* `Vector.map_le` (`[Asymm α]` and `[Trichotomous β]`): only `[Trichotomous α]` and `[Asymm β]` are
  needed. If `map f ys < map f xs` lexicographically, compare the first heads `a`, `b`: trichotomy
  of `α` and strict monotonicity of `f` turn `f b < f a` into `b < a` and `f b = f a` into `b = a`
  (anything else contradicts asymmetry, hence irreflexivity, of `β`). So `ys < xs`
  (`list_lt_of_map_lt`); equal lengths are not even needed.
* `Vector.prod_reverse`, `Vector.sum_reverse` (`[LawfulLeftIdentity]`): `foldr op e` of a reversed
  list equals `foldr op e` of the list for every associative and commutative `op` and every `e`
  (`foldr_reverse`); the identity law is not used.
* `Vector.replace_extract` (`[LawfulBEq α]`): `replace` changes the first index `j` with
  `xs[j] == a`, for any `BEq`; taking a prefix commutes with that (`List.replace_take` holds for any
  `BEq`; `Array.replace` is `List.replace` for the flipped `BEq`, `array_replace_toArray`).
* `Vector.count_replicate` (`[LawfulBEq α]`): `count a` is `countP (· == a)`, and
  `countP p (replicate n b) = if p b then n else 0` for every `p`.

All 65 others are necessary. Models (all on `Nat`, by type synonyms where `decide` needs a decidable
order):
* `BEq Nat`: `bFalse` (never true: not reflexive), `bSum1` (`x + y = 1`: symmetric, not reflexive),
  `bGe` (`y ≤ x`: reflexive and transitive, not symmetric).
* `NF`: `<` everywhere false (asymmetric, irreflexive, not trichotomous), standard `≤`/`compare`.
* `NR`: `<` is `≤` (trichotomous, not irreflexive/asymmetric).
* `NC`: cyclic `a < b ↔ b ≡ a + 1 (mod 3)`, `≤` its reflexive closure (`LawfulOrderLT`, not
  transitive); `NCs`: the same `<` with the standard `≤` (`IsLinearOrder`, not `LawfulOrderLT`).
* `NP`: parity preorder `a % 2 ≤ b % 2` with matching `<` and `compare` (`LawfulOrderLT`,
  `LawfulOrderOrd`, not antisymmetric); vectors compare equal-parity entries differently with
  `compareLex` (`.eq`, continue) and `<` (stop, since `List.Lex` continues only on `=`).
* `NE`: standard `≤`/`<`, `compare` always `.eq`.
* `Add`/`Mul Nat`: left projection (associative, right but no left identity), right projection
  (no right identity), `opNA e` (two-sided identity `e`, not associative), `opNAC e` (commutative
  with identity `e`, not associative), `opLI e` (`if a = e then b else a`: associative with left
  identity, not commutative).
* `Fin 2` for `NoNatZeroDivisors` (`2 • 1 = 2 • 0`), `Empty` for `Nonempty`, `n = 0` for `NeZero`.
Dependent `[LawfulBEq α]` hypotheses (used by `Decidable (a ∈ xs)` in the statement) are refuted
as `¬ ∀ α [BEq α], LawfulBEq α`.

Run with the lean4 repo's stage1 binary: `lean checks/OrderVectorHand.lean`.
-/

set_option warn.classDefReducibility false
set_option linter.unusedVariables false

universe u v

namespace OrderVectorHand

/-! ## `BEq Nat` models -/

/-- Never true: not reflexive. -/
def bFalse : BEq Nat := ⟨fun _ _ => false⟩
/-- `x == y ↔ x + y = 1`: symmetric, not reflexive. -/
def bSum1 : BEq Nat := ⟨fun x y => x + y == 1⟩
/-- `x == y ↔ y ≤ x`: reflexive and transitive, not symmetric. -/
def bGe : BEq Nat := ⟨fun x y => decide (y ≤ x)⟩

/-! ## Order models -/

/-- `Nat` with `<` everywhere false and the standard `≤` and `compare`. -/
def NF := Nat
instance : LT NF := ⟨fun _ _ => False⟩
instance : LE NF := inferInstanceAs (LE Nat)
instance : Ord NF := inferInstanceAs (Ord Nat)
instance : DecidableLT NF := fun _ _ => (isFalse id : Decidable False)
instance : DecidableEq NF := inferInstanceAs (DecidableEq Nat)
instance : OfNat NF n := ⟨(n : Nat)⟩
instance : Std.Asymm (· < · : NF → NF → Prop) := ⟨fun _ _ h => h.elim⟩
instance : Std.Irrefl (· < · : NF → NF → Prop) := ⟨fun _ h => h⟩
instance : Std.IsLinearOrder NF := inferInstanceAs (Std.IsLinearOrder Nat)
instance : Std.LawfulOrderOrd NF := inferInstanceAs (Std.LawfulOrderOrd Nat)
def NF.toNat (a : NF) : Nat := a

/-- `Nat` with `<` being `≤`. -/
def NR := Nat
instance : LT NR := ⟨fun a b => @LE.le Nat _ a b⟩
instance : DecidableLT NR := fun a b => Nat.decLe a b
instance : DecidableEq NR := inferInstanceAs (DecidableEq Nat)
instance : OfNat NR n := ⟨(n : Nat)⟩
instance : Std.Trichotomous (· < · : NR → NR → Prop) :=
  ⟨fun a b h1 h2 => Nat.le_antisymm (Nat.le_of_not_le h2) (Nat.le_of_not_le h1)⟩

/-- Cyclic relation on residues mod 3. -/
def cyc (a b : Nat) : Prop := (a + 1) % 3 = b % 3
/-- Reflexive closure of `cyc`. -/
def cycLe (a b : Nat) : Prop := a % 3 = b % 3 ∨ (a + 1) % 3 = b % 3
def cycDec : DecidableRel cyc := fun a b => Nat.decEq ((a + 1) % 3) (b % 3)

/-- Cyclic `<` on residues mod 3, `≤` its reflexive closure. -/
def NC := Nat
instance : LT NC := ⟨cyc⟩
instance : LE NC := ⟨cycLe⟩
instance : DecidableLT NC := cycDec
instance : DecidableEq NC := inferInstanceAs (DecidableEq Nat)
instance : OfNat NC n := ⟨(n : Nat)⟩
instance : Std.LawfulOrderLT NC := ⟨fun a b => by
  show cyc a b ↔ cycLe a b ∧ ¬ cycLe b a
  unfold cyc cycLe; omega⟩

/-- The cyclic `<` of `NC` with the standard `≤`. -/
def NCs := Nat
instance : LT NCs := ⟨cyc⟩
instance : LE NCs := inferInstanceAs (LE Nat)
instance : DecidableLT NCs := cycDec
instance : DecidableEq NCs := inferInstanceAs (DecidableEq Nat)
instance : OfNat NCs n := ⟨(n : Nat)⟩
instance : Std.IsLinearOrder NCs := inferInstanceAs (Std.IsLinearOrder Nat)

/-- Parity preorder. -/
def parLt (a b : Nat) : Prop := a % 2 < b % 2
def parLe (a b : Nat) : Prop := a % 2 ≤ b % 2
def parCmp (a b : Nat) : Ordering := compare (a % 2) (b % 2)
def parDec : DecidableRel parLt := fun a b => Nat.decLt (a % 2) (b % 2)

/-- Parity preorder: `≤`, `<` and `compare` of `a % 2`. -/
def NP := Nat
instance : LT NP := ⟨parLt⟩
instance : LE NP := ⟨parLe⟩
instance : Ord NP := ⟨parCmp⟩
instance : DecidableLT NP := parDec
instance : DecidableEq NP := inferInstanceAs (DecidableEq Nat)
instance : OfNat NP n := ⟨(n : Nat)⟩
instance : Std.LawfulOrderLT NP := ⟨fun a b => by
  show parLt a b ↔ parLe a b ∧ ¬ parLe b a
  unfold parLt parLe; omega⟩
instance : Std.LawfulOrderOrd NP :=
  ⟨fun (a b : Nat) => Std.LawfulOrderOrd.isLE_compare (α := Nat) (a % 2) (b % 2),
   fun (a b : Nat) => Std.LawfulOrderOrd.isGE_compare (α := Nat) (a % 2) (b % 2)⟩

/-- Standard `≤` and `<`, `compare` always `.eq`. -/
def NE := Nat
instance : LT NE := inferInstanceAs (LT Nat)
instance : LE NE := inferInstanceAs (LE Nat)
instance : Ord NE := ⟨fun _ _ => .eq⟩
instance : DecidableLT NE := inferInstanceAs (DecidableLT Nat)
instance : DecidableEq NE := inferInstanceAs (DecidableEq Nat)
instance : OfNat NE n := ⟨(n : Nat)⟩
instance : Std.IsLinearOrder NE := inferInstanceAs (Std.IsLinearOrder Nat)
instance : Std.LawfulOrderLT NE := inferInstanceAs (Std.LawfulOrderLT Nat)

/-! ## Operation models -/

/-- Left projection: associative; `e` is a right identity but no left identity. -/
def addLeft : Add Nat := ⟨fun a _ => a⟩
def mulLeft : Mul Nat := ⟨fun a _ => a⟩
/-- Right projection: no right identity. -/
def addRight : Add Nat := ⟨fun _ b => b⟩
def mulRight : Mul Nat := ⟨fun _ b => b⟩

theorem addLeft_assoc : @Std.Associative Nat (fun x y => @HAdd.hAdd _ _ _ (@instHAdd _ addLeft) x y) :=
  ⟨fun _ _ _ => rfl⟩
theorem mulLeft_assoc : @Std.Associative Nat (fun x y => @HMul.hMul _ _ _ (@instHMul _ mulLeft) x y) :=
  ⟨fun _ _ _ => rfl⟩

/-- Two-sided identity `e`, not associative. -/
def opNA (e a b : Nat) : Nat := if a = e then b else if b = e then a else 2 * a + b
/-- Commutative with identity `e`, not associative. -/
def opNAC (e a b : Nat) : Nat := if a = e then b else if b = e then a else 2 * (a + b)
/-- Associative with left identity `e`, not commutative. -/
def opLI (e a b : Nat) : Nat := if a = e then b else a

theorem opNA_left (e a : Nat) : opNA e e a = a := by simp [opNA]
theorem opNA_right (e a : Nat) : opNA e a e = a := by unfold opNA; split <;> simp_all
theorem opNAC_left (e a : Nat) : opNAC e e a = a := by simp [opNAC]
theorem opNAC_comm (e a b : Nat) : opNAC e a b = opNAC e b a := by
  unfold opNAC; split <;> split <;> omega
theorem opLI_left (e a : Nat) : opLI e e a = a := by simp [opLI]
theorem opLI_assoc (e a b c : Nat) : opLI e (opLI e a b) c = opLI e a (opLI e b c) := by
  unfold opLI; split <;> simp_all

def addNA : Add Nat := ⟨opNA 0⟩
def mulNA : Mul Nat := ⟨opNA 1⟩
def addNAC : Add Nat := ⟨opNAC 0⟩
def mulNAC : Mul Nat := ⟨opNAC 1⟩
def addLI : Add Nat := ⟨opLI 0⟩
def mulLI : Mul Nat := ⟨opLI 1⟩

theorem lawfulIdentity (op : Nat → Nat → Nat) (e : Nat) (h1 : ∀ a, op e a = a)
    (h2 : ∀ a, op a e = a) : Std.LawfulIdentity op e :=
  @Std.LawfulIdentity.mk _ _ _ (@Std.Identity.mk _ _ _ ⟨⟩)
    (@Std.LawfulLeftIdentity.mk _ _ _ _ ⟨⟩ h1) (@Std.LawfulRightIdentity.mk _ _ _ _ ⟨⟩ h2)

theorem lawfulLeftIdentity (op : Nat → Nat → Nat) (e : Nat) (h1 : ∀ a, op e a = a) :
    Std.LawfulLeftIdentity op e :=
  @Std.LawfulLeftIdentity.mk _ _ _ _ ⟨⟩ h1

theorem addNA_id : @Std.LawfulIdentity Nat (fun x y => @HAdd.hAdd _ _ _ (@instHAdd _ addNA) x y) 0 :=
  lawfulIdentity _ _ (opNA_left 0) (opNA_right 0)
theorem mulNA_id : @Std.LawfulIdentity Nat (fun x y => @HMul.hMul _ _ _ (@instHMul _ mulNA) x y) 1 :=
  lawfulIdentity _ _ (opNA_left 1) (opNA_right 1)
theorem addNAC_comm : @Std.Commutative Nat (fun x y => @HAdd.hAdd _ _ _ (@instHAdd _ addNAC) x y) :=
  ⟨opNAC_comm 0⟩
theorem mulNAC_comm : @Std.Commutative Nat (fun x y => @HMul.hMul _ _ _ (@instHMul _ mulNAC) x y) :=
  ⟨opNAC_comm 1⟩
theorem addNAC_lid :
    @Std.LawfulLeftIdentity Nat Nat (fun x y => @HAdd.hAdd _ _ _ (@instHAdd _ addNAC) x y) 0 :=
  lawfulLeftIdentity _ _ (opNAC_left 0)
theorem mulNAC_lid :
    @Std.LawfulLeftIdentity Nat Nat (fun x y => @HMul.hMul _ _ _ (@instHMul _ mulNAC) x y) 1 :=
  lawfulLeftIdentity _ _ (opNAC_left 1)
theorem addLI_assoc : @Std.Associative Nat (fun x y => @HAdd.hAdd _ _ _ (@instHAdd _ addLI) x y) :=
  ⟨opLI_assoc 0⟩
theorem mulLI_assoc : @Std.Associative Nat (fun x y => @HMul.hMul _ _ _ (@instHMul _ mulLI) x y) :=
  ⟨opLI_assoc 1⟩
theorem addLI_lid :
    @Std.LawfulLeftIdentity Nat Nat (fun x y => @HAdd.hAdd _ _ _ (@instHAdd _ addLI) x y) 0 :=
  lawfulLeftIdentity _ _ (opLI_left 0)
theorem mulLI_lid :
    @Std.LawfulLeftIdentity Nat Nat (fun x y => @HMul.hMul _ _ _ (@instHMul _ mulLI) x y) 1 :=
  lawfulLeftIdentity _ _ (opLI_left 1)

/-! ## Helper lemmas for the removable verdicts -/

theorem list_lt_of_map_lt {α : Type u} {β : Type v} [LT α] [LT β]
    [Std.Trichotomous (· < · : α → α → Prop)] [Std.Asymm (· < · : β → β → Prop)] (f : α → β)
    (w : ∀ x y, x < y → f x < f y) : ∀ l₁ l₂ : List α, l₁.map f < l₂.map f → l₁ < l₂
  | [], [], h => absurd h (List.not_lt_nil _)
  | [], _ :: _, _ => List.nil_lt_cons _ _
  | _ :: _, [], h => absurd h (List.not_lt_nil _)
  | a :: l₁, b :: l₂, h => by
    have irr : ∀ c : β, ¬ c < c := fun c hc => Std.Asymm.asymm c c hc hc
    rw [List.map_cons, List.map_cons, List.cons_lt_cons_iff] at h
    rw [List.cons_lt_cons_iff]
    by_cases hab : a < b
    · exact .inl hab
    by_cases hba : b < a
    · rcases h with h | ⟨h, -⟩
      · exact absurd (w b a hba) (Std.Asymm.asymm _ _ h)
      · exact absurd (h ▸ w b a hba) (irr _)
    have e := Std.Trichotomous.trichotomous a b hab hba
    subst e
    rcases h with h | ⟨-, h⟩
    · exact absurd h (irr _)
    · exact .inr ⟨rfl, list_lt_of_map_lt f w l₁ l₂ h⟩

/-- `Vector.map_le` with only `[Trichotomous α]` and `[Asymm β]`. -/
theorem vector_map_le {α : Type u} {β : Type v} {n : Nat} [LT α] [LT β]
    [Std.Trichotomous (· < · : α → α → Prop)] [Std.Asymm (· < · : β → β → Prop)]
    {xs ys : Vector α n} {f : α → β} (w : ∀ x y, x < y → f x < f y) (h : xs ≤ ys) :
    Vector.map f xs ≤ Vector.map f ys := by
  intro hc
  apply h
  have hc' : ys.toArray.toList.map f < xs.toArray.toList.map f := by simpa using hc
  exact list_lt_of_map_lt f w _ _ hc'

theorem foldr_append_singleton {α : Type u} (op : α → α → α) [Std.Associative op]
    [Std.Commutative op] (e x : α) :
    ∀ l : List α, (l ++ [x]).foldr op e = op x (l.foldr op e)
  | [] => rfl
  | y :: t => by
    rw [List.cons_append, List.foldr_cons, foldr_append_singleton op e x t, List.foldr_cons,
      ← Std.Associative.assoc (op := op), Std.Commutative.comm (op := op) y x,
      Std.Associative.assoc (op := op)]

/-- `foldr` is invariant under reversal for associative, commutative operations, any `e`. -/
theorem foldr_reverse {α : Type u} (op : α → α → α) [Std.Associative op]
    [Std.Commutative op] (e : α) : ∀ l : List α, l.reverse.foldr op e = l.foldr op e
  | [] => rfl
  | y :: t => by
    rw [List.reverse_cons, foldr_append_singleton, foldr_reverse op e t, List.foldr_cons]

/-- The flipped `BEq`: `Array.replace` tests `xs[i] == a`, `List.replace` tests `a == x`. -/
def flipBEq {α : Type u} [BEq α] : BEq α := ⟨fun x y => y == x⟩

theorem replace_eq_flip {α : Type u} [BEq α] (a b : α) : ∀ l : List α,
    (match l.finIdxOf? a with | none => l | some i => l.set i b) = @List.replace α flipBEq l a b
  | [] => rfl
  | x :: t => by
    have ih := replace_eq_flip a b t
    rw [List.finIdxOf?_cons]
    show _ = (match x == a with
      | true => b :: t | false => x :: @List.replace α flipBEq t a b)
    cases h : x == a
    · cases hf : t.finIdxOf? a <;> simp only [hf] at ih
      · simp only [Option.map_none]; rw [← ih]; rfl
      · simp only [Option.map_some]; rw [← ih]; rfl
    · simp

theorem array_replace_toArray {α : Type u} [BEq α] (l : List α) (a b : α) :
    l.toArray.replace a b = (@List.replace α flipBEq l a b).toArray := by
  rw [← replace_eq_flip, Array.replace]
  cases h : l.toArray.finIdxOf? a with
  | none => rw [List.finIdxOf?_toArray] at h; simp [h]
  | some i => rw [List.finIdxOf?_toArray] at h; simp [h]

end OrderVectorHand

open OrderVectorHand

/-! # Removable (6) -/

-- `Vector.map_le` (`[Asymm α]`, idx 5): only `[Trichotomous α]` and `[Asymm β]` are used
-- (`vector_map_le`).
theorem map_le_h5 {α : Type u} {β : Type v} {n : Nat} [inst : LT α] [inst_1 : LT β]
    [Std.Trichotomous fun (x1 x2 : α) => x1 < x2]
    [Std.Asymm fun (x1 x2 : β) => x1 < x2] [Std.Trichotomous fun (x1 x2 : β) => x1 < x2]
    {xs ys : Vector α n} {f : α → β} :
    (∀ (x y : α), x < y → f x < f y) → xs ≤ ys → Vector.map f xs ≤ Vector.map f ys :=
  vector_map_le

-- `Vector.map_le` (`[Trichotomous β]`, idx 8): same argument.
theorem map_le_h8 {α : Type u} {β : Type v} {n : Nat} [inst : LT α] [inst_1 : LT β]
    [Std.Asymm fun (x1 x2 : α) => x1 < x2] [Std.Trichotomous fun (x1 x2 : α) => x1 < x2]
    [Std.Asymm fun (x1 x2 : β) => x1 < x2] {xs ys : Vector α n} {f : α → β} :
    (∀ (x y : α), x < y → f x < f y) → xs ≤ ys → Vector.map f xs ≤ Vector.map f ys :=
  vector_map_le

-- `Vector.prod_reverse` (`[LawfulLeftIdentity]`): `foldr_reverse` needs only associativity and
-- commutativity.
theorem prod_reverse_h6 {α : Type u} {n : Nat} [inst : One α] [inst_1 : Mul α]
    [Std.Associative fun (x1 x2 : α) => x1 * x2] [Std.Commutative fun (x1 x2 : α) => x1 * x2]
    (xs : Vector α n) : xs.reverse.prod = xs.prod := by
  rw [← Vector.prod_toList, ← Vector.prod_toList, Vector.toList_reverse]
  exact foldr_reverse _ _ _

-- `Vector.sum_reverse` (`[LawfulLeftIdentity]`): same argument.
theorem sum_reverse_h6 {α : Type u} {n : Nat} [inst : Zero α] [inst_1 : Add α]
    [Std.Associative fun (x1 x2 : α) => x1 + x2] [Std.Commutative fun (x1 x2 : α) => x1 + x2]
    (xs : Vector α n) : xs.reverse.sum = xs.sum := by
  rw [← Vector.sum_toList, ← Vector.sum_toList, Vector.toList_reverse]
  exact foldr_reverse _ _ _

-- `Vector.replace_extract` (`[LawfulBEq α]`): `replace` and prefixes commute for any `BEq`
-- (`array_replace_toArray`, `List.replace_take`).
theorem replace_extract_h2 {α : Type u} [inst : BEq α] {n : Nat} {a b : α} {xs : Vector α n}
    {i : Nat} : (xs.extract 0 i).replace a b = (xs.replace a b).extract 0 i := by
  rcases xs with ⟨⟨l⟩, rfl⟩
  apply Vector.toArray_inj.mp
  simp only [Vector.replace, Vector.extract, Vector.toArray_mk]
  simp [array_replace_toArray, @List.replace_take α flipBEq]

-- `Vector.count_replicate` (`[LawfulBEq α]`): `count a = countP (· == a)` and `countP_replicate`
-- holds for every predicate.
theorem count_replicate_h2 {α : Type u} [inst : BEq α] {a b : α} {n : Nat} :
    Vector.count a (Vector.replicate n b) = if (b == a) = true then n else 0 := by
  simp [Vector.count, Array.count, Array.countP_replicate]

/-! # Necessary: `BEq` lemmas -/

-- `Vector.contains_eq_true_of_mem` (`[LawfulBEq α]`): `bFalse`, `a = 0`, `as = #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : BEq α] {a : α} {as : Vector α n},
    a ∈ as → as.contains a = true :=
  fun H => absurd (@H Nat 1 bFalse 0 #v[0] (by simp)) (by decide +kernel)

-- `Vector.replace_replicate_ne` (`[LawfulBEq α]`): `bGe`, `a = 1`, `b = 0`: `b == a` is false but
-- `replace` tests `a == b`, which is true.
example : ¬ ∀ {α : Type} [inst : BEq α] {n : Nat} {a b c : α},
    (!b == a) = true → (Vector.replicate n a).replace b c = Vector.replicate n a :=
  fun H => absurd (@H Nat bGe 1 1 0 5 rfl) (by decide +kernel)

-- `Vector.replace_append_left` (`[LawfulBEq α]`): `bSum1`, `xs = #v[0]`, `ys = #v[1]`, `a = 0`:
-- only the element of `ys` is `== 0`.
example : ¬ ∀ {α : Type} [inst : BEq α] {n m : Nat} {a b : α} {xs : Vector α n}
    {ys : Vector α m}, a ∈ xs → (xs ++ ys).replace a b = xs.replace a b ++ ys :=
  fun H => absurd (@H Nat bSum1 1 1 0 5 #v[0] #v[1] (by simp)) (by decide +kernel)

-- `Vector.replace_append_right` (`[LawfulBEq α]`): `bSum1`, `xs = #v[1]`, `ys = #v[]`, `a = 0`:
-- `0 ∉ xs` but `1 == 0`.
example : ¬ ∀ {α : Type} [inst : BEq α] {n m : Nat} {a b : α} {xs : Vector α n}
    {ys : Vector α m}, ¬a ∈ xs → (xs ++ ys).replace a b = xs ++ ys.replace a b :=
  fun H => absurd (@H Nat bSum1 1 0 0 5 #v[1] #v[] (by simp)) (by decide +kernel)

-- `Vector.countP_replace` (`[LawfulBEq α]`): `bSum1`, `xs = #v[1]`, `a = b = 0`, `p = (· = 1)`.
example : ¬ ∀ {α : Type} [inst : BEq α] {n : Nat} {a b : α} {xs : Vector α n} {p : α → Bool},
    Vector.countP p (xs.replace a b) =
      if xs.contains a = true then (Vector.countP p xs + if p b = true then 1 else 0) -
        if p a = true then 1 else 0
      else Vector.countP p xs :=
  fun H => absurd (@H Nat bSum1 1 0 0 #v[1] (fun x => decide (x = 1))) (by decide +kernel)

-- `Vector.count_replace` (`[LawfulBEq α]`): `bSum1`, `xs = #v[1]`, `a = b = 0`, `c = 1`.
example : ¬ ∀ {α : Type} [inst : BEq α] {n : Nat} {a b c : α} {xs : Vector α n},
    Vector.count c (xs.replace a b) =
      if xs.contains a = true then
        (Vector.count c xs + if (b == c) = true then 1 else 0) - if (a == c) = true then 1 else 0
      else Vector.count c xs :=
  fun H => absurd (@H Nat bSum1 1 0 0 1 #v[1]) (by decide +kernel)

-- `Vector.not_mem_of_count_eq_zero` (`[LawfulBEq α]`): `bFalse`, `a = 0`, `xs = #v[0]`.
example : ¬ ∀ {α : Type} [inst : BEq α] {n : Nat} {a : α} {xs : Vector α n},
    Vector.count a xs = 0 → ¬a ∈ xs :=
  fun H => @H Nat bFalse 1 0 #v[0] (by decide +kernel) (by simp)

-- `Vector.findFinIdx?_eq_bind_find?_finIdxOf?` (`[LawfulBEq α]`): `bFalse`, `xs = #v[0]`,
-- `p = fun _ => true`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : BEq α] {xs : Vector α n} {p : α → Bool},
    Vector.findFinIdx? p xs = (Vector.find? p xs).bind fun (x : α) => xs.finIdxOf? x :=
  fun H => absurd (@H Nat 1 bFalse #v[0] (fun _ => true)) (by decide +kernel)

-- `Vector.any_beq'` (`[PartialEquivBEq α]`): `bGe`, `xs = #v[0]`, `a = 1`: `0 == 1` is false,
-- `1 == 0` is true.
example : ¬ ∀ {α : Type} {n : Nat} {a : α} [inst : BEq α] {xs : Vector α n},
    (xs.any fun (x : α) => x == a) = xs.contains a :=
  fun H => absurd (@H Nat 1 1 bGe #v[0]) (by decide +kernel)

-- `Vector.all_bne'` (`[PartialEquivBEq α]`): same values.
example : ¬ ∀ {α : Type} {n : Nat} {a : α} [inst : BEq α] {xs : Vector α n},
    (xs.all fun (x : α) => x != a) = !xs.contains a :=
  fun H => absurd (@H Nat 1 1 bGe #v[0]) (by decide +kernel)

-- `Vector.lex_eq_false_iff_exists` (`[PartialEquivBEq α]`): `bGe`, `lt = (· < ·)`,
-- `xs = #v[0]`, `ys = #v[1]`: `lex` is true, but `ys.isEqv xs (· == ·)` holds.
example : ¬ ∀ {α : Type} {n : Nat} [inst : BEq α] (lt : α → α → Bool),
    (∀ (x y : α), (x == y) = true → lt x y = false) →
      (∀ (x y : α), lt x y = true → lt y x = false) →
        (∀ (x y : α), lt x y = false → lt y x = false → (x == y) = true) →
          ∀ {xs ys : Vector α n},
            xs.lex ys lt = false ↔
              (ys.isEqv xs fun (x1 x2 : α) => x1 == x2) = true ∨
                ∃ (i : Nat), ∃ (h : i < n),
                  (∀ (j : Nat) (hj : j < i), (xs[j] == ys[j]) = true) ∧ lt ys[i] xs[i] = true :=
  fun H => by
    have h := (@H Nat 1 bGe (fun x y => decide (x < y))
      (fun x y h => by change decide (y ≤ x) = true at h; simp at h ⊢; omega)
      (fun x y h => by simp at h ⊢; omega)
      (fun x y h1 h2 => by simp at h1 h2; change decide (y ≤ x) = true; simp; omega)
      #v[0] #v[1]).mpr
      (.inl (by decide +kernel))
    exact absurd h (by decide +kernel)

-- `Vector.getElem_replace` (`[LawfulBEq α]`, dependent: `Decidable (a ∈ xs.take i)` uses it):
-- `bFalse` is not lawful.
example : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq α :=
  fun H => absurd (@ReflBEq.rfl Nat bFalse (@H Nat bFalse).toReflBEq 0) (by decide)

-- `Vector.getElem?_replace` (`[LawfulBEq α]`, dependent): `bFalse` is not lawful.
example : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq α :=
  fun H => absurd (@ReflBEq.rfl Nat bFalse (@H Nat bFalse).toReflBEq 0) (by decide)

-- `Vector.replace_push` (`[LawfulBEq α]`, dependent): `bFalse` is not lawful.
example : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq α :=
  fun H => absurd (@ReflBEq.rfl Nat bFalse (@H Nat bFalse).toReflBEq 0) (by decide)

-- `Vector.replace_append` (`[LawfulBEq α]`, dependent): `bFalse` is not lawful.
example : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq α :=
  fun H => absurd (@ReflBEq.rfl Nat bFalse (@H Nat bFalse).toReflBEq 0) (by decide)

-- `Vector.contains_eq_mem` (`[LawfulBEq α]`, dependent: `decide (a ∈ as)` uses it): `bFalse`.
example : ¬ ∀ {α : Type} [inst : BEq α], LawfulBEq α :=
  fun H => absurd (@ReflBEq.rfl Nat bFalse (@H Nat bFalse).toReflBEq 0) (by decide)

-- `Vector.instReflBEq` (`[ReflBEq α]`): `n = 1`, `bFalse`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : BEq α], ReflBEq (Vector α n) :=
  fun H => absurd (@ReflBEq.rfl _ _ (@H Nat 1 bFalse) #v[0]) (by decide +kernel)

-- `Vector.instLawfulBEq` (`[LawfulBEq α]`): `n = 1`, `bFalse`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : BEq α], LawfulBEq (Vector α n) :=
  fun H => absurd (@ReflBEq.rfl _ _ (@H Nat 1 bFalse).toReflBEq #v[0]) (by decide +kernel)

/-! # Necessary: `NeZero n` -/

-- `Vector.map_inj` (`[NeZero n]`): `n = 0`, `f = id`, `g = fun _ => 0`.
example : ¬ ∀ {n : Nat} {α : Type} {α_1 : Type} {f g : α → α_1},
    Vector.map (n := n) f = Vector.map g ↔ f = g :=
  fun H => absurd (congrFun ((@H 0 Nat Nat id (fun _ => 0)).mp
    (funext fun v => Vector.ext fun i h => absurd h (Nat.not_lt_zero i))) 1) (by decide)

-- `Vector.reflBEq_iff` (`[NeZero n]`): `n = 0`, `bFalse`: `Vector Nat 0` is reflexive.
example : ¬ ∀ {α : Type} {n : Nat} [inst : BEq α], ReflBEq (Vector α n) ↔ ReflBEq α :=
  fun H => absurd (@ReflBEq.rfl Nat bFalse ((@H Nat 0 bFalse).mp ⟨fun {_} => rfl⟩) 0) (by decide)

-- `Vector.lawfulBEq_iff` (`[NeZero n]`): `n = 0`, `bFalse`: `Vector Nat 0` is lawful.
example : ¬ ∀ {α : Type} {n : Nat} [inst : BEq α], LawfulBEq (Vector α n) ↔ LawfulBEq α :=
  fun H => absurd (@ReflBEq.rfl Nat bFalse ((@H Nat 0 bFalse).mp
    { rfl := fun {_} => rfl
      eq_of_beq := fun {_ _} _ => Vector.ext fun i h => absurd h (Nat.not_lt_zero i) }).toReflBEq 0)
    (by decide)

/-! # Necessary: other instances -/

-- `Vector.instNonempty` (`[Nonempty α]`): `α = Empty`, `n = 1`.
example : ¬ ∀ {α : Type} {n : Nat}, Nonempty (Vector α n) :=
  fun H => (@H Empty 1).elim fun v => nomatch v[0]

-- `Vector.instAddRightCancel` (`[AddRightCancel α]`): `n = 1`, `a + b = 0`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Add α], Lean.Grind.AddRightCancel (Vector α n) :=
  fun H => absurd (@Lean.Grind.AddRightCancel.add_right_cancel _ _ (@H Nat 1 ⟨fun _ _ => 0⟩)
    #v[0] #v[1] #v[0] (by decide +kernel)) (by decide)

-- `Vector.instNoNatZeroDivisors` (`[NoNatZeroDivisors α]`): `α = Fin 2`, `n = 1`:
-- `2 • #v[1] = 2 • #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Lean.Grind.NatModule α],
    Lean.Grind.NoNatZeroDivisors (Vector α n) :=
  fun H => absurd (@Lean.Grind.NoNatZeroDivisors.no_nat_zero_divisors _ _ (@H (Fin 2) 1 _)
    2 #v[1] #v[0] (by decide) (by decide +kernel)) (by decide)

/-! # Necessary: order lemmas and instances -/

-- `Vector.append_le_append_iff` (`[Trichotomous]`): `NF` (`<` false, so `≤` always true),
-- `xs₁ = #v[0]`, `xs₂ = #v[1]`, `m = 0`.
example : ¬ ∀ {α : Type} {n m : Nat} [inst : LT α] [Std.Asymm fun (x1 x2 : α) => x1 < x2]
    {xs₁ xs₂ : Vector α n} {ys₁ ys₂ : Vector α m},
    xs₁ ++ ys₁ ≤ xs₂ ++ ys₂ ↔ xs₁ < xs₂ ∨ xs₁ = xs₂ ∧ ys₁ ≤ ys₂ :=
  fun H => absurd (@H NF 1 0 _ _ #v[0] #v[1] #v[] #v[]) (by decide +kernel)

-- `Vector.map_le` (`[Trichotomous α]`, idx 6): `NF → Nat`, `xs = #v[1]`, `ys = #v[0]`.
example : ¬ ∀ {α β : Type} {n : Nat} [inst : LT α] [inst_1 : LT β]
    [Std.Asymm fun (x1 x2 : α) => x1 < x2] [Std.Asymm fun (x1 x2 : β) => x1 < x2]
    [Std.Trichotomous fun (x1 x2 : β) => x1 < x2] {xs ys : Vector α n} {f : α → β},
    (∀ (x y : α), x < y → f x < f y) → xs ≤ ys → Vector.map f xs ≤ Vector.map f ys :=
  fun H => absurd (@H NF Nat 1 _ _ _ _ _ #v[1] #v[0] NF.toNat (fun _ _ h => False.elim h)
    (by decide +kernel)) (by decide +kernel)

-- `Vector.map_le_map_iff` (`[Trichotomous α]`): `NF → Nat`, `xs = #v[1]`, `ys = #v[0]`.
example : ¬ ∀ {α β : Type} {n : Nat} [inst : LT α] [inst_2 : LT β]
    [Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → β),
    (∀ (a b : α), a < b → f a < f b) → ∀ {xs ys : Vector α n},
      Vector.map f xs ≤ Vector.map f ys ↔ xs ≤ ys :=
  fun H => absurd (@H NF Nat 1 _ _ _ NF.toNat (fun _ _ h => False.elim h) #v[1] #v[0])
    (by decide +kernel)

-- `Vector.map_lt_map_iff` (`[Trichotomous α]`): `NF → Nat`, `xs = #v[0]`, `ys = #v[1]`.
example : ¬ ∀ {α β : Type} {n : Nat} [inst : LT α] [inst_2 : LT β]
    [Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → β),
    (∀ (a b : α), a < b → f a < f b) → ∀ {xs ys : Vector α n},
      Vector.map f xs < Vector.map f ys ↔ xs < ys :=
  fun H => absurd (@H NF Nat 1 _ _ _ NF.toNat (fun _ _ h => False.elim h) #v[0] #v[1])
    (by decide +kernel)

-- `Vector.flatMap_lt_flatMap_iff` (`[Trichotomous α]`): `NF → Nat`, `f a = #v[a]`,
-- `xs = #v[0]`, `ys = #v[1]`.
example : ¬ ∀ {α β : Type} {m n : Nat} [inst : LT α] [inst_2 : LT β]
    [Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → Vector β m),
    (∀ (a b : α), a < b → f a < f b) → 0 < m → ∀ {xs ys : Vector α n},
      xs.flatMap f < ys.flatMap f ↔ xs < ys :=
  fun H => absurd (@H NF Nat 1 1 _ _ _ (fun a => #v[NF.toNat a]) (fun _ _ h => False.elim h)
    (by decide) #v[0] #v[1]) (by decide +kernel)

-- `Vector.flatMap_lt_flatMap_iff` (`[Asymm β]`): `Nat → NR` (`<` is `≤`), `f = fun _ => #v[0]`,
-- `xs = ys = #v[0]`.
example : ¬ ∀ {α β : Type} {m n : Nat} [inst : LT α]
    [Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β] (f : α → Vector β m),
    (∀ (a b : α), a < b → f a < f b) → 0 < m → ∀ {xs ys : Vector α n},
      xs.flatMap f < ys.flatMap f ↔ xs < ys :=
  fun H => absurd (@H Nat NR 1 1 _ _ _ (fun _ => #v[0]) (fun _ _ _ => by decide +kernel)
    (by decide) #v[0] #v[0]) (by decide +kernel)

-- `Vector.flatMap_le_flatMap_iff` (`[Trichotomous α]`): `NF → Nat`, `f a = #v[a]`,
-- `xs = #v[1]`, `ys = #v[0]`.
example : ¬ ∀ {α β : Type} {m n : Nat} [inst : LT α] [inst_2 : LT β]
    [Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → Vector β m),
    (∀ (a b : α), a < b → f a < f b) → 0 < m → ∀ {xs ys : Vector α n},
      xs.flatMap f ≤ ys.flatMap f ↔ xs ≤ ys :=
  fun H => absurd (@H NF Nat 1 1 _ _ _ (fun a => #v[NF.toNat a]) (fun _ _ h => False.elim h)
    (by decide) #v[1] #v[0]) (by decide +kernel)

-- `Vector.flatMap_le_flatMap_iff` (`[Asymm β]`): `Nat → NR`, `f = fun _ => #v[0]`,
-- `xs = ys = #v[0]`.
example : ¬ ∀ {α β : Type} {m n : Nat} [inst : LT α]
    [Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β] (f : α → Vector β m),
    (∀ (a b : α), a < b → f a < f b) → 0 < m → ∀ {xs ys : Vector α n},
      xs.flatMap f ≤ ys.flatMap f ↔ xs ≤ ys :=
  fun H => absurd (@H Nat NR 1 1 _ _ _ (fun _ => #v[0]) (fun _ _ _ => by decide +kernel)
    (by decide) #v[0] #v[0]) (by decide +kernel)

-- `Vector.le_trans` (`[LawfulOrderLT α]`): `NCs` (cyclic `<`, standard `≤`), `0 ≤ 1 ≤ 2`,
-- but `2 < 0`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : LT α] [inst_1 : LE α] [Std.IsLinearOrder α]
    {xs ys zs : Vector α n}, xs ≤ ys → ys ≤ zs → xs ≤ zs :=
  fun H => absurd (@H NCs 1 _ _ _ #v[0] #v[1] #v[2] (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

-- `Vector.le_trans` (`[IsLinearOrder α]`): `NC` (cyclic `<`, `LawfulOrderLT`), same values.
example : ¬ ∀ {α : Type} {n : Nat} [inst : LT α] [inst_1 : LE α] [Std.LawfulOrderLT α]
    {xs ys zs : Vector α n}, xs ≤ ys → ys ≤ zs → xs ≤ zs :=
  fun H => absurd (@H NC 1 _ _ _ #v[0] #v[1] #v[2] (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

-- `Vector.lt_of_le_of_lt` (`[LawfulOrderLT α]`): `NCs`, `0 ≤ 1 < 2`, `¬ 0 < 2`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : LT α] [inst_1 : LE α] [Std.IsLinearOrder α]
    {xs ys zs : Vector α n}, xs ≤ ys → ys < zs → xs < zs :=
  fun H => absurd (@H NCs 1 _ _ _ #v[0] #v[1] #v[2] (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

-- `Vector.lt_of_le_of_lt` (`[IsLinearOrder α]`): `NC`, same values.
example : ¬ ∀ {α : Type} {n : Nat} [inst : LT α] [inst_1 : LE α] [Std.LawfulOrderLT α]
    {xs ys zs : Vector α n}, xs ≤ ys → ys < zs → xs < zs :=
  fun H => absurd (@H NC 1 _ _ _ #v[0] #v[1] #v[2] (by decide +kernel) (by decide +kernel))
    (by decide +kernel)

-- `Vector.instIsLinearOrderOfLawfulOrderLT` (`[IsLinearOrder α]`): `NC`, `n = 1`: not transitive.
example : ¬ ∀ {α : Type} {n : Nat} [inst : LT α] [inst_1 : LE α] [Std.LawfulOrderLT α],
    Std.IsLinearOrder (Vector α n) :=
  fun H => absurd (@Std.IsPreorder.le_trans _ _ (@H NC 1 _ _ _).toIsPartialOrder.toIsPreorder
    #v[0] #v[1] #v[2] (by decide +kernel) (by decide +kernel)) (by decide +kernel)

-- `Vector.instIsLinearOrderOfLawfulOrderLT` (`[LawfulOrderLT α]`): `NF`, `n = 1`: `≤` is
-- always true, not antisymmetric.
example : ¬ ∀ {α : Type} {n : Nat} [inst : LT α] [inst_1 : LE α] [Std.IsLinearOrder α],
    Std.IsLinearOrder (Vector α n) :=
  fun H => absurd (@Std.IsPartialOrder.le_antisymm _ _ (@H NF 1 _ _ _).toIsPartialOrder
    #v[0] #v[1] (by decide +kernel) (by decide +kernel)) (by decide)

-- `Vector.instLawfulOrderOrd` (`[IsLinearOrder α]`): `NP` (parity), `n = 2`:
-- `compare #v[0, 1] #v[2, 0] = .gt` (`0` and `2` compare equal), but `#v[0, 1] ≤ #v[2, 0]`
-- (`0 ≠ 2`, neither `<`).
example : ¬ ∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Ord α] [Std.LawfulOrderLT α]
    [Std.LawfulOrderOrd α] {n : Nat}, Std.LawfulOrderOrd (Vector α n) :=
  fun H => absurd ((@Std.LawfulOrderOrd.isLE_compare _ _ _ (@H NP _ _ _ _ _ 2)
    #v[0, 1] #v[2, 0]).mpr (by decide +kernel)) (by decide +kernel)

-- `Vector.instLawfulOrderOrd` (`[LawfulOrderLT α]`): `NF`, `n = 1`: `compare #v[1] #v[0] = .gt`
-- but `#v[1] ≤ #v[0]`.
example : ¬ ∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Ord α] [Std.IsLinearOrder α]
    [Std.LawfulOrderOrd α] {n : Nat}, Std.LawfulOrderOrd (Vector α n) :=
  fun H => absurd ((@Std.LawfulOrderOrd.isLE_compare _ _ _ (@H NF _ _ _ _ _ 1)
    #v[1] #v[0]).mpr (by decide +kernel)) (by decide +kernel)

-- `Vector.instLawfulOrderOrd` (`[LawfulOrderOrd α]`): `NE` (`compare` always `eq`), `n = 1`.
example : ¬ ∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Ord α] [Std.IsLinearOrder α]
    [Std.LawfulOrderLT α] {n : Nat}, Std.LawfulOrderOrd (Vector α n) :=
  fun H => absurd ((@Std.LawfulOrderOrd.isLE_compare _ _ _ (@H NE _ _ _ _ _ 1)
    #v[1] #v[0]).mp (by decide +kernel)) (by decide +kernel)

-- `Vector.instReflLeOfIrreflLt` (`[Irrefl]`): `NR` (`<` is `≤`), `n = 1`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : LT α], Std.Refl fun (x1 x2 : Vector α n) => x1 ≤ x2 :=
  fun H => absurd ((@H NR 1 _).refl #v[0]) (by decide +kernel)

-- `Vector.instTotalLeOfAsymmLt` (`[Asymm]`): `NR`, `n = 1`: `¬ #v[0] ≤ #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : LT α], Std.Total fun (x1 x2 : Vector α n) => x1 ≤ x2 :=
  fun H => absurd ((@H NR 1 _).total #v[0] #v[0]) (by decide +kernel)

-- `Vector.instLawfulOrderLTOfAsymmLt` (`[Asymm]`): `NR`, `n = 1`: `#v[0] < #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : LT α], Std.LawfulOrderLT (Vector α n) :=
  fun H => (fun h => h.2 h.1) ((@Std.LawfulOrderLT.lt_iff _ _ _ (@H NR 1 _) #v[0] #v[0]).mp
    (by decide +kernel))

-- `Vector.ltIrrefl` (`[Irrefl]`): `NR`, `n = 1`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : LT α], Std.Irrefl fun (x1 x2 : Vector α n) => x1 < x2 :=
  fun H => (@H NR 1 _).irrefl #v[0] (by decide +kernel)

-- `Vector.instAsymmLt` (`[Asymm]`): `NR`, `n = 1`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : LT α], Std.Asymm fun (x1 x2 : Vector α n) => x1 < x2 :=
  fun H => (@H NR 1 _).asymm #v[0] #v[0] (by decide +kernel) (by decide +kernel)

/-! # Necessary: `sum`/`prod`/`foldr` lemmas -/

-- `Vector.prod_eq_foldl` (`[Associative]`): `mulNA`, `xs = #v[2, 2, 2]` (`10 ≠ 14`).
example : ¬ ∀ {α : Type} {n : Nat} [inst : One α] [inst_1 : Mul α]
    [Std.LawfulIdentity (fun (x1 x2 : α) => x1 * x2) 1] {xs : Vector α n},
    xs.prod = Vector.foldl (fun (x1 x2 : α) => x1 * x2) 1 xs :=
  fun H => absurd (@H Nat 3 _ mulNA mulNA_id #v[2, 2, 2]) (by decide +kernel)

-- `Vector.prod_eq_foldl` (`[LawfulIdentity]`): left projection, `xs = #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : One α] [inst_1 : Mul α]
    [Std.Associative fun (x1 x2 : α) => x1 * x2] {xs : Vector α n},
    xs.prod = Vector.foldl (fun (x1 x2 : α) => x1 * x2) 1 xs :=
  fun H => absurd (@H Nat 1 _ mulLeft mulLeft_assoc #v[0]) (by decide +kernel)

-- `Vector.sum_eq_foldl` (`[Associative]`): `addNA`, `xs = #v[1, 1, 1]` (`5 ≠ 7`).
example : ¬ ∀ {α : Type} {n : Nat} [inst : Zero α] [inst_1 : Add α]
    [Std.LawfulIdentity (fun (x1 x2 : α) => x1 + x2) 0] {xs : Vector α n},
    xs.sum = Vector.foldl (fun (x1 x2 : α) => x1 + x2) 0 xs :=
  fun H => absurd (@H Nat 3 _ addNA addNA_id #v[1, 1, 1]) (by decide +kernel)

-- `Vector.sum_eq_foldl` (`[LawfulIdentity]`): left projection, `xs = #v[1]`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Zero α] [inst_1 : Add α]
    [Std.Associative fun (x1 x2 : α) => x1 + x2] {xs : Vector α n},
    xs.sum = Vector.foldl (fun (x1 x2 : α) => x1 + x2) 0 xs :=
  fun H => absurd (@H Nat 1 _ addLeft addLeft_assoc #v[1]) (by decide +kernel)

-- `Vector.foldr_eq_foldl` (`[Associative f]`): `f = opNA 0`, `init = 0`, `xs = #v[1, 1, 1]`.
example : ¬ ∀ {α : Type} {n : Nat} {init : α} {xs : Vector α n} {f : α → α → α}
    [Std.LawfulIdentity f init], Vector.foldr f init xs = Vector.foldl f init xs :=
  fun H => absurd (@H Nat 3 0 #v[1, 1, 1] (opNA 0)
    (lawfulIdentity _ _ (opNA_left 0) (opNA_right 0))) (by decide +kernel)

-- `Vector.sum_push` (`[Associative]`): `addNA`, `xs = #v[1, 1]`, `x = 1`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Add α] [inst_1 : Zero α]
    [Std.LawfulIdentity (fun (x1 x2 : α) => x1 + x2) 0] {xs : Vector α n} {x : α},
    (xs.push x).sum = xs.sum + x :=
  fun H => absurd (@H Nat 2 addNA _ addNA_id #v[1, 1] 1) (by decide +kernel)

-- `Vector.sum_push` (`[LawfulIdentity]`): left projection, `xs = #v[]`, `x = 1`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Add α] [inst_1 : Zero α]
    [Std.Associative fun (x1 x2 : α) => x1 + x2] {xs : Vector α n} {x : α},
    (xs.push x).sum = xs.sum + x :=
  fun H => absurd (@H Nat 0 addLeft _ addLeft_assoc #v[] 1) (by decide +kernel)

-- `Vector.prod_push` (`[Associative]`): `mulNA`, `xs = #v[2, 2]`, `x = 2`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Mul α] [inst_1 : One α]
    [Std.LawfulIdentity (fun (x1 x2 : α) => x1 * x2) 1] {xs : Vector α n} {x : α},
    (xs.push x).prod = xs.prod * x :=
  fun H => absurd (@H Nat 2 mulNA _ mulNA_id #v[2, 2] 2) (by decide +kernel)

-- `Vector.prod_push` (`[LawfulIdentity]`): left projection, `xs = #v[]`, `x = 0`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Mul α] [inst_1 : One α]
    [Std.Associative fun (x1 x2 : α) => x1 * x2] {xs : Vector α n} {x : α},
    (xs.push x).prod = xs.prod * x :=
  fun H => absurd (@H Nat 0 mulLeft _ mulLeft_assoc #v[] 0) (by decide +kernel)

-- `Vector.prod_reverse` (`[Associative]`): `mulNAC`, `xs = #v[0, 0, 2]` (`8 ≠ 4`).
example : ¬ ∀ {α : Type} {n : Nat} [inst : One α] [inst_1 : Mul α]
    [Std.Commutative fun (x1 x2 : α) => x1 * x2]
    [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 * x2) 1] (xs : Vector α n),
    xs.reverse.prod = xs.prod :=
  fun H => absurd (@H Nat 3 _ mulNAC mulNAC_comm mulNAC_lid #v[0, 0, 2]) (by decide +kernel)

-- `Vector.prod_reverse` (`[Commutative]`): `mulLI`, `xs = #v[0, 2]`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : One α] [inst_1 : Mul α]
    [Std.Associative fun (x1 x2 : α) => x1 * x2]
    [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 * x2) 1] (xs : Vector α n),
    xs.reverse.prod = xs.prod :=
  fun H => absurd (@H Nat 2 _ mulLI mulLI_assoc mulLI_lid #v[0, 2]) (by decide +kernel)

-- `Vector.sum_reverse` (`[Associative]`): `addNAC`, `xs = #v[1, 1, 2]` (`14 ≠ 12`).
example : ¬ ∀ {α : Type} {n : Nat} [inst : Zero α] [inst_1 : Add α]
    [Std.Commutative fun (x1 x2 : α) => x1 + x2]
    [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 + x2) 0] (xs : Vector α n),
    xs.reverse.sum = xs.sum :=
  fun H => absurd (@H Nat 3 _ addNAC addNAC_comm addNAC_lid #v[1, 1, 2]) (by decide +kernel)

-- `Vector.sum_reverse` (`[Commutative]`): `addLI`, `xs = #v[1, 2]`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Zero α] [inst_1 : Add α]
    [Std.Associative fun (x1 x2 : α) => x1 + x2]
    [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 + x2) 0] (xs : Vector α n),
    xs.reverse.sum = xs.sum :=
  fun H => absurd (@H Nat 2 _ addLI addLI_assoc addLI_lid #v[1, 2]) (by decide +kernel)

-- `Vector.sum_append` (`[Associative]`): `addNA`, `as₁ = #v[1, 1]`, `as₂ = #v[1]`.
example : ¬ ∀ {α : Type} {n m : Nat} [inst : Zero α] [inst_1 : Add α]
    [Std.LeftIdentity (fun (x1 x2 : α) => x1 + x2) 0]
    [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 + x2) 0] {as₁ : Vector α n} {as₂ : Vector α m},
    (as₁ ++ as₂).sum = as₁.sum + as₂.sum :=
  fun H => absurd (@H Nat 2 1 _ addNA ⟨⟩ addNA_id.toLawfulLeftIdentity #v[1, 1] #v[1])
    (by decide +kernel)

-- `Vector.sum_append` (`[LawfulLeftIdentity]`): left projection, `as₁ = #v[]`, `as₂ = #v[1]`.
example : ¬ ∀ {α : Type} {n m : Nat} [inst : Zero α] [inst_1 : Add α]
    [Std.Associative fun (x1 x2 : α) => x1 + x2] [Std.LeftIdentity (fun (x1 x2 : α) => x1 + x2) 0]
    {as₁ : Vector α n} {as₂ : Vector α m}, (as₁ ++ as₂).sum = as₁.sum + as₂.sum :=
  fun H => absurd (@H Nat 0 1 _ addLeft addLeft_assoc ⟨⟩ #v[] #v[1]) (by decide +kernel)

-- `Vector.prod_append` (`[Associative]`): `mulNA`, `as₁ = #v[2, 2]`, `as₂ = #v[2]`.
example : ¬ ∀ {α : Type} {n m : Nat} [inst : One α] [inst_1 : Mul α]
    [Std.LeftIdentity (fun (x1 x2 : α) => x1 * x2) 1]
    [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 * x2) 1] {as₁ : Vector α n} {as₂ : Vector α m},
    (as₁ ++ as₂).prod = as₁.prod * as₂.prod :=
  fun H => absurd (@H Nat 2 1 _ mulNA ⟨⟩ mulNA_id.toLawfulLeftIdentity #v[2, 2] #v[2])
    (by decide +kernel)

-- `Vector.prod_append` (`[LawfulLeftIdentity]`): left projection, `as₁ = #v[]`, `as₂ = #v[0]`.
example : ¬ ∀ {α : Type} {n m : Nat} [inst : One α] [inst_1 : Mul α]
    [Std.Associative fun (x1 x2 : α) => x1 * x2] [Std.LeftIdentity (fun (x1 x2 : α) => x1 * x2) 1]
    {as₁ : Vector α n} {as₂ : Vector α m}, (as₁ ++ as₂).prod = as₁.prod * as₂.prod :=
  fun H => absurd (@H Nat 0 1 _ mulLeft mulLeft_assoc ⟨⟩ #v[] #v[0]) (by decide +kernel)

-- `Vector.prod_singleton` (`[LawfulRightIdentity]`): right projection, `x = 0`.
example : ¬ ∀ {α : Type} [inst : Mul α] [inst_1 : One α] {x : α}, #v[x].prod = x :=
  fun H => absurd (@H Nat mulRight _ 0) (by decide +kernel)

-- `Vector.sum_singleton` (`[LawfulRightIdentity]`): right projection, `x = 1`.
example : ¬ ∀ {α : Type} [inst : Add α] [inst_1 : Zero α] {x : α}, #v[x].sum = x :=
  fun H => absurd (@H Nat addRight _ 1) (by decide +kernel)
