/-!
Hand resolution of the 153 instance hypotheses in `Init.Data.List.*` (Lemmas, Lex, MinMaxOn,
MinMaxIdx, MinMax, Erase, Find, Count, Perm, Pairwise, Basic, BasicAux, ToArray, Package; cluster
`OrderList`) that `HypCheck.lean` left unresolved. For each hypothesis `hᵢ` of theorem `T`, this file
proves `T'` (removable), `¬T'` (necessary), or, for a dependent hypothesis, `¬∀ indep, Hᵢ`.

Removable (47):
* `MinMaxOn`/`MinMaxIdx`, `[IsLinearPreorder β]` (20): the index scan `minIdxOn.go` and the fold
  `minOn` make the same comparison at every step for any `LE`, so `xs[minIdxOn f xs h] = minOn f xs h`
  (`getElem_minIdxOn`, `getElem_maxIdxOn`, `getElem_get_minIdxOn?`, `getElem_get_maxIdxOn?`); the
  kept index never decreases (`minIdxOn_take_le`, `maxIdxOn_take_le`, `left_le_minIdxOn_append`,
  `left_le_maxIdxOn_append`); `LawfulOrderLT` alone makes the scan switch to a position that is
  strictly below (above) all earlier ones (`le_minIdxOn_of_apply_getElem_lt_apply_getElem`, `le_max…`);
  `minOn f a a = a` (the six `…replicate…` lemmas); the fold keeps a head that is `≤` everything
  (`minOn_eq_head`, `maxOn_eq_head`); `maxOn?_eq_ite`/`maxOn?_eq_if` hold by definition.
* `max_map` and `max_map_eq_max` (`[IsLinearPreorder β]`): the left-leaning `max` laws give
  `f (maxOn f x y) = max (f x) (f y)` (resp. `f (max a b) = max (f a) (f b)` with `hf`) directly.
* `Lex`: `not_lt_of_cons_le_cons` and `le_of_cons_le_cons` need none of their instances (`Lex.rel`,
  `Lex.cons`); `map_le` needs neither `Asymm α` (derivable from `hf` and `Asymm β`) nor
  `Trichotomous β`: `map f l₂ < map f l₁ → l₂ < l₁` uses only `Trichotomous α` and `Asymm β`.
* `[LawfulBEq α]` (14): `Perm.count`, `Pairwise.erase`, `Nodup.erase`, `erase_eq_eraseIdx_of_idxOf`,
  `replace_replicate_ne`, `Perm.insert`, `length_le_length_insert`, `length_insert_pos`,
  `mem_insert_of_mem`, `insert_replicate_ne`, `count_erase_self`, `eq_or_mem_of_mem_insert`,
  `count_replicate`, `le_length_erase`: the functions involved test `==` in the same orientation, or
  the statement only uses that `insert`/`erase` return `l`, `a :: l` or a sublist.
* `sum_reverse`, `prod_reverse` (`LawfulLeftIdentity`): associativity and commutativity suffice;
  `foldl_max_eq_max`, `foldl_min_eq_min` (`IdempotentOp`): associativity suffices (`l ≠ []`).

Necessary (106): 25 dependent ones (`LawfulBEq α` used by a `Decidable (a ∈ l)` instance or a proof
in the statement, `MinEqOr`/`MaxEqOr` used by the subtype instances), refuted as `∀ α [BEq α],
LawfulBEq α` etc.; the other 81 by counterexamples with the models below, mostly lists of length
1 to 3.

Models (in `OrderListHand`, each a copy of `Nat` with its own instances):
* `Rps`: `a ≤ b ↔ b ≡ a ∨ b ≡ a + 1 (mod 3)`, reflexive and total, not transitive; with its lawful
  strict part as `<`. Refutes the `IsLinearPreorder β` lemmas with `xs = [0, 1, 2]` (max) or
  `[2, 1, 0]` (min), where the fold ends at the last element although the first is not below it.
* `Near`: `a ≤ b ↔ |a - b| ≤ 1`, reflexive, not transitive, not total (`…_le_of_apply_getElem_le_apply_getElem`).
* `LtF`: `<` empty (asymmetric, not trichotomous), usual `≤`/`compare`; `LtFT`: `<` empty, `≤` true,
  `compare` constantly `.eq` (lawful `<`, not antisymmetric); `OrdEq`: usual `≤`/`<`, `compare`
  constantly `.eq`; `LtLe`: `a < b ↔ a ≤ b` (reflexive).
* `BTrue`, `BFalse`: constant `BEq`; `BLe`: `a == b ↔ a ≤ b` (not symmetric; `List.replace` tests
  `a == x`, `Array.replace` tests `x == a`).
* `Mid`: `max`/`min` as rounded midpoint (idempotent, not associative); `Dist`: `|a - b|`
  (commutative, identity `0`, not associative); `Last`: last nonzero argument (associative, left
  identity, not commutative); `Shift`: usual addition with `0`/`1` := `1` (no identity); `LProj`:
  left projection (associative, no identity).

Run with the lean4 repo's stage1 binary: `lean checks/OrderListHand.lean`.
-/

set_option linter.unusedVariables false

universe u_1 u_2 u_3
open scoped Std.OppositeOrderInstances

namespace OrderListHand

/-! ## Models -/

/-- `Nat` with rock–paper–scissors `≤`: `a ≤ b ↔ b ≡ a ∨ b ≡ a + 1 (mod 3)`. Reflexive and total,
not transitive (`0 ≤ 1 ≤ 2`, `¬ 0 ≤ 2`); `<` is its lawful strict part (`a < b ↔ b ≡ a + 1`). -/
def Rps := Nat
instance : OfNat Rps n := ⟨(n : Nat)⟩
instance : DecidableEq Rps := inferInstanceAs (DecidableEq Nat)
def Rps.val (a : Rps) : Nat := a
instance : LE Rps := ⟨fun a b => b.val % 3 = a.val % 3 ∨ b.val % 3 = (a.val + 1) % 3⟩
instance : DecidableLE Rps := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
instance : LT Rps := ⟨fun a b => a ≤ b ∧ ¬ b ≤ a⟩
instance : DecidableLT Rps := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : Std.LawfulOrderLT Rps := ⟨fun _ _ => Iff.rfl⟩

/-- `Nat` with `a ≤ b ↔ |a - b| ≤ 1`: reflexive and symmetric, neither transitive nor total. -/
def Near := Nat
instance : OfNat Near n := ⟨(n : Nat)⟩
instance : DecidableEq Near := inferInstanceAs (DecidableEq Nat)
def Near.val (a : Near) : Nat := a
instance : LE Near := ⟨fun a b => a.val ≤ b.val + 1 ∧ b.val ≤ a.val + 1⟩
instance : DecidableLE Near := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- `Nat` with `<` empty and the usual `≤` and `compare`: `<` is irreflexive and asymmetric but
not trichotomous, and not the strict part of `≤` (`LawfulOrderLT` fails); `≤` is a linear order. -/
def LtF := Nat
instance : OfNat LtF n := ⟨(n : Nat)⟩
instance : DecidableEq LtF := inferInstanceAs (DecidableEq Nat)
def LtF.val (a : LtF) : Nat := a
instance : LT LtF := ⟨fun _ _ => False⟩
instance : DecidableLT LtF := fun _ _ => instDecidableFalse
instance : LE LtF := inferInstanceAs (LE Nat)
instance : DecidableLE LtF := inferInstanceAs (DecidableLE Nat)
instance : Ord LtF := inferInstanceAs (Ord Nat)
instance : Std.IsLinearOrder LtF := inferInstanceAs (Std.IsLinearOrder Nat)
instance : Std.LawfulOrderOrd LtF := inferInstanceAs (Std.LawfulOrderOrd Nat)
instance : Std.Asymm (α := LtF) (· < ·) := ⟨fun _ _ h => h.elim⟩
instance : Std.Irrefl (α := LtF) (· < ·) := ⟨fun _ h => h⟩

/-- `Nat` with `<` empty, `≤` everywhere true and `compare` constantly `.eq`: `LawfulOrderLT` and
`LawfulOrderOrd` hold, `≤` is a total preorder but not antisymmetric (`IsLinearOrder` fails). -/
def LtFT := Nat
instance : OfNat LtFT n := ⟨(n : Nat)⟩
instance : DecidableEq LtFT := inferInstanceAs (DecidableEq Nat)
instance : LT LtFT := ⟨fun _ _ => False⟩
instance : DecidableLT LtFT := fun _ _ => instDecidableFalse
instance : LE LtFT := ⟨fun _ _ => True⟩
instance : Ord LtFT := ⟨fun _ _ => .eq⟩
instance : Std.LawfulOrderLT LtFT := ⟨fun _ _ => by simp [LT.lt, LE.le]⟩
instance : Std.LawfulOrderOrd LtFT := ⟨fun _ _ => by simp [LE.le, compare], fun _ _ => by simp [LE.le, compare]⟩

/-- `Nat` with the usual `≤` and `<` but `compare` constantly `.eq` (`LawfulOrderOrd` fails). -/
def OrdEq := Nat
instance : OfNat OrdEq n := ⟨(n : Nat)⟩
instance : DecidableEq OrdEq := inferInstanceAs (DecidableEq Nat)
instance : LT OrdEq := inferInstanceAs (LT Nat)
instance : DecidableLT OrdEq := inferInstanceAs (DecidableLT Nat)
instance : LE OrdEq := inferInstanceAs (LE Nat)
instance : Ord OrdEq := ⟨fun _ _ => .eq⟩
instance : Std.IsLinearOrder OrdEq := inferInstanceAs (Std.IsLinearOrder Nat)
instance : Std.LawfulOrderLT OrdEq := inferInstanceAs (Std.LawfulOrderLT Nat)

/-- `Nat` with `a < b ↔ a ≤ b`: reflexive, so neither irreflexive nor asymmetric; trichotomous. -/
def LtLe := Nat
instance : OfNat LtLe n := ⟨(n : Nat)⟩
instance : DecidableEq LtLe := inferInstanceAs (DecidableEq Nat)
def LtLe.val (a : LtLe) : Nat := a
def LtLe.mk (n : Nat) : LtLe := n
instance : LT LtLe := ⟨fun a b => a.val ≤ b.val⟩
instance : DecidableLT LtLe := fun a b => Nat.decLe a.val b.val

/-- `BEq Nat` that is constantly `true`: an equivalence, not lawful. -/
def BTrue := Nat
instance : OfNat BTrue n := ⟨(n : Nat)⟩
instance : DecidableEq BTrue := inferInstanceAs (DecidableEq Nat)
instance : BEq BTrue := ⟨fun _ _ => true⟩

/-- `BEq Nat` that is constantly `false`: not reflexive. -/
def BFalse := Nat
instance : OfNat BFalse n := ⟨(n : Nat)⟩
instance : DecidableEq BFalse := inferInstanceAs (DecidableEq Nat)
instance : BEq BFalse := ⟨fun _ _ => false⟩

/-- `BEq Nat` with `a == b ↔ a ≤ b`: reflexive and transitive, not symmetric. -/
def BLe := Nat
instance : OfNat BLe n := ⟨(n : Nat)⟩
instance : DecidableEq BLe := inferInstanceAs (DecidableEq Nat)
def BLe.val (a : BLe) : Nat := a
instance : BEq BLe := ⟨fun a b => decide (a.val ≤ b.val)⟩

/-- `Max`/`Min` on `Nat` as the rounded-down midpoint: idempotent and commutative, not associative
(`max (max 0 0) 4 = 2`, `max 0 (max 0 4) = 1`). -/
def Mid := Nat
instance : OfNat Mid n := ⟨(n : Nat)⟩
instance : DecidableEq Mid := inferInstanceAs (DecidableEq Nat)
def Mid.val (a : Mid) : Nat := a
instance : Max Mid := ⟨fun a b => ((a.val + b.val) / 2 : Nat)⟩
instance : Min Mid := ⟨fun a b => ((a.val + b.val) / 2 : Nat)⟩
instance : Std.IdempotentOp (max : Mid → Mid → Mid) := ⟨fun a => by
  show ((a.val + a.val) / 2 : Nat) = a.val; omega⟩
instance : Std.IdempotentOp (min : Mid → Mid → Mid) := ⟨fun a => by
  show ((a.val + a.val) / 2 : Nat) = a.val; omega⟩

/-- `+`/`*` on `Nat` as the distance `|a - b|`, with `0`/`1` both `0`: commutative with two-sided
identity `0`, not associative (`(1 ⊕ 2) ⊕ 3 = 2`, `1 ⊕ (2 ⊕ 3) = 0`). -/
def Dist := Nat
def Dist.mk (n : Nat) : Dist := n
instance : DecidableEq Dist := inferInstanceAs (DecidableEq Nat)
def Dist.val (a : Dist) : Nat := a
def Dist.op (a b : Dist) : Dist := (a.val - b.val + (b.val - a.val) : Nat)
instance : Add Dist := ⟨Dist.op⟩
instance : Mul Dist := ⟨Dist.op⟩
instance : Zero Dist := ⟨(0 : Nat)⟩
instance : One Dist := ⟨(0 : Nat)⟩
instance : Std.Commutative (fun x y : Dist => x + y) := ⟨fun a b => by
  show (a.val - b.val + (b.val - a.val) : Nat) = (b.val - a.val + (a.val - b.val) : Nat); omega⟩
instance : Std.Commutative (fun x y : Dist => x * y) := ⟨fun a b => by
  show (a.val - b.val + (b.val - a.val) : Nat) = (b.val - a.val + (a.val - b.val) : Nat); omega⟩
instance : Std.LeftIdentity (fun x y : Dist => x + y) 0 := ⟨⟩
instance : Std.LeftIdentity (fun x y : Dist => x * y) 1 := ⟨⟩
instance : Std.RightIdentity (fun x y : Dist => x + y) 0 := ⟨⟩
instance : Std.RightIdentity (fun x y : Dist => x * y) 1 := ⟨⟩
instance : Std.Identity (fun x y : Dist => x + y) 0 := ⟨⟩
instance : Std.Identity (fun x y : Dist => x * y) 1 := ⟨⟩
instance : Std.LawfulIdentity (fun x y : Dist => x + y) 0 where
  left_id a := by show (0 - a.val + (a.val - 0) : Nat) = a.val; omega
  right_id a := by show (a.val - 0 + (0 - a.val) : Nat) = a.val; omega
instance : Std.LawfulIdentity (fun x y : Dist => x * y) 1 where
  left_id a := by show (0 - a.val + (a.val - 0) : Nat) = a.val; omega
  right_id a := by show (a.val - 0 + (0 - a.val) : Nat) = a.val; omega

/-- `+`/`*` on `Nat` as "last nonzero argument" (`a ⊕ b = if b = 0 then a else b`), with `0`/`1`
both `0`: associative with two-sided identity `0`, not commutative. -/
def Last := Nat
def Last.mk (n : Nat) : Last := n
instance : DecidableEq Last := inferInstanceAs (DecidableEq Nat)
def Last.val (a : Last) : Nat := a
def Last.op (a b : Last) : Last := if b.val = 0 then a else b
instance : Add Last := ⟨Last.op⟩
instance : Mul Last := ⟨Last.op⟩
instance : Zero Last := ⟨(0 : Nat)⟩
instance : One Last := ⟨(0 : Nat)⟩
theorem Last.op_assoc (a b c : Last) : Last.op (Last.op a b) c = Last.op a (Last.op b c) := by
  unfold Last.op; by_cases hc : c.val = 0 <;> by_cases hb : b.val = 0 <;> simp_all
theorem Last.op_left_id (a : Last) : Last.op (Last.mk 0) a = a := by
  unfold Last.op; by_cases ha : a.val = 0 <;> simp_all <;> exact ha.symm
instance : Std.Associative (fun x y : Last => x + y) := ⟨Last.op_assoc⟩
instance : Std.Associative (fun x y : Last => x * y) := ⟨Last.op_assoc⟩
instance : Std.LeftIdentity (fun x y : Last => x + y) 0 := ⟨⟩
instance : Std.LeftIdentity (fun x y : Last => x * y) 1 := ⟨⟩
instance : Std.LawfulLeftIdentity (fun x y : Last => x + y) 0 := ⟨Last.op_left_id⟩
instance : Std.LawfulLeftIdentity (fun x y : Last => x * y) 1 := ⟨Last.op_left_id⟩

/-- `+` and `*` both the usual addition on `Nat`, with `0`/`1` both `1`: associative and commutative,
without identity. -/
def Shift := Nat
def Shift.mk (n : Nat) : Shift := n
instance : DecidableEq Shift := inferInstanceAs (DecidableEq Nat)
instance : Add Shift := inferInstanceAs (Add Nat)
instance : Mul Shift := ⟨fun a b => (a : Nat) + (b : Nat)⟩
instance : Zero Shift := ⟨(1 : Nat)⟩
instance : One Shift := ⟨(1 : Nat)⟩
instance : Std.Associative (fun x y : Shift => x + y) := ⟨Nat.add_assoc⟩
instance : Std.Associative (fun x y : Shift => x * y) := ⟨Nat.add_assoc⟩
instance : Std.Commutative (fun x y : Shift => x + y) := ⟨Nat.add_comm⟩
instance : Std.Commutative (fun x y : Shift => x * y) := ⟨Nat.add_comm⟩

/-- `+`/`*` on `Nat` as left projection (`a ⊕ b = a`), `0`/`1` both `0`: associative, `0` is not an
identity. -/
def LProj := Nat
def LProj.mk (n : Nat) : LProj := n
instance : DecidableEq LProj := inferInstanceAs (DecidableEq Nat)
instance : Add LProj := ⟨fun a _ => a⟩
instance : Mul LProj := ⟨fun a _ => a⟩
instance : Zero LProj := ⟨(0 : Nat)⟩
instance : One LProj := ⟨(0 : Nat)⟩
instance : Std.Associative (fun x y : LProj => x + y) := ⟨fun _ _ _ => rfl⟩
instance : Std.Associative (fun x y : LProj => x * y) := ⟨fun _ _ _ => rfl⟩

end OrderListHand
open OrderListHand


/-! ## Dependent hypotheses (necessary: `∀ indep, Hᵢ` fails) -/


-- `List.getElem_replace` (`inst`, idx 4): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem getElem_replace_h4 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.getElem?_insert` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem getElemQ_insert_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.getElem?_insert_succ` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem getElemQ_insert_succ_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.idxOf_append` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem idxOf_append_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.head?_insert` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem headQ_insert_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.insert_append` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem insert_append_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.decide_mem_cons` (`inst`, idx 4): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem decide_mem_cons_h4 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.finIdxOf?_eq_pmap_idxOf?` (`inst`, idx 4): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem finIdxOfQ_eq_pmap_idxOfQ_h4 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.erase_append` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem erase_append_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.head_insert` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem head_insert_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.getElem?_replace` (`inst`, idx 4): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem getElemQ_replace_h4 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.Nodup.count` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem Nodup_count_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.replace_append` (`inst`, idx 4): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem replace_append_h4 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.getElem?_insert_zero` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem getElemQ_insert_zero_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.length_insert` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem length_insert_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.nodup_iff_count_eq_ite` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem nodup_iff_count_eq_ite_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.getElem_insert` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem getElem_insert_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.contains_eq_mem` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem contains_eq_mem_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.elem_eq_mem` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem elem_eq_mem_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.length_erase` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem length_erase_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.insert_eq` (`inst`, idx 2): dependent (the conclusion uses it, through a Decidable (a ∈ l) instance or a proof term); ∀ α [BEq α], LawfulBEq α fails for the constant-true BEq
theorem insert_eq_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq α) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := (0 : BTrue)) (b := 1) rfl) (by decide)

-- `List.min?_eq_some_iff_subtype` (`inst`, idx 5): dependent; ∀ α [Min α], MinEqOr α fails for the midpoint min (min 0 4 = 2)
theorem minQ_eq_some_iff_subtype_h5 :
    ¬ (∀ {α : Type} [inst : Min α], Std.MinEqOr α) :=
  fun h => by
    have := (@h Mid _).min_eq_or 0 4
    revert this; decide

-- `List.min?_eq_min?_attach` (`inst`, idx 2): dependent; ∀ α [Min α], MinEqOr α fails for the midpoint min (min 0 4 = 2)
theorem minQ_eq_minQ_attach_h2 :
    ¬ (∀ {α : Type} [inst : Min α], Std.MinEqOr α) :=
  fun h => by
    have := (@h Mid _).min_eq_or 0 4
    revert this; decide

-- `List.max?_eq_some_iff_subtype` (`inst`, idx 5): dependent; ∀ α [Max α], MaxEqOr α fails for the midpoint max (max 0 4 = 2)
theorem maxQ_eq_some_iff_subtype_h5 :
    ¬ (∀ {α : Type} [inst : Max α], Std.MaxEqOr α) :=
  fun h => by
    have := (@h Mid _).max_eq_or 0 4
    revert this; decide

-- `List.max?_eq_max?_attach` (`inst`, idx 2): dependent; ∀ α [Max α], MaxEqOr α fails for the midpoint max (max 0 4 = 2)
theorem maxQ_eq_maxQ_attach_h2 :
    ¬ (∀ {α : Type} [inst : Max α], Std.MaxEqOr α) :=
  fun h => by
    have := (@h Mid _).max_eq_or 0 4
    revert this; decide


/-! ## `MinMaxOn`/`MinMaxIdx`: necessary -/


-- `List.apply_maxOn_lt_apply_getElem_of_lt_maxIdxOn` (`inst`, idx 5): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [0, 1, 2], k = 0: maxIdxOn = 2 but ¬ 0 < 2
theorem apply_maxOn_lt_apply_getElem_of_lt_maxIdxOn_h5 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [Std.LawfulOrderLT β] {f : α → β}
        {xs : List α} (h : xs ≠ []) {k : Nat} (hk : k < List.maxIdxOn f xs h),
        f (xs[k]'(Nat.lt_trans hk (List.maxIdxOn_lt_length h))) < f (List.maxOn f xs h)) :=
  fun h => by
    have := h (β := Rps) (f := id) (xs := [(0 : Rps), 1, 2]) (by simp) (k := 0) (by decide)
    revert this; decide

-- `List.apply_minOn_lt_apply_getElem_of_lt_minIdxOn` (`inst`, idx 5): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [2, 1, 0], k = 0: minIdxOn = 2 but ¬ 0 < 2
theorem apply_minOn_lt_apply_getElem_of_lt_minIdxOn_h5 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [Std.LawfulOrderLT β] {f : α → β}
        {xs : List α} (h : xs ≠ []) {k : Nat} (hk : k < List.minIdxOn f xs h),
        f (List.minOn f xs h) < f (xs[k]'(Nat.lt_trans hk (List.minIdxOn_lt_length h)))) :=
  fun h => by
    have := h (β := Rps) (f := id) (xs := [(2 : Rps), 1, 0]) (by simp) (k := 0) (by decide)
    revert this; decide

-- `List.maxIdxOn_append` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [0], ys = [1, 2], f = id
theorem maxIdxOn_append_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs ys : List α} {f : α → β} (hxs : xs ≠ [])
        (hys : ys ≠ []),
        List.maxIdxOn f (xs ++ ys) (List.minIdxOn_append._proof_1 hxs) =
          if f (List.maxOn f ys hys) ≤ f (List.maxOn f xs hxs) then List.maxIdxOn f xs hxs
          else xs.length + List.maxIdxOn f ys hys) :=
  fun h => by
    have := h (β := Rps) (xs := [(0 : Rps)]) (ys := [1, 2]) (f := id) (by simp) (by simp)
    revert this; decide

-- `List.minIdxOn_append` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [0], ys = [2, 1], f = id
theorem minIdxOn_append_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs ys : List α} {f : α → β} (hxs : xs ≠ [])
        (hys : ys ≠ []),
        List.minIdxOn f (xs ++ ys) (List.minIdxOn_append._proof_1 hxs) =
          if f (List.minOn f xs hxs) ≤ f (List.minOn f ys hys) then List.minIdxOn f xs hxs
          else xs.length + List.minIdxOn f ys hys) :=
  fun h => by
    have := h (β := Rps) (xs := [(0 : Rps)]) (ys := [2, 1]) (f := id) (by simp) (by simp)
    revert this; decide

-- `List.maxOn_append` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [0], ys = [1, 2], f = id
theorem maxOn_append_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs ys : List α} {f : α → β} (hxs : xs ≠ [])
        (hys : ys ≠ []),
        List.maxOn f (xs ++ ys) (List.minOn_append._proof_1 hxs) = maxOn f (List.maxOn f xs hxs) (List.maxOn f ys hys)) :=
  fun h => by
    have := h (β := Rps) (xs := [(0 : Rps)]) (ys := [1, 2]) (f := id) (by simp) (by simp)
    revert this; decide

-- `List.minOn_append` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [0], ys = [2, 1], f = id
theorem minOn_append_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs ys : List α} {f : α → β} (hxs : xs ≠ [])
        (hys : ys ≠ []),
        List.minOn f (xs ++ ys) (List.minOn_append._proof_1 hxs) = minOn f (List.minOn f xs hxs) (List.minOn f ys hys)) :=
  fun h => by
    have := h (β := Rps) (xs := [(0 : Rps)]) (ys := [2, 1]) (f := id) (by simp) (by simp)
    revert this; decide

-- `List.maxOn?_append` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [0], ys = [1, 2], f = id
theorem maxOnQ_append_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] (xs ys : List α) (f : α → β),
        List.maxOn? f (xs ++ ys) = Option.merge (maxOn f) (List.maxOn? f xs) (List.maxOn? f ys)) :=
  fun h => by
    have := h (β := Rps) [(0 : Rps)] [1, 2] id
    revert this; decide

-- `List.minOn?_append` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [0], ys = [2, 1], f = id
theorem minOnQ_append_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] (xs ys : List α) (f : α → β),
        List.minOn? f (xs ++ ys) = Option.merge (minOn f) (List.minOn? f xs) (List.minOn? f ys)) :=
  fun h => by
    have := h (β := Rps) [(0 : Rps)] [2, 1] id
    revert this; decide

-- `List.apply_minOn_le_iff` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [2, 1, 0], b = 2
theorem apply_minOn_le_iff_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs : List α} {f : α → β} (h : xs ≠ []) {b : β},
        f (List.minOn f xs h) ≤ b ↔ ∃ (x : α), x ∈ xs ∧ f x ≤ b) :=
  fun h => by
    have := h (β := Rps) (xs := [(2 : Rps), 1, 0]) (f := id) (by simp) (b := 2)
    revert this; decide

-- `List.le_apply_maxOn_iff` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [0, 1, 2], b = 0
theorem le_apply_maxOn_iff_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs : List α} {f : α → β} (h : xs ≠ []) {b : β},
        b ≤ f (List.maxOn f xs h) ↔ ∃ (x : α), x ∈ xs ∧ b ≤ f x) :=
  fun h => by
    have := h (β := Rps) (xs := [(0 : Rps), 1, 2]) (f := id) (by simp) (b := 0)
    revert this; decide

-- `List.apply_minOn_lt_iff` (`inst`, idx 5): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [2, 1, 0], b = 0
theorem apply_minOn_lt_iff_h5 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [Std.LawfulOrderLT β]
        {xs : List α} {f : α → β} (h : xs ≠ []) {b : β}, f (List.minOn f xs h) < b ↔ ∃ (x : α), x ∈ xs ∧ f x < b) :=
  fun h => by
    have := h (β := Rps) (xs := [(2 : Rps), 1, 0]) (f := id) (by simp) (b := 0)
    revert this; decide

-- `List.lt_apply_minOn_iff` (`inst`, idx 5): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [2, 1, 0], b = 2
theorem lt_apply_minOn_iff_h5 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [Std.LawfulOrderLT β]
        {xs : List α} {f : α → β} (h : xs ≠ []) {b : β}, b < f (List.minOn f xs h) ↔ ∀ (x : α), x ∈ xs → b < f x) :=
  fun h => by
    have := h (β := Rps) (xs := [(2 : Rps), 1, 0]) (f := id) (by simp) (b := 2)
    revert this; decide

-- `List.lt_apply_maxOn_iff` (`inst`, idx 5): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [0, 1, 2], b = 0
theorem lt_apply_maxOn_iff_h5 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [Std.LawfulOrderLT β]
        {xs : List α} {f : α → β} (h : xs ≠ []) {b : β}, b < f (List.maxOn f xs h) ↔ ∃ (x : α), x ∈ xs ∧ b < f x) :=
  fun h => by
    have := h (β := Rps) (xs := [(0 : Rps), 1, 2]) (f := id) (by simp) (b := 0)
    revert this; decide

-- `List.apply_maxOn_lt_iff` (`inst`, idx 5): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [0, 1, 2], b = 0
theorem apply_maxOn_lt_iff_h5 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [Std.LawfulOrderLT β]
        {xs : List α} {f : α → β} (h : xs ≠ []) {b : β}, f (List.maxOn f xs h) < b ↔ ∀ (x : α), x ∈ xs → f x < b) :=
  fun h => by
    have := h (β := Rps) (xs := [(0 : Rps), 1, 2]) (f := id) (by simp) (b := 0)
    revert this; decide

-- `List.minIdxOn_eq_iff_eq_minOn` (`inst`, idx 5): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [2, 1, 0], i = 2
theorem minIdxOn_eq_iff_eq_minOn_h5 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [Std.LawfulOrderLT β] {f : α → β}
        {xs : List α} (h : xs ≠ []) {i : Nat},
        List.minIdxOn f xs h = i ↔
          ∃ (hi : i < xs.length), xs[i] = List.minOn f xs h ∧ ∀ (j : Nat) (hj : j < i), f (List.minOn f xs h) < f xs[j]) :=
  fun h => by
    have := h (β := Rps) (f := id) (xs := [(2 : Rps), 1, 0]) (by simp) (i := 2)
    revert this; decide

-- `List.maxIdxOn_eq_iff_eq_maxOn` (`inst`, idx 5): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [0, 1, 2], i = 2
theorem maxIdxOn_eq_iff_eq_maxOn_h5 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [Std.LawfulOrderLT β] {f : α → β}
        {xs : List α} (h : xs ≠ []) {i : Nat},
        List.maxIdxOn f xs h = i ↔
          ∃ (hi : i < xs.length), xs[i] = List.maxOn f xs h ∧ ∀ (j : Nat) (hj : j < i), f xs[j] < f (List.maxOn f xs h)) :=
  fun h => by
    have := h (β := Rps) (f := id) (xs := [(0 : Rps), 1, 2]) (by simp) (i := 2)
    revert this; decide

-- `List.minIdxOn_eq_iff` (`inst`, idx 5): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [2, 1, 0], i = 2
theorem minIdxOn_eq_iff_h5 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [Std.LawfulOrderLT β] {f : α → β}
        {xs : List α} (h : xs ≠ []) {i : Nat},
        List.minIdxOn f xs h = i ↔
          ∃ (h : i < xs.length),
            (∀ (j : Nat) (x : j < xs.length), f xs[i] ≤ f xs[j]) ∧ ∀ (j : Nat) (x : j < i), f xs[i] < f xs[j]) :=
  fun h => by
    have := h (β := Rps) (f := id) (xs := [(2 : Rps), 1, 0]) (by simp) (i := 2)
    revert this; decide

-- `List.maxIdxOn_eq_iff` (`inst`, idx 5): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [0, 1, 2], i = 2
theorem maxIdxOn_eq_iff_h5 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [Std.LawfulOrderLT β] {f : α → β}
        {xs : List α} (h : xs ≠ []) {i : Nat},
        List.maxIdxOn f xs h = i ↔
          ∃ (h : i < xs.length),
            (∀ (j : Nat) (x : j < xs.length), f xs[j] ≤ f xs[i]) ∧ ∀ (j : Nat) (x : j < i), f xs[j] < f xs[i]) :=
  fun h => by
    have := h (β := Rps) (f := id) (xs := [(0 : Rps), 1, 2]) (by simp) (i := 2)
    revert this; decide

-- `List.minIdxOn_le_of_apply_getElem_le_apply_getElem` (`inst`, idx 4): a ≤ b ↔ |a - b| ≤ 1 (Near, reflexive, not transitive, not total), xs = [0, 1, 2], i = 1: minIdxOn = 2
theorem minIdxOn_le_of_apply_getElem_le_apply_getElem_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) {i : Nat}
        (hi : i < xs.length), (∀ (j : Nat) (x : j < xs.length), f xs[i] ≤ f xs[j]) → List.minIdxOn f xs h ≤ i) :=
  fun h => by
    have := h (β := Near) (f := id) (xs := [(0 : Near), 1, 2]) (by simp) (i := 1) (by decide) (by decide)
    revert this; decide

-- `List.maxIdxOn_le_of_apply_getElem_le_apply_getElem` (`inst`, idx 4): a ≤ b ↔ |a - b| ≤ 1 (Near, reflexive, not transitive, not total), xs = [0, 1, 2], i = 1: maxIdxOn = 2
theorem maxIdxOn_le_of_apply_getElem_le_apply_getElem_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) {i : Nat}
        (hi : i < xs.length), (∀ (j : Nat) (x : j < xs.length), f xs[j] ≤ f xs[i]) → List.maxIdxOn f xs h ≤ i) :=
  fun h => by
    have := h (β := Near) (f := id) (xs := [(0 : Near), 1, 2]) (by simp) (i := 1) (by decide) (by decide)
    revert this; decide

-- `List.maxIdxOn_le_of_apply_getElem_le_apply_maxOn` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [0, 1, 2], k = 0
theorem maxIdxOn_le_of_apply_getElem_le_apply_maxOn_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) {k : Nat}
        (hi : k < xs.length), f (List.maxOn f xs h) ≤ f xs[k] → List.maxIdxOn f xs h ≤ k) :=
  fun h => by
    have := h (β := Rps) (f := id) (xs := [(0 : Rps), 1, 2]) (by simp) (k := 0) (by decide) (by decide)
    revert this; decide

-- `List.minIdxOn_le_of_apply_getElem_le_apply_minOn` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), xs = [2, 1, 0], k = 0
theorem minIdxOn_le_of_apply_getElem_le_apply_minOn_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []) {k : Nat}
        (hi : k < xs.length), f xs[k] ≤ f (List.minOn f xs h) → List.minIdxOn f xs h ≤ k) :=
  fun h => by
    have := h (β := Rps) (f := id) (xs := [(2 : Rps), 1, 0]) (by simp) (k := 0) (by decide) (by decide)
    revert this; decide

-- `List.maxIdxOn_cons` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), x = 0, xs = [2, 1]
theorem maxIdxOn_cons_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {x : α} {xs : List α} {f : α → β},
        List.maxIdxOn f (x :: xs) List.minIdxOn_cons._proof_1 =
          if h : xs = [] then 0 else if f (List.maxOn f xs h) ≤ f x then 0 else List.maxIdxOn f xs h + 1) :=
  fun h => by
    have := h (β := Rps) (x := (0 : Rps)) (xs := [2, 1]) (f := id)
    revert this; decide

-- `List.maxIdxOn?_cons` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), x = 0, xs = [2, 1]
theorem maxIdxOnQ_cons_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {x : α} {xs : List α},
        List.maxIdxOn? f (x :: xs) =
          Option.some (if h : xs = [] then 0 else if f (List.maxOn f xs h) ≤ f x then 0 else List.maxIdxOn f xs h + 1)) :=
  fun h => by
    have := h (β := Rps) (x := (0 : Rps)) (xs := [2, 1]) (f := id)
    revert this; decide

-- `List.maxOn_cons` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), x = 0, xs = [2, 1]
theorem maxOn_cons_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {x : α} {xs : List α} {f : α → β},
        List.maxOn f (x :: xs) List.minOn_cons._proof_1 = if h : xs = [] then x else maxOn f x (List.maxOn f xs h)) :=
  fun h => by
    have := h (β := Rps) (x := (0 : Rps)) (xs := [2, 1]) (f := id)
    revert this; decide

-- `List.maxOn?_cons` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), x = 0, xs = [2, 1]
theorem maxOnQ_cons_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {x : α} {xs : List α},
        List.maxOn? f (x :: xs) = Option.some ((List.maxOn? f xs).elim x (maxOn f x))) :=
  fun h => by
    have := h (β := Rps) (x := (0 : Rps)) (xs := [2, 1]) (f := id)
    revert this; decide

-- `List.minIdxOn_cons` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), x = 0, xs = [1, 2]
theorem minIdxOn_cons_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {x : α} {xs : List α} {f : α → β},
        List.minIdxOn f (x :: xs) List.minIdxOn_cons._proof_1 =
          if h : xs = [] then 0 else if f x ≤ f (List.minOn f xs h) then 0 else List.minIdxOn f xs h + 1) :=
  fun h => by
    have := h (β := Rps) (x := (0 : Rps)) (xs := [1, 2]) (f := id)
    revert this; decide

-- `List.minIdxOn?_cons` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), x = 0, xs = [1, 2]
theorem minIdxOnQ_cons_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {x : α} {xs : List α},
        List.minIdxOn? f (x :: xs) =
          Option.some (if h : xs = [] then 0 else if f x ≤ f (List.minOn f xs h) then 0 else List.minIdxOn f xs h + 1)) :=
  fun h => by
    have := h (β := Rps) (x := (0 : Rps)) (xs := [1, 2]) (f := id)
    revert this; decide

-- `List.minOn_cons` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), x = 0, xs = [1, 2]
theorem minOn_cons_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {x : α} {xs : List α} {f : α → β},
        List.minOn f (x :: xs) List.minOn_cons._proof_1 = if h : xs = [] then x else minOn f x (List.minOn f xs h)) :=
  fun h => by
    have := h (β := Rps) (x := (0 : Rps)) (xs := [1, 2]) (f := id)
    revert this; decide

-- `List.minOn?_cons` (`inst`, idx 4): rock-paper-scissors ≤ on Nat (Rps, reflexive and total, not transitive), x = 0, xs = [1, 2]
theorem minOnQ_cons_h4 :
    ¬ (∀ {β : Type} {α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {x : α} {xs : List α},
        List.minOn? f (x :: xs) = Option.some ((List.minOn? f xs).elim x (minOn f x))) :=
  fun h => by
    have := h (β := Rps) (x := (0 : Rps)) (xs := [1, 2]) (f := id)
    revert this; decide

-- `List.min_map_eq_min` (`inst`, idx 5): Min α := max on Nat (usual ≤), β = Nat, f = id, l = [0, 1]
theorem min_map_eq_min_h5 :
    ¬ (∀ {α : Type} {β : Type} [inst : Min α] [inst_1 : LE α] [DecidableLE α] [inst_3 : Min β] [inst_4 : LE β]
        [DecidableLE β] [Std.IsLinearPreorder β] [Std.LawfulOrderLeftLeaningMin β] {f : α → β},
        (∀ (a b : α), f a ≤ f b ↔ a ≤ b) →
          ∀ {l : List α} {h : l ≠ []}, (List.map f l).min (by simpa using h) = f (l.min h)) :=
  fun h => by
    have := h (α := Nat) (β := Nat) (inst := ⟨max⟩) (f := id) (fun _ _ => Iff.rfl) (l := [0, 1]) (h := by simp)
    revert this; decide


/-! ## `Lex`: necessary -/


-- `List.map_le_map_iff` (`inst`, idx 3): < empty on Nat (LtF, asymmetric, not trichotomous) to the usual Nat, f = val, l₁ = [1], l₂ = [0]
theorem map_le_map_iff_h3 :
    ¬ (∀ {α : Type} {β : Type} [inst : LT α] [inst_1 : LT β] [Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → β),
        (∀ (a b : α), a < b → f a < f b) → ∀ {l₁ l₂ : List α}, List.map f l₁ ≤ List.map f l₂ ↔ l₁ ≤ l₂) :=
  fun h => by
    have := h (α := LtF) (β := Nat) LtF.val (fun _ _ (h : False) => h.elim) (l₁ := [1]) (l₂ := [0])
    revert this; decide

-- `List.map_lt_map_iff` (`inst`, idx 3): < empty on Nat (LtF, asymmetric, not trichotomous) to the usual Nat, f = val, l₁ = [0], l₂ = [1]
theorem map_lt_map_iff_h3 :
    ¬ (∀ {α : Type} {β : Type} [inst : LT α] [inst_1 : LT β] [Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → β),
        (∀ (a b : α), a < b → f a < f b) → ∀ {l₁ l₂ : List α}, List.map f l₁ < List.map f l₂ ↔ l₁ < l₂) :=
  fun h => by
    have := h (α := LtF) (β := Nat) LtF.val (fun _ _ (h : False) => h.elim) (l₁ := [0]) (l₂ := [1])
    revert this; decide

-- `List.flatMap_le_flatMap_iff` (`inst`, idx 3): < empty on Nat (LtF, asymmetric, not trichotomous) to the usual Nat, f a = [a], l₁ = [1], l₂ = [0]
theorem flatMap_le_flatMap_iff_h3 :
    ¬ (∀ {α : Type} {β : Type} [inst : LT α] [inst_1 : LT β] [Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → List β),
        (∀ (a b : α), a < b → f a < f b) →
          (∀ (a b : α), f a <+: f b → a = b) →
            (∀ (a : α), f a ≠ []) → ∀ {l₁ l₂ : List α}, List.flatMap f l₁ ≤ List.flatMap f l₂ ↔ l₁ ≤ l₂) :=
  fun h => by
    have := h (α := LtF) (β := Nat) (fun a => [a.val]) (fun _ _ (h : False) => h.elim) (fun (a b : LtF) (h : [a.val] <+: [b.val]) => by have := h.eq_of_length (by simp); simp at this; exact this) (fun _ => List.cons_ne_nil _ _) (l₁ := [1]) (l₂ := [0])
    revert this; decide

-- `List.flatMap_lt_flatMap_iff` (`inst`, idx 3): < empty on Nat (LtF, asymmetric, not trichotomous) to the usual Nat, f a = [a], l₁ = [0], l₂ = [1]
theorem flatMap_lt_flatMap_iff_h3 :
    ¬ (∀ {α : Type} {β : Type} [inst : LT α] [inst_1 : LT β] [Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → List β),
        (∀ (a b : α), a < b → f a < f b) →
          (∀ (a b : α), f a <+: f b → a = b) →
            (∀ (a : α), f a ≠ []) → ∀ {l₁ l₂ : List α}, List.flatMap f l₁ < List.flatMap f l₂ ↔ l₁ < l₂) :=
  fun h => by
    have := h (α := LtF) (β := Nat) (fun a => [a.val]) (fun _ _ (h : False) => h.elim) (fun (a b : LtF) (h : [a.val] <+: [b.val]) => by have := h.eq_of_length (by simp); simp at this; exact this) (fun _ => List.cons_ne_nil _ _) (l₁ := [0]) (l₂ := [1])
    revert this; decide

-- `List.flatMap_le_flatMap_iff` (`inst`, idx 5): usual Nat to a < b ↔ a ≤ b on Nat (LtLe, reflexive), f a = [a], l₁ = l₂ = [0]
theorem flatMap_le_flatMap_iff_h5 :
    ¬ (∀ {α : Type} {β : Type} [inst : LT α] [Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
        (f : α → List β),
        (∀ (a b : α), a < b → f a < f b) →
          (∀ (a b : α), f a <+: f b → a = b) →
            (∀ (a : α), f a ≠ []) → ∀ {l₁ l₂ : List α}, List.flatMap f l₁ ≤ List.flatMap f l₂ ↔ l₁ ≤ l₂) :=
  fun h => by
    have := h (α := Nat) (β := LtLe) (fun a => [LtLe.mk a]) (fun _ _ h => List.Lex.rel (Nat.le_of_lt h)) (fun (a b : Nat) (h : [LtLe.mk a] <+: [LtLe.mk b]) => by have := h.eq_of_length (by simp); simp at this; exact this) (fun _ => List.cons_ne_nil _ _) (l₁ := [0]) (l₂ := [0])
    revert this; decide

-- `List.flatMap_lt_flatMap_iff` (`inst`, idx 5): usual Nat to a < b ↔ a ≤ b on Nat (LtLe, reflexive), f a = [a], l₁ = l₂ = [0]
theorem flatMap_lt_flatMap_iff_h5 :
    ¬ (∀ {α : Type} {β : Type} [inst : LT α] [Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
        (f : α → List β),
        (∀ (a b : α), a < b → f a < f b) →
          (∀ (a b : α), f a <+: f b → a = b) →
            (∀ (a : α), f a ≠ []) → ∀ {l₁ l₂ : List α}, List.flatMap f l₁ < List.flatMap f l₂ ↔ l₁ < l₂) :=
  fun h => by
    have := h (α := Nat) (β := LtLe) (fun a => [LtLe.mk a]) (fun _ _ h => List.Lex.rel (Nat.le_of_lt h)) (fun (a b : Nat) (h : [LtLe.mk a] <+: [LtLe.mk b]) => by have := h.eq_of_length (by simp); simp at this; exact this) (fun _ => List.cons_ne_nil _ _) (l₁ := [0]) (l₂ := [0])
    revert this; decide

-- `List.map_le` (`inst`, idx 5): < empty on Nat (LtF, asymmetric, not trichotomous) to the usual Nat, f = val, l₁ = [1], l₂ = [0]
theorem map_le_h5 :
    ¬ (∀ {α : Type} {β : Type} [inst : LT α] [inst_1 : LT β] [Std.Asymm fun (x1 x2 : α) => x1 < x2]
        [Std.Asymm fun (x1 x2 : β) => x1 < x2] [Std.Trichotomous fun (x1 x2 : β) => x1 < x2] {l₁ l₂ : List α} {f : α → β},
        (∀ (x y : α), x < y → f x < f y) → l₁ ≤ l₂ → List.map f l₁ ≤ List.map f l₂) :=
  fun h => by
    have := h (α := LtF) (β := Nat) (l₁ := [1]) (l₂ := [0]) (f := LtF.val) (fun _ _ (h : False) => h.elim) (by decide)
    revert this; decide

-- `List.append_le_append_iff_of_length_eq` (`inst`, idx 3): < empty on Nat (LtF, asymmetric, not trichotomous), l₁ = [0], l₂ = [1], l₃ = l₄ = []
theorem append_le_append_iff_of_length_eq_h3 :
    ¬ (∀ {α : Type} [inst : LT α] [Std.Asymm fun (x1 x2 : α) => x1 < x2] {l₁ l₂ l₃ l₄ : List α},
        l₁.length = l₂.length → (l₁ ++ l₃ ≤ l₂ ++ l₄ ↔ l₁ < l₂ ∨ l₁ = l₂ ∧ l₃ ≤ l₄)) :=
  fun h => by
    have := h (α := LtF) (l₁ := [0]) (l₂ := [1]) (l₃ := []) (l₄ := []) rfl
    revert this; decide

-- `List.le_iff_exists` (`inst`, idx 3): < empty on Nat (LtF, asymmetric, not trichotomous), l₁ = [0], l₂ = [1]: [0] ≤ [1] holds but no position has <
theorem le_iff_exists_h3 :
    ¬ (∀ {α : Type} [inst : LT α] [Std.Asymm fun (x1 x2 : α) => x1 < x2] {l₁ l₂ : List α},
        l₁ ≤ l₂ ↔
          l₁ = List.take l₁.length l₂ ∨
            ∃ (i : Nat),
              ∃ (h₁ : i < l₁.length), ∃ (h₂ : i < l₂.length), (∀ (j : Nat) (hj : j < i), l₁[j] = l₂[j]) ∧ l₁[i] < l₂[i]) :=
  fun h => by
    rcases (h (α := LtF) (l₁ := [0]) (l₂ := [1])).mp (by decide) with h | ⟨i, h₁, h₂, -, h⟩
    · revert h; decide
    · exact h

-- `List.lex_eq_false_iff_exists` (`inst`, idx 4): BEq Nat with a == b ↔ a ≤ b (BLe, not symmetric), lt a b := b < a, l₁ = [1], l₂ = [0]: lex is true but isEqv [0] [1] holds
theorem lex_eq_false_iff_exists_h4 :
    ¬ (∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] (lt : α → α → Bool),
        (∀ (x y : α), (x == y) = Bool.true → lt x y = Bool.false) →
          (∀ (x y : α), lt x y = Bool.true → lt y x = Bool.false) →
            (∀ (x y : α), lt x y = Bool.false → lt y x = Bool.false → (x == y) = Bool.true) →
              (l₁.lex l₂ lt = Bool.false ↔
                (l₂.isEqv (List.take l₂.length l₁) fun (x1 x2 : α) => x1 == x2) = Bool.true ∨
                  ∃ (i : Nat),
                    ∃ (h₁ : i < l₁.length),
                      ∃ (h₂ : i < l₂.length),
                        (∀ (j : Nat) (hj : j < i), (l₁[j] == l₂[j]) = Bool.true) ∧ lt l₂[i] l₁[i] = Bool.true)) :=
  fun h => by
    have := h (α := BLe) (l₁ := [1]) (l₂ := [0]) (fun a b => decide (b.val < a.val))
      (fun x y h => by change decide (x.val ≤ y.val) = true at h; simp at h ⊢; omega)
      (fun x y h => by simp at h ⊢; omega)
      (fun x y h₁ h₂ => by change decide (x.val ≤ y.val) = true; simp at h₁ h₂ ⊢; omega)
    exact absurd (this.mpr (Or.inl (by decide))) (by decide)

-- `List.lt_of_le_of_lt` (`inst`, idx 3): < empty, ≤ everywhere true on Nat (LtFT, LawfulOrderLT holds, ≤ not antisymmetric), l₁ = [1], l₂ = [0], l₃ = [0, 0]
theorem lt_of_le_of_lt_h3 :
    ¬ (∀ {α : Type} [inst : LT α] [inst_1 : LE α] [Std.LawfulOrderLT α] {l₁ l₂ l₃ : List α}, l₁ ≤ l₂ → l₂ < l₃ → l₁ < l₃) :=
  fun h => by
    have := h (α := LtFT) (l₁ := [1]) (l₂ := [0]) (l₃ := [0, 0]) (by decide) (by decide)
    revert this; decide

-- `List.lt_of_le_of_lt` (`inst`, idx 4): < empty on Nat (LtF, asymmetric, not trichotomous) with the usual ≤, l₁ = [1], l₂ = [0], l₃ = [0, 0]
theorem lt_of_le_of_lt_h4 :
    ¬ (∀ {α : Type} [inst : LT α] [inst_1 : LE α] [Std.IsLinearOrder α] {l₁ l₂ l₃ : List α}, l₁ ≤ l₂ → l₂ < l₃ → l₁ < l₃) :=
  fun h => by
    have := h (α := LtF) (l₁ := [1]) (l₂ := [0]) (l₃ := [0, 0]) (by decide) (by decide)
    revert this; decide

-- `List.le_trans` (`inst`, idx 3): < empty, ≤ everywhere true on Nat (LtFT, LawfulOrderLT holds, ≤ not antisymmetric), l₁ = [0, 0], l₂ = [1], l₃ = [0]
theorem le_trans_h3 :
    ¬ (∀ {α : Type} [inst : LT α] [inst_1 : LE α] [Std.LawfulOrderLT α] {l₁ l₂ l₃ : List α}, l₁ ≤ l₂ → l₂ ≤ l₃ → l₁ ≤ l₃) :=
  fun h => by
    have := h (α := LtFT) (l₁ := [0, 0]) (l₂ := [1]) (l₃ := [0]) (by decide) (by decide)
    revert this; decide

-- `List.le_trans` (`inst`, idx 4): < empty on Nat (LtF, asymmetric, not trichotomous) with the usual ≤, l₁ = [0, 0], l₂ = [1], l₃ = [0]
theorem le_trans_h4 :
    ¬ (∀ {α : Type} [inst : LT α] [inst_1 : LE α] [Std.IsLinearOrder α] {l₁ l₂ l₃ : List α}, l₁ ≤ l₂ → l₂ ≤ l₃ → l₁ ≤ l₃) :=
  fun h => by
    have := h (α := LtF) (l₁ := [0, 0]) (l₂ := [1]) (l₃ := [0]) (by decide) (by decide)
    revert this; decide

-- `List.instIsLinearOrder` (`inst`, idx 3): < empty, ≤ everywhere true on Nat (LtFT, LawfulOrderLT holds, ≤ not antisymmetric): list ≤ is not transitive ([0, 0] ≤ [1] ≤ [0])
theorem instIsLinearOrder_h3 :
    ¬ (∀ {α : Type} [inst : LT α] [inst_1 : LE α] [Std.LawfulOrderLT α], Std.IsLinearOrder (List α)) :=
  fun h => by
    have := (@h LtFT _ _ _).le_trans [0, 0] [1] [0] (by decide) (by decide)
    revert this; decide

-- `List.instIsLinearOrder` (`inst`, idx 4): < empty on Nat (LtF, asymmetric, not trichotomous) with the usual ≤: list ≤ is not transitive ([0, 0] ≤ [1] ≤ [0])
theorem instIsLinearOrder_h4 :
    ¬ (∀ {α : Type} [inst : LT α] [inst_1 : LE α] [Std.IsLinearOrder α], Std.IsLinearOrder (List α)) :=
  fun h => by
    have := (@h LtF _ _ _).le_trans [0, 0] [1] [0] (by decide) (by decide)
    revert this; decide

-- `List.instLawfulOrderOrd` (`inst`, idx 4): < empty, ≤ everywhere true on Nat (LtFT, LawfulOrderLT holds, ≤ not antisymmetric), compare constantly .eq: compare [1, 1] [0] = .gt but [1, 1] ≤ [0]
theorem instLawfulOrderOrd_h4 :
    ¬ (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Ord α] [Std.LawfulOrderLT α] [Std.LawfulOrderOrd α],
        Std.LawfulOrderOrd (List α)) :=
  fun h => by
    have := (@h LtFT _ _ _ _ _).isLE_compare [1, 1] [0]
    revert this; decide

-- `List.instLawfulOrderOrd` (`inst`, idx 5): < empty on Nat (LtF, asymmetric, not trichotomous) with the usual ≤ and compare: compare [1] [0] = .gt but [1] ≤ [0]
theorem instLawfulOrderOrd_h5 :
    ¬ (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Ord α] [Std.IsLinearOrder α] [Std.LawfulOrderOrd α],
        Std.LawfulOrderOrd (List α)) :=
  fun h => by
    have := (@h LtF _ _ _ _ _).isLE_compare [1] [0]
    revert this; decide

-- `List.instLawfulOrderOrd` (`inst`, idx 6): usual ≤, < on Nat with compare constantly .eq (OrdEq): compare [1] [0] = .eq but ¬ [1] ≤ [0]
theorem instLawfulOrderOrd_h6 :
    ¬ (∀ {α : Type} [inst : LE α] [inst_1 : LT α] [inst_2 : Ord α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α],
        Std.LawfulOrderOrd (List α)) :=
  fun h => by
    have := (@h OrdEq _ _ _ _ _).isLE_compare [1] [0]
    revert this; decide

-- `List.instReflLeOfIrreflLt` (`inst`, idx 2): a < b ↔ a ≤ b on Nat (LtLe, reflexive): ¬ [0] ≤ [0]
theorem instReflLeOfIrreflLt_h2 :
    ¬ (∀ {α : Type} [inst : LT α], Std.Refl fun (x1 x2 : List α) => x1 ≤ x2) :=
  fun h => by
    have := (@h LtLe _).refl [0]
    revert this; decide

-- `List.ltIrrefl` (`inst`, idx 2): a < b ↔ a ≤ b on Nat (LtLe, reflexive): [0] < [0]
theorem ltIrrefl_h2 :
    ¬ (∀ {α : Type} [inst : LT α], Std.Irrefl fun (x1 x2 : List α) => x1 < x2) :=
  fun h => (@h LtLe _).irrefl [0] (by decide)

-- `List.instAsymmLt` (`inst`, idx 2): a < b ↔ a ≤ b on Nat (LtLe, reflexive): [0] < [0]
theorem instAsymmLt_h2 :
    ¬ (∀ {α : Type} [inst : LT α], Std.Asymm fun (x1 x2 : List α) => x1 < x2) :=
  fun h => (@h LtLe _).asymm [0] [0] (by decide) (by decide)

-- `List.instLawfulOrderLTOfAsymmLt` (`inst`, idx 2): a < b ↔ a ≤ b on Nat (LtLe, reflexive): [0] < [0] but ¬ [0] ≤ [0]
theorem instLawfulOrderLTOfAsymmLt_h2 :
    ¬ (∀ {α : Type} [inst : LT α], Std.LawfulOrderLT (List α)) :=
  fun h => by
    have := (@h LtLe _).lt_iff [0] [0]
    revert this; decide

-- `List.instTotalLeOfAsymmLt` (`inst`, idx 2): a < b ↔ a ≤ b on Nat (LtLe, reflexive): ¬ [0] ≤ [0]
theorem instTotalLeOfAsymmLt_h2 :
    ¬ (∀ {α : Type} [inst : LT α], Std.Total fun (x1 x2 : List α) => x1 ≤ x2) :=
  fun h => by
    have := (@h LtLe _).total [0] [0]
    revert this; decide

-- `List.instAntisymmLeOfTrichotomousLt` (`s`, idx 2): < empty on Nat (LtF, asymmetric, not trichotomous): [0] ≤ [1] ≤ [0]
theorem instAntisymmLeOfTrichotomousLt_h2 :
    ¬ (∀ {α : Type} [inst : LT α], Std.Antisymm fun (x1 x2 : List α) => x1 ≤ x2) :=
  fun h => by
    have := (@h LtF _).antisymm [0] [1] (by decide) (by decide)
    revert this; decide


/-! ## `BEq`: necessary -/


-- `List.replace_toArray` (`inst`, idx 2): BEq Nat with a == b ↔ a ≤ b (BLe): List.replace tests a == x, Array.replace tests x == a; l = [0], a = 1, b = 5
theorem replace_toArray_h2 :
    ¬ (∀ {α : Type} [inst : BEq α] (l : List α) (a b : α), l.toArray.replace a b = (l.replace a b).toArray) :=
  fun h => by
    have := h (α := BLe) [0] 1 5
    revert this; decide +kernel

-- `List.finIdxOf?_eq_some_iff` (`inst`, idx 2): BEq Nat constantly true (BTrue), l = [1], a = 0, i = 0
theorem finIdxOfQ_eq_some_iff_h2 :
    ¬ (∀ {α : Type} [inst : BEq α] {l : List α} {a : α} {i : Fin l.length},
        List.finIdxOf? a l = Option.some i ↔ l[i] = a ∧ ∀ (j : Fin l.length), j < i → ¬l[j] = a) :=
  fun h => by
    have := h (α := BTrue) (l := [1]) (a := 0) (i := ⟨0, by decide⟩)
    revert this; decide

-- `List.instLawfulBEq` (`inst`, idx 2): BEq Nat constantly true (BTrue): [0] == [1]
theorem instLawfulBEq_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], LawfulBEq (List α)) :=
  fun h => absurd ((@h BTrue _).eq_of_beq (a := [(0 : BTrue)]) (b := [1]) (by decide)) (by decide)

-- `List.exists_erase_eq` (`inst`, idx 2): BEq Nat constantly true (BTrue), a = 0, l = [1, 0]: l.erase 0 = [0], but the only split with 0 ∉ l₁ is l₁ = [1]
theorem exists_erase_eq_h2 :
    ¬ (∀ {α : Type} [inst : BEq α] {a : α} {l : List α},
        a ∈ l → ∃ (l₁ : List α), ∃ (l₂ : List α), ¬a ∈ l₁ ∧ l = l₁ ++ a :: l₂ ∧ l.erase a = l₁ ++ l₂) :=
  fun h => by
    obtain ⟨l₁, l₂, hn, he, hr⟩ := h (α := BTrue) (a := 0) (l := [1, 0]) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    match l₁, l₂, hn, he, hr with
    | [], _, _, he, _ => exact absurd (List.cons.inj he).1 (by decide)
    | [x], l₂, _, he, hr =>
      obtain ⟨rfl, h2⟩ := List.cons.inj he
      obtain ⟨-, rfl⟩ := List.cons.inj h2
      revert hr; decide
    | _ :: _ :: _, _, _, he, _ => exact absurd (congrArg List.length he) (by simp)

-- `List.lookup_eq_some_iff` (`inst`, idx 3): BEq Nat constantly true (BTrue), l = [(1, 5)], k = 0, b = 5: lookup gives some 5, but (0, 5) ∉ l
theorem lookup_eq_some_iff_h3 :
    ¬ (∀ {α : Type} [inst : BEq α] {β : Type} {l : List (α × β)} {k : α} {b : β},
        List.lookup k l = Option.some b ↔
          ∃ (l₁ : List (α × β)),
            ∃ (l₂ : List (α × β)), l = l₁ ++ (k, b) :: l₂ ∧ ∀ (p : α × β), p ∈ l₁ → (k != p.fst) = Bool.true) :=
  fun h => by
    obtain ⟨l₁, l₂, he, hall⟩ := (h (α := BTrue) (l := [((1 : BTrue), 5)]) (k := 0) (b := 5)).mp (by decide)
    match l₁, he, hall with
    | [], he, _ => exact absurd (List.cons.inj he).1 (by decide)
    | p :: _, _, hall => exact absurd (hall p (List.mem_cons_self ..)) (fun h => Bool.noConfusion h)

-- `List.instReflBEq` (`inst`, idx 2): BEq Nat constantly false (BFalse): ([0] == [0]) = false
theorem instReflBEq_h2 :
    ¬ (∀ {α : Type} [inst : BEq α], ReflBEq (List α)) :=
  fun h => absurd ((@h BFalse _).rfl (a := [(0 : BFalse)])) (by decide)


/-! ## Sums, products and folds: necessary -/


-- `List.sum_reverse` (`inst`, idx 3): +/* as |a - b| on Nat with unit 0 (Dist, commutative, two-sided identity, not associative), xs = [1, 2, 3]
theorem sum_reverse_h3 :
    ¬ (∀ {α : Type} [inst : Zero α] [inst_1 : Add α] [Std.Commutative fun (x1 x2 : α) => x1 + x2]
        [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 + x2) 0] (xs : List α), xs.reverse.sum = xs.sum) :=
  fun h => by
    have := h (α := Dist) [Dist.mk 1, Dist.mk 2, Dist.mk 3]
    revert this; decide

-- `List.sum_reverse` (`inst`, idx 4): +/* as last nonzero argument on Nat with unit 0 (Last, associative, left identity, not commutative), xs = [1, 2]
theorem sum_reverse_h4 :
    ¬ (∀ {α : Type} [inst : Zero α] [inst_1 : Add α] [Std.Associative fun (x1 x2 : α) => x1 + x2]
        [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 + x2) 0] (xs : List α), xs.reverse.sum = xs.sum) :=
  fun h => by
    have := h (α := Last) [Last.mk 1, Last.mk 2]
    revert this; decide

-- `List.prod_reverse` (`inst`, idx 3): +/* as |a - b| on Nat with unit 0 (Dist, commutative, two-sided identity, not associative), xs = [1, 2, 3]
theorem prod_reverse_h3 :
    ¬ (∀ {α : Type} [inst : One α] [inst_1 : Mul α] [Std.Commutative fun (x1 x2 : α) => x1 * x2]
        [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 * x2) 1] (xs : List α), xs.reverse.prod = xs.prod) :=
  fun h => by
    have := h (α := Dist) [Dist.mk 1, Dist.mk 2, Dist.mk 3]
    revert this; decide

-- `List.prod_reverse` (`inst`, idx 4): +/* as last nonzero argument on Nat with unit 0 (Last, associative, left identity, not commutative), xs = [1, 2]
theorem prod_reverse_h4 :
    ¬ (∀ {α : Type} [inst : One α] [inst_1 : Mul α] [Std.Associative fun (x1 x2 : α) => x1 * x2]
        [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 * x2) 1] (xs : List α), xs.reverse.prod = xs.prod) :=
  fun h => by
    have := h (α := Last) [Last.mk 1, Last.mk 2]
    revert this; decide

-- `List.sum_singleton` (`inst`, idx 3): usual addition on Nat as +/* with 0/1 := 1 (Shift, associative, commutative, no identity), x = 0: [0].sum = 1
theorem sum_singleton_h3 :
    ¬ (∀ {α : Type} [inst : Add α] [inst_1 : Zero α] {x : α}, [x].sum = x) :=
  fun h => by
    have := h (α := Shift) (x := Shift.mk 0)
    revert this; decide

-- `List.prod_singleton` (`inst`, idx 3): usual addition on Nat as +/* with 0/1 := 1 (Shift, associative, commutative, no identity), x = 0: [0].prod = 1
theorem prod_singleton_h3 :
    ¬ (∀ {α : Type} [inst : Mul α] [inst_1 : One α] {x : α}, [x].prod = x) :=
  fun h => by
    have := h (α := Shift) (x := Shift.mk 0)
    revert this; decide

-- `List.sum_append` (`inst`, idx 3): usual addition on Nat as +/* with 0/1 := 1 (Shift, associative, commutative, no identity), l₁ = l₂ = []
theorem sum_append_h3 :
    ¬ (∀ {α : Type} [inst : Add α] [inst_1 : Zero α] [Std.Associative fun (x1 x2 : α) => x1 + x2] {l₁ l₂ : List α},
        (l₁ ++ l₂).sum = l₁.sum + l₂.sum) :=
  fun h => by
    have := h (α := Shift) (l₁ := []) (l₂ := [])
    revert this; decide

-- `List.prod_append` (`inst`, idx 3): usual addition on Nat as +/* with 0/1 := 1 (Shift, associative, commutative, no identity), l₁ = l₂ = []
theorem prod_append_h3 :
    ¬ (∀ {α : Type} [inst : Mul α] [inst_1 : One α] [Std.Associative fun (x1 x2 : α) => x1 * x2] {l₁ l₂ : List α},
        (l₁ ++ l₂).prod = l₁.prod * l₂.prod) :=
  fun h => by
    have := h (α := Shift) (l₁ := []) (l₂ := [])
    revert this; decide

-- `List.sum_append` (`inst`, idx 4): +/* as |a - b| on Nat with unit 0 (Dist, commutative, two-sided identity, not associative), l₁ = [1, 2], l₂ = [3]
theorem sum_append_h4 :
    ¬ (∀ {α : Type} [inst : Add α] [inst_1 : Zero α] [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 + x2) 0]
        {l₁ l₂ : List α}, (l₁ ++ l₂).sum = l₁.sum + l₂.sum) :=
  fun h => by
    have := h (α := Dist) (l₁ := [Dist.mk 1, Dist.mk 2]) (l₂ := [Dist.mk 3])
    revert this; decide

-- `List.prod_append` (`inst`, idx 4): +/* as |a - b| on Nat with unit 0 (Dist, commutative, two-sided identity, not associative), l₁ = [1, 2], l₂ = [3]
theorem prod_append_h4 :
    ¬ (∀ {α : Type} [inst : Mul α] [inst_1 : One α] [Std.LawfulLeftIdentity (fun (x1 x2 : α) => x1 * x2) 1]
        {l₁ l₂ : List α}, (l₁ ++ l₂).prod = l₁.prod * l₂.prod) :=
  fun h => by
    have := h (α := Dist) (l₁ := [Dist.mk 1, Dist.mk 2]) (l₂ := [Dist.mk 3])
    revert this; decide

-- `List.sum_eq_foldl` (`inst`, idx 3): +/* as |a - b| on Nat with unit 0 (Dist, commutative, two-sided identity, not associative), xs = [1, 2, 3]
theorem sum_eq_foldl_h3 :
    ¬ (∀ {α : Type} [inst : Zero α] [inst_1 : Add α] [Std.LawfulIdentity (fun (x1 x2 : α) => x1 + x2) 0] {xs : List α},
        xs.sum = List.foldl (fun (x1 x2 : α) => x1 + x2) 0 xs) :=
  fun h => by
    have := h (α := Dist) (xs := [Dist.mk 1, Dist.mk 2, Dist.mk 3])
    revert this; decide

-- `List.prod_eq_foldl` (`inst`, idx 3): +/* as |a - b| on Nat with unit 0 (Dist, commutative, two-sided identity, not associative), xs = [1, 2, 3]
theorem prod_eq_foldl_h3 :
    ¬ (∀ {α : Type} [inst : One α] [inst_1 : Mul α] [Std.LawfulIdentity (fun (x1 x2 : α) => x1 * x2) 1] {xs : List α},
        xs.prod = List.foldl (fun (x1 x2 : α) => x1 * x2) 1 xs) :=
  fun h => by
    have := h (α := Dist) (xs := [Dist.mk 1, Dist.mk 2, Dist.mk 3])
    revert this; decide

-- `List.sum_eq_foldl` (`inst`, idx 4): +/* as left projection on Nat with 0/1 := 0 (LProj, associative, no identity), xs = [1]
theorem sum_eq_foldl_h4 :
    ¬ (∀ {α : Type} [inst : Zero α] [inst_1 : Add α] [Std.Associative fun (x1 x2 : α) => x1 + x2] {xs : List α},
        xs.sum = List.foldl (fun (x1 x2 : α) => x1 + x2) 0 xs) :=
  fun h => by
    have := h (α := LProj) (xs := [LProj.mk 1])
    revert this; decide

-- `List.prod_eq_foldl` (`inst`, idx 4): +/* as left projection on Nat with 0/1 := 0 (LProj, associative, no identity), xs = [1]
theorem prod_eq_foldl_h4 :
    ¬ (∀ {α : Type} [inst : One α] [inst_1 : Mul α] [Std.Associative fun (x1 x2 : α) => x1 * x2] {xs : List α},
        xs.prod = List.foldl (fun (x1 x2 : α) => x1 * x2) 1 xs) :=
  fun h => by
    have := h (α := LProj) (xs := [LProj.mk 1])
    revert this; decide

-- `List.foldr_eq_foldl` (`inst`, idx 4): f = |a - b| on Nat, init = 0 (identity, not associative), xs = [1, 2, 3]
theorem foldr_eq_foldl_h4 :
    ¬ (∀ {α : Type} {init : α} {xs : List α} {f : α → α → α} [Std.LawfulIdentity f init],
        List.foldr f init xs = List.foldl f init xs) :=
  fun h => by
    have := h (α := Dist) (init := 0) (xs := [Dist.mk 1, Dist.mk 2, Dist.mk 3]) (f := fun x y => x + y)
    revert this; decide

-- `List.foldl_max_eq_max` (`inst`, idx 3): max/min as rounded midpoint on Nat (Mid, idempotent, not associative), l = [0, 4], a = 0
theorem foldl_max_eq_max_h3 :
    ¬ (∀ {α : Type} [inst : Max α] [Std.IdempotentOp (Max.max : α → α → α)] {l : List α} (hl : l ≠ []) {a : α},
        List.foldl Max.max a l = Max.max a (l.max hl)) :=
  fun h => by
    have := h (α := Mid) (l := [0, 4]) (by simp) (a := 0)
    revert this; decide

-- `List.foldl_min_eq_min` (`inst`, idx 3): max/min as rounded midpoint on Nat (Mid, idempotent, not associative), l = [0, 4], a = 0
theorem foldl_min_eq_min_h3 :
    ¬ (∀ {α : Type} [inst : Min α] [Std.IdempotentOp (Min.min : α → α → α)] {l : List α} (hl : l ≠ []) {a : α},
        List.foldl Min.min a l = Min.min a (l.min hl)) :=
  fun h => by
    have := h (α := Mid) (l := [0, 4]) (by simp) (a := 0)
    revert this; decide

-- `List.foldl_max` (`inst`, idx 3): max/min as rounded midpoint on Nat (Mid, idempotent, not associative), l = [0, 4], a = 0
theorem foldl_max_h3 :
    ¬ (∀ {α : Type} [inst : Max α] [Std.IdempotentOp (Max.max : α → α → α)] {l : List α} {a : α},
        List.foldl Max.max a l = Max.max a (l.max?.getD a)) :=
  fun h => by
    have := h (α := Mid) (l := [0, 4]) (a := 0)
    revert this; decide

-- `List.foldl_min` (`inst`, idx 3): max/min as rounded midpoint on Nat (Mid, idempotent, not associative), l = [0, 4], a = 0
theorem foldl_min_h3 :
    ¬ (∀ {α : Type} [inst : Min α] [Std.IdempotentOp (Min.min : α → α → α)] {l : List α} {a : α},
        List.foldl Min.min a l = Min.min a (l.min?.getD a)) :=
  fun h => by
    have := h (α := Mid) (l := [0, 4]) (a := 0)
    revert this; decide


/-! ## `MinMaxOn`/`MinMaxIdx`: removable -/

namespace OrderListHand

/-! ### Helpers for `minIdxOn`/`minOn` without any order laws -/

section MinIdx
variable {β : Type u_1} {α : Type u_2} [LE β] [DecidableLE β]

/-- A copy of the private scan `List.minIdxOn.go`. -/
def myGo (f : α → β) (x : α) (i j : Nat) : List α → Nat
  | [] => i
  | y :: ys => if f x ≤ f y then myGo f x i (j + 1) ys else myGo f y j (j + 1) ys

theorem minIdxOn_cons_eq' (f : α → β) (y : α) (ys : List α) :
    List.minIdxOn f (y :: ys) (List.cons_ne_nil _ _) = myGo f y 0 1 ys := by
  unfold List.minIdxOn
  generalize 0 = i
  generalize 1 = j
  induction ys generalizing y i j with
  | nil => rfl
  | cons z zs ih =>
    show (if f y ≤ f z then _ else _) = _
    simp only [myGo]
    split
    · exact ih _ _ _
    · exact ih _ _ _

theorem minIdxOn_cons_eq (f : α → β) (y : α) (ys : List α) (h : y :: ys ≠ []) :
    List.minIdxOn f (y :: ys) h = myGo f y 0 1 ys :=
  minIdxOn_cons_eq' f y ys

/-- The scan `minIdxOn.go` and the fold `minOn` make the same choice at every step, so the index
it returns points at the folded value (for any `LE`). -/
theorem go_getElem? (f : α → β) :
    ∀ (ys pre : List α) (x : α) (i j : Nat), pre.length = j → pre[i]? = some x →
      (pre ++ ys)[myGo f x i j ys]? = some (ys.foldl (minOn f) x)
  | [], pre, x, i, j, _, hx => by simpa [myGo] using hx
  | y :: ys, pre, x, i, j, hj, hx => by
    have hi : i < pre.length := (List.getElem?_eq_some_iff.mp hx).1
    have e : pre ++ y :: ys = (pre ++ [y]) ++ ys := by simp
    rw [e]
    simp only [myGo, List.foldl_cons, minOn]
    split
    · exact go_getElem? f ys (pre ++ [y]) x i (j + 1) (by simp [hj])
        (by rw [List.getElem?_append_left hi]; exact hx)
    · exact go_getElem? f ys (pre ++ [y]) y j (j + 1) (by simp [hj])
        (by rw [List.getElem?_append_right (by omega)]; simp [hj])

theorem getElem_minIdxOn' {f : α → β} {xs : List α} (h : xs ≠ []) :
    xs[xs.minIdxOn f h]'(List.minIdxOn_lt_length h) = xs.minOn f h := by
  match xs, h with
  | z :: zs, h =>
    have : (z :: zs)[List.minIdxOn f (z :: zs) h]? = some (List.minOn f (z :: zs) h) := by
      rw [minIdxOn_cons_eq]; exact go_getElem? f zs [z] z 0 1 rfl rfl
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans this)

/-- The index kept by the scan never decreases. -/
theorem le_go (f : α → β) : ∀ (ys : List α) (x : α) (i j : Nat), i ≤ j → i ≤ myGo f x i j ys
  | [], _, _, _, _ => by simp [myGo]
  | y :: ys, x, i, j, h => by
    simp only [myGo]
    split
    · exact le_go f ys x i (j + 1) (by omega)
    · exact Nat.le_trans h (le_go f ys y j (j + 1) (by omega))

theorem go_take_le (f : α → β) : ∀ (ys : List α) (k : Nat) (x : α) (i j : Nat), i ≤ j →
    myGo f x i j (ys.take k) ≤ myGo f x i j ys
  | [], _, _, _, _, _ => by simp
  | _ :: _, 0, x, i, j, h => by rw [List.take_zero]; exact le_go f _ x i j h
  | y :: ys, k + 1, x, i, j, h => by
    simp only [List.take_succ_cons, myGo]
    split
    · exact go_take_le f ys k x i (j + 1) (by omega)
    · exact go_take_le f ys k y j (j + 1) (by omega)

theorem go_le_go_append (f : α → β) (ys : List α) : ∀ (zs : List α) (x : α) (i j : Nat), i ≤ j →
    myGo f x i j zs ≤ myGo f x i j (zs ++ ys)
  | [], x, i, j, h => le_go f ys x i j h
  | z :: zs, x, i, j, h => by
    simp only [List.cons_append, myGo]
    split
    · exact go_le_go_append f ys zs x i (j + 1) (by omega)
    · exact go_le_go_append f ys zs z j (j + 1) (by omega)

theorem minIdxOn_take_le' {xs : List α} {f : α → β} {i : Nat} (h : xs.take i ≠ []) :
    (xs.take i).minIdxOn f h ≤ xs.minIdxOn f (List.ne_nil_of_take_ne_nil h) := by
  match xs, i, h with
  | [], _, h => simp at h
  | _ :: _, 0, h => simp at h
  | z :: zs, k + 1, h =>
    simp only [List.take_succ_cons, minIdxOn_cons_eq]; exact go_take_le f zs k z 0 1 (by omega)

theorem left_le_minIdxOn_append' {xs ys : List α} {f : α → β} (h : xs ≠ []) :
    xs.minIdxOn f h ≤ (xs ++ ys).minIdxOn f (by simp [h]) := by
  match xs, h with
  | z :: zs, _ =>
    simp only [List.cons_append, minIdxOn_cons_eq]; exact go_le_go_append f ys zs z 0 1 (by omega)

/-- If no earlier element is `≤` the one at position `t`, the scan reaches `t` and switches to it. -/
theorem le_go_of_not_le (f : α → β) (t : Nat) : ∀ (ys pre : List α) (x : α) (c j : Nat),
    pre.length = j → pre[c]? = some x → c < j → j ≤ t → t < j + ys.length →
    (∀ k, k < t → ∀ a b, (pre ++ ys)[k]? = some a → (pre ++ ys)[t]? = some b → ¬ f a ≤ f b) →
    t ≤ myGo f x c j ys
  | [], _, _, _, _, _, _, _, h₁, h₂, _ => by simp at h₂; omega
  | y :: ys, pre, x, c, j, hj, hx, hc, h₁, h₂, H => by
    have e : pre ++ y :: ys = (pre ++ [y]) ++ ys := by simp
    rw [e] at H
    simp only [myGo]
    by_cases ht : t = j
    · subst ht
      have hn : ¬ f x ≤ f y := H c hc x y
        (by rw [List.append_assoc, List.getElem?_append_left (by omega)]; exact hx)
        (by rw [List.append_assoc, List.getElem?_append_right (by omega)]; simp [hj])
      simp only [hn, ↓reduceIte]
      exact le_go f ys y _ _ (by omega)
    · split
      · exact le_go_of_not_le f t ys (pre ++ [y]) x c (j + 1) (by simp [hj])
          (by rw [List.getElem?_append_left (by omega)]; exact hx) (by omega) (by omega)
          (by simp at h₂; omega) H
      · exact le_go_of_not_le f t ys (pre ++ [y]) y j (j + 1) (by simp [hj])
          (by rw [List.getElem?_append_right (by omega)]; simp [hj]) (by omega) (by omega)
          (by simp at h₂; omega) H

theorem le_minIdxOn_of_not_le {f : α → β} {xs : List α} (h : xs ≠ []) {i : Nat}
    (hi : i < xs.length) (H : ∀ j (hj : j < i), ¬ f (xs[j]'(by omega)) ≤ f xs[i]) :
    i ≤ xs.minIdxOn f h := by
  match xs, h with
  | z :: zs, h =>
    by_cases i0 : i = 0
    · omega
    · rw [minIdxOn_cons_eq]
      refine le_go_of_not_le f i zs [z] z 0 1 rfl rfl (by omega) (by omega)
        (by simp at hi; omega) ?_
      intro k hk a b ha hb
      have ha' := List.getElem?_eq_some_iff.mp ha
      have hb' := List.getElem?_eq_some_iff.mp hb
      have := H k hk
      simp only [List.singleton_append] at ha' hb'
      rw [← ha'.2, ← hb'.2]; exact this

/-- The fold `minOn` keeps its start value if that value is `≤` all others. -/
theorem foldl_minOn_of_le (f : α → β) : ∀ (ys : List α) (x : α), (∀ y ∈ ys, f x ≤ f y) →
    ys.foldl (minOn f) x = x
  | [], _, _ => rfl
  | y :: ys, x, h => by
    simp only [List.foldl_cons, minOn, h y (List.mem_cons_self ..), ↓reduceIte]
    exact foldl_minOn_of_le f ys x (fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem foldl_minOn_replicate (f : α → β) (k : Nat) (a : α) :
    (List.replicate k a).foldl (minOn f) a = a := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.foldl_cons, minOn, ite_self, ih]

end MinIdx

end OrderListHand

namespace OrderListHand

theorem apply_maxOn_eq_max {β : Type u_1} {α : Type u_2} [LE β] [DecidableLE β] [Max β]
    [Std.LawfulOrderLeftLeaningMax β] (f : α → β) (z y : α) : f (maxOn f z y) = max (f z) (f y) := by
  by_cases h : f y ≤ f z
  · rw [maxOn_eq_left h, Std.LawfulOrderLeftLeaningMax.max_eq_left _ _ h]
  · rw [maxOn_eq_right h, Std.LawfulOrderLeftLeaningMax.max_eq_right _ _ h]

theorem map_foldl_maxOn {β : Type u_1} {α : Type u_2} [LE β] [DecidableLE β] [Max β]
    [Std.LawfulOrderLeftLeaningMax β] (f : α → β) :
    ∀ (zs : List α) (z : α), f (zs.foldl (maxOn f) z) = (zs.map f).foldl max (f z)
  | [], _ => rfl
  | y :: ys, z => by
    simp only [List.foldl_cons, List.map_cons]
    rw [map_foldl_maxOn f ys, apply_maxOn_eq_max f]

theorem map_foldl_max {α : Type u_1} {β : Type u_2} [Max α] [LE α] [Std.LawfulOrderLeftLeaningMax α]
    [Max β] [LE β] [Std.LawfulOrderLeftLeaningMax β] (f : α → β) (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) :
    ∀ (zs : List α) (z : α), f (zs.foldl max z) = (zs.map f).foldl max (f z)
  | [], _ => rfl
  | y :: ys, z => by
    simp only [List.foldl_cons, List.map_cons]
    rw [map_foldl_max f hf ys]
    congr 1
    by_cases h : y ≤ z
    · rw [Std.LawfulOrderLeftLeaningMax.max_eq_left _ _ h,
        Std.LawfulOrderLeftLeaningMax.max_eq_left _ _ ((hf y z).mpr h)]
    · rw [Std.LawfulOrderLeftLeaningMax.max_eq_right _ _ h,
        Std.LawfulOrderLeftLeaningMax.max_eq_right _ _ (fun h' => h ((hf y z).mp h'))]

/-- With `+` associative and commutative, `(l ++ [a]).sum = a + l.sum` (no identity needed). -/
theorem sum_append_singleton {α : Type u_1} [Zero α] [Add α] [Std.Associative fun x y : α => x + y]
    [Std.Commutative fun x y : α => x + y] (l : List α) (a : α) : (l ++ [a]).sum = a + l.sum := by
  have hA : ∀ a b c : α, a + b + c = a + (b + c) := Std.Associative.assoc (op := fun x y : α => x + y)
  have hC : ∀ a b : α, a + b = b + a := Std.Commutative.comm (op := fun x y : α => x + y)
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.cons_append, List.sum_cons, ih]; rw [← hA, hC x a, hA]

theorem prod_append_singleton {α : Type u_1} [One α] [Mul α] [Std.Associative fun x y : α => x * y]
    [Std.Commutative fun x y : α => x * y] (l : List α) (a : α) : (l ++ [a]).prod = a * l.prod := by
  have hA : ∀ a b c : α, a * b * c = a * (b * c) := Std.Associative.assoc (op := fun x y : α => x * y)
  have hC : ∀ a b : α, a * b = b * a := Std.Commutative.comm (op := fun x y : α => x * y)
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.cons_append, List.prod_cons, ih]; rw [← hA, hC x a, hA]

/-- `map f l₂ < map f l₁ → l₂ < l₁` for strictly monotone `f`, using only `Trichotomous` on `α` and
`Asymm` on `β`. -/
theorem lt_of_map_lt {α : Type u_1} {β : Type u_2} [LT α] [LT β]
    [Std.Trichotomous (· < · : α → α → Prop)] [Std.Asymm (· < · : β → β → Prop)] {f : α → β}
    (hf : ∀ x y : α, x < y → f x < f y) : ∀ {l₂ l₁ : List α}, List.map f l₂ < List.map f l₁ → l₂ < l₁
  | [], [], h => absurd h (List.not_lt_nil _)
  | [], _ :: _, _ => List.Lex.nil
  | _ :: _, [], h => absurd h (List.not_lt_nil _)
  | a :: as, b :: bs, h => by
    rw [List.map_cons, List.map_cons, List.cons_lt_cons_iff] at h
    by_cases hab : a < b
    · exact List.Lex.rel hab
    by_cases hba : b < a
    · have hfba := hf _ _ hba
      rcases h with h | ⟨h, -⟩
      · exact absurd h (Std.Asymm.asymm _ _ hfba)
      · rw [h] at hfba; exact absurd hfba (Std.Asymm.asymm _ _ hfba)
    have e := Std.Trichotomous.trichotomous a b hab hba
    subst e
    rcases h with h | ⟨-, h⟩
    · exact absurd h (Std.Asymm.asymm _ _ h)
    · exact List.Lex.cons (lt_of_map_lt hf h)

/-- `contains b (replicate n a) = false` when `(b == a) = false`, for any `BEq`. -/
theorem contains_replicate_of_beq_false {α : Type u_1} [BEq α] {a b : α} (h : (b == a) = false) :
    ∀ n, (List.replicate n a).contains b = false
  | 0 => rfl
  | n + 1 => by simp only [List.replicate_succ, List.contains_cons, h, contains_replicate_of_beq_false h n]; rfl

end OrderListHand


-- `List.getElem_minIdxOn` (`inst`, idx 4): the index scan minIdxOn.go and the fold minOn make the same comparison at every step, for any LE, so the index points at the folded value
theorem getElem_minIdxOn_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []),
      xs[List.minIdxOn f xs h] = List.minOn f xs h :=
  fun h => getElem_minIdxOn' h

-- `List.getElem_maxIdxOn` (`inst`, idx 4): the index scan minIdxOn.go and the fold minOn make the same comparison at every step, for any LE (maxIdxOn is minIdxOn for the opposite LE)
theorem getElem_maxIdxOn_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {xs : List α} (h : xs ≠ []),
      xs[List.maxIdxOn f xs h] = List.maxOn f xs h :=
  by
    intro β α le _ f xs h
    exact @getElem_minIdxOn' β α le.opposite _ f xs h

-- `List.getElem_get_minIdxOn?` (`inst`, idx 4): the index scan minIdxOn.go and the fold minOn make the same comparison at every step, for any LE
theorem getElem_get_minIdxOnQ_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {xs : List α}
      (h : (List.minIdxOn? f xs).isSome = Bool.true),
      xs[(List.minIdxOn? f xs).get h] = List.minOn f xs (List.isSome_minIdxOn?_iff.mp h) :=
  by
    intro β α le _ f xs h
    match xs, h with
    | z :: zs, _ => exact getElem_minIdxOn' (List.cons_ne_nil _ _)

-- `List.getElem_get_maxIdxOn?` (`inst`, idx 4): the index scan minIdxOn.go and the fold minOn make the same comparison at every step, for any LE (opposite LE)
theorem getElem_get_maxIdxOnQ_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {xs : List α}
      (h : (List.maxIdxOn? f xs).isSome = Bool.true),
      xs[(List.maxIdxOn? f xs).get h] = List.maxOn f xs (List.isSome_maxIdxOn?_iff.mp h) :=
  by
    intro β α le _ f xs h
    match xs, h with
    | z :: zs, _ => exact @getElem_minIdxOn' β α le.opposite _ f (z :: zs) (List.cons_ne_nil _ _)

-- `List.le_minIdxOn_of_apply_getElem_lt_apply_getElem` (`inst`, idx 5): LawfulOrderLT suffices: when the scan reaches position i, the kept earlier element is not ≤ xs[i] (by hypothesis), so it switches to i; the kept index never decreases
theorem le_minIdxOn_of_apply_getElem_lt_apply_getElem_h5 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [Std.LawfulOrderLT β] {f : α → β}
      {xs : List α} (h : xs ≠ []) {i : Nat} (hi : i < xs.length),
      (∀ (j : Nat) (x : j < i), f xs[i] < f xs[j]) → i ≤ List.minIdxOn f xs h :=
  by
    intro β α le _ _ _ f xs h i hi H
    exact le_minIdxOn_of_not_le h hi (fun j hj => ((Std.LawfulOrderLT.lt_iff _ _).mp (H j hj)).2)

-- `List.le_maxIdxOn_of_apply_getElem_lt_apply_getElem` (`inst`, idx 5): LawfulOrderLT suffices (same scan argument, opposite LE)
theorem le_maxIdxOn_of_apply_getElem_lt_apply_getElem_h5 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [Std.LawfulOrderLT β] {f : α → β}
      {xs : List α} (h : xs ≠ []) {i : Nat} (hi : i < xs.length),
      (∀ (j : Nat) (x : j < i), f xs[j] < f xs[i]) → i ≤ List.maxIdxOn f xs h :=
  by
    intro β α le _ _ _ f xs h i hi H
    exact @le_minIdxOn_of_not_le β α le.opposite _ f xs h i hi
      (fun j hj h' => ((Std.LawfulOrderLT.lt_iff _ _).mp (H j hj)).2 (LE.le_opposite_iff.mp h'))

-- `List.minIdxOn_take_le` (`inst`, idx 4): the index kept by the scan never decreases, and the scan of take i xs is a prefix of the scan of xs
theorem minIdxOn_take_le_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {xs : List α} {f : α → β} {i : Nat}
      (h : List.take i xs ≠ []), List.minIdxOn f (List.take i xs) h ≤ List.minIdxOn f xs (List.ne_nil_of_take_ne_nil h) :=
  fun h => minIdxOn_take_le' h

-- `List.maxIdxOn_take_le` (`inst`, idx 4): the index kept by the scan never decreases (opposite LE)
theorem maxIdxOn_take_le_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {xs : List α} {f : α → β} {i : Nat}
      (h : List.take i xs ≠ []), List.maxIdxOn f (List.take i xs) h ≤ List.maxIdxOn f xs (List.ne_nil_of_take_ne_nil h) :=
  by
    intro β α le _ xs f i h
    exact @minIdxOn_take_le' β α le.opposite _ xs f i h

-- `List.left_le_minIdxOn_append` (`inst`, idx 4): the index kept by the scan never decreases
theorem left_le_minIdxOn_append_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {xs ys : List α} {f : α → β} (h : xs ≠ []),
      List.minIdxOn f xs h ≤ List.minIdxOn f (xs ++ ys) (List.minIdxOn_append._proof_1 h) :=
  fun h => left_le_minIdxOn_append' h

-- `List.left_le_maxIdxOn_append` (`inst`, idx 4): the index kept by the scan never decreases (opposite LE)
theorem left_le_maxIdxOn_append_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {xs ys : List α} {f : α → β} (h : xs ≠ []),
      List.maxIdxOn f xs h ≤ List.maxIdxOn f (xs ++ ys) (List.minIdxOn_append._proof_1 h) :=
  by
    intro β α le _ xs ys f h
    exact @left_le_minIdxOn_append' β α le.opposite _ xs ys f h

-- `List.minOn_replicate` (`inst`, idx 4): minOn f a a = a for any LE (both branches of the if are a)
theorem minOn_replicate_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {n : Nat} {a : α} {f : α → β}
      (h : List.replicate n a ≠ []), List.minOn f (List.replicate n a) h = a :=
  by
    intro β α _ _ n a f h
    match n, h with
    | 0, h => simp at h
    | k + 1, _ => exact foldl_minOn_replicate f k a

-- `List.maxOn_replicate` (`inst`, idx 4): maxOn f a a = a for any LE
theorem maxOn_replicate_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {n : Nat} {a : α} {f : α → β}
      (h : List.replicate n a ≠ []), List.maxOn f (List.replicate n a) h = a :=
  by
    intro β α le _ n a f h
    match n, h with
    | 0, h => simp at h
    | k + 1, _ => exact @foldl_minOn_replicate β α le.opposite _ f k a

-- `List.minOn?_replicate_of_pos` (`inst`, idx 4): minOn f a a = a for any LE
theorem minOnQ_replicate_of_pos_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {n : Nat} {a : α} {f : α → β},
      0 < n → List.minOn? f (List.replicate n a) = Option.some a :=
  by
    intro β α _ _ n a f hn
    match n, hn with
    | 0, hn => exact absurd hn (Nat.lt_irrefl 0)
    | k + 1, _ => exact congrArg some (foldl_minOn_replicate f k a)

-- `List.maxOn?_replicate_of_pos` (`inst`, idx 4): maxOn f a a = a for any LE
theorem maxOnQ_replicate_of_pos_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {n : Nat} {a : α} {f : α → β},
      0 < n → List.maxOn? f (List.replicate n a) = Option.some a :=
  by
    intro β α le _ n a f hn
    match n, hn with
    | 0, hn => exact absurd hn (Nat.lt_irrefl 0)
    | k + 1, _ => exact congrArg some (@foldl_minOn_replicate β α le.opposite _ f k a)

-- `List.minOn?_replicate` (`inst`, idx 4): minOn f a a = a for any LE
theorem minOnQ_replicate_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {n : Nat} {a : α} {f : α → β},
      List.minOn? f (List.replicate n a) = if n = 0 then Option.none else Option.some a :=
  by
    intro β α _ _ n a f
    cases n with
    | zero => rfl
    | succ k =>
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      exact congrArg some (foldl_minOn_replicate f k a)

-- `List.maxOn?_replicate` (`inst`, idx 4): maxOn f a a = a for any LE
theorem maxOnQ_replicate_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {n : Nat} {a : α} {f : α → β},
      List.maxOn? f (List.replicate n a) = if n = 0 then Option.none else Option.some a :=
  by
    intro β α le _ n a f
    cases n with
    | zero => rfl
    | succ k =>
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      exact congrArg some (@foldl_minOn_replicate β α le.opposite _ f k a)

-- `List.minOn_eq_head` (`inst`, idx 4): the fold keeps the head when f head ≤ f x for every later x; no order law used
theorem minOn_eq_head_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {xs : List α} {f : α → β} (h : xs ≠ []),
      (∀ (x : α), x ∈ xs → f (xs.head h) ≤ f x) → List.minOn f xs h = xs.head h :=
  by
    intro β α _ _ xs f h H
    match xs, h with
    | z :: zs, _ => exact foldl_minOn_of_le f zs z (fun y hy => H y (List.mem_cons_of_mem _ hy))

-- `List.maxOn_eq_head` (`inst`, idx 4): the fold keeps the head when f x ≤ f head for every later x; no order law used
theorem maxOn_eq_head_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {xs : List α} {f : α → β} (h : xs ≠ []),
      (∀ (x : α), x ∈ xs → f x ≤ f (xs.head h)) → List.maxOn f xs h = xs.head h :=
  by
    intro β α le _ xs f h H
    match xs, h with
    | z :: zs, _ =>
      exact @foldl_minOn_of_le β α le.opposite _ f zs z
        (fun y hy => LE.le_opposite_iff.mpr (H y (List.mem_cons_of_mem _ hy)))

-- `List.max_map` (`inst`, idx 5): LawfulOrderLeftLeaningMax alone gives f (maxOn f x y) = max (f x) (f y) (both are decided by f y ≤ f x), so the two folds agree
theorem max_map_h5 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : Max β]
      [Std.LawfulOrderLeftLeaningMax β] {xs : List α} {f : α → β} (h : xs ≠ []),
      (List.map f xs).max (List.min_map._proof_1 h) = f (List.maxOn f xs h) :=
  by
    intro β α _ _ _ _ xs f h
    match xs, h with
    | z :: zs, _ => exact (map_foldl_maxOn f zs z).symm

-- `List.max_map_eq_max` (`inst`, idx 9): the left-leaning laws and hf give f (max a b) = max (f a) (f b) (both are decided by b ≤ a), so the folds agree
theorem max_map_eq_max_h9 :
    ∀ {α : Type u_1} {β : Type u_2} [inst : Max α] [inst_1 : LE α] [DecidableLE α] [Std.LawfulOrderLeftLeaningMax α]
      [inst_4 : Max β] [inst_5 : LE β] [DecidableLE β] [Std.LawfulOrderLeftLeaningMax β] {f : α → β},
      (∀ (a b : α), f a ≤ f b ↔ a ≤ b) →
        ∀ {l : List α} {h : l ≠ []}, (List.map f l).max (by simpa using h) = f (l.max h) :=
  by
    intro α β _ _ _ _ _ _ _ _ f hf l h
    match l, h with
    | z :: zs, _ => exact (map_foldl_max f hf zs z).symm

-- `List.maxOn?_eq_ite` (`inst`, idx 4): holds by definition (case split on xs)
theorem maxOnQ_eq_ite_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {xs : List α},
      List.maxOn? f xs = if h : xs ≠ [] then Option.some (List.maxOn f xs h) else Option.none :=
  by
    intro β α _ _ f xs
    cases xs with
    | nil => rfl
    | cons z zs => simp only [ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceDIte]; rfl

-- `List.maxOn?_eq_if` (`inst`, idx 4): holds by definition (case split on xs)
theorem maxOnQ_eq_if_h4 :
    ∀ {β : Type u_1} {α : Type u_2} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {xs : List α},
      List.maxOn? f xs = if h : xs ≠ [] then Option.some (List.maxOn f xs h) else Option.none :=
  by
    intro β α _ _ f xs
    cases xs with
    | nil => rfl
    | cons z zs => simp only [ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceDIte]; rfl


/-! ## `Lex`: removable -/

-- Derivability of `Asymm α` in `map_le` (helper, not a verdict).
theorem asymm_of_strictMono {α : Type u_1} {β : Type u_2} [LT α] [LT β]
    [Std.Asymm (· < · : β → β → Prop)] {f : α → β} (hf : ∀ x y : α, x < y → f x < f y) :
    Std.Asymm (· < · : α → α → Prop) :=
  ⟨fun a b hab hba => Std.Asymm.asymm _ _ (hf _ _ hab) (hf _ _ hba)⟩


-- `List.not_lt_of_cons_le_cons` (`i₁`, idx 2): a :: l₁ ≤ b :: l₂ means ¬ (b :: l₂ < a :: l₁), and b < a would give that by Lex.rel; no law needed
theorem not_lt_of_cons_le_cons_h2 :
    ∀ {α : Type u_1} [inst : LT α] [i₂ : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {a b : α} {l₁ l₂ : List α},
      a :: l₁ ≤ b :: l₂ → ¬b < a :=
  fun h hba => h (List.Lex.rel hba)

-- `List.not_lt_of_cons_le_cons` (`i₂`, idx 3): a :: l₁ ≤ b :: l₂ means ¬ (b :: l₂ < a :: l₁), and b < a would give that by Lex.rel; no law needed
theorem not_lt_of_cons_le_cons_h3 :
    ∀ {α : Type u_1} [inst : LT α] [i₁ : Std.Asymm fun (x1 x2 : α) => x1 < x2] {a b : α} {l₁ l₂ : List α},
      a :: l₁ ≤ b :: l₂ → ¬b < a :=
  fun h hba => h (List.Lex.rel hba)

-- `List.le_of_cons_le_cons` (`i₀`, idx 2): l₂ < l₁ gives a :: l₂ < a :: l₁ by Lex.cons; no law needed
theorem le_of_cons_le_cons_h2 :
    ∀ {α : Type u_1} [inst : LT α] [i₁ : Std.Asymm fun (x1 x2 : α) => x1 < x2]
      [i₂ : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {a : α} {l₁ l₂ : List α}, a :: l₁ ≤ a :: l₂ → l₁ ≤ l₂ :=
  fun h h' => h (List.Lex.cons h')

-- `List.le_of_cons_le_cons` (`i₁`, idx 3): l₂ < l₁ gives a :: l₂ < a :: l₁ by Lex.cons; no law needed
theorem le_of_cons_le_cons_h3 :
    ∀ {α : Type u_1} [inst : LT α] [i₀ : Std.Irrefl fun (x1 x2 : α) => x1 < x2]
      [i₂ : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {a : α} {l₁ l₂ : List α}, a :: l₁ ≤ a :: l₂ → l₁ ≤ l₂ :=
  fun h h' => h (List.Lex.cons h')

-- `List.le_of_cons_le_cons` (`i₂`, idx 4): l₂ < l₁ gives a :: l₂ < a :: l₁ by Lex.cons; no law needed
theorem le_of_cons_le_cons_h4 :
    ∀ {α : Type u_1} [inst : LT α] [i₀ : Std.Irrefl fun (x1 x2 : α) => x1 < x2] [i₁ : Std.Asymm fun (x1 x2 : α) => x1 < x2]
      {a : α} {l₁ l₂ : List α}, a :: l₁ ≤ a :: l₂ → l₁ ≤ l₂ :=
  fun h h' => h (List.Lex.cons h')

-- `List.map_le` (`inst`, idx 4): derivable: strict monotonicity of f and Asymm on β give Asymm on α; the proof (lt_of_map_lt) uses only Trichotomous on α and Asymm on β
theorem map_le_h4 :
    ∀ {α : Type u_1} {β : Type u_2} [inst : LT α] [inst_1 : LT β] [Std.Trichotomous fun (x1 x2 : α) => x1 < x2]
      [Std.Asymm fun (x1 x2 : β) => x1 < x2] [Std.Trichotomous fun (x1 x2 : β) => x1 < x2] {l₁ l₂ : List α} {f : α → β},
      (∀ (x y : α), x < y → f x < f y) → l₁ ≤ l₂ → List.map f l₁ ≤ List.map f l₂ :=
  fun hf h h' => h (lt_of_map_lt hf h')

-- `List.map_le` (`inst`, idx 7): map f l₂ < map f l₁ → l₂ < l₁ needs only Trichotomous on α and Asymm on β (lt_of_map_lt)
theorem map_le_h7 :
    ∀ {α : Type u_1} {β : Type u_2} [inst : LT α] [inst_1 : LT β] [Std.Asymm fun (x1 x2 : α) => x1 < x2]
      [Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [Std.Asymm fun (x1 x2 : β) => x1 < x2] {l₁ l₂ : List α} {f : α → β},
      (∀ (x y : α), x < y → f x < f y) → l₁ ≤ l₂ → List.map f l₁ ≤ List.map f l₂ :=
  fun hf h h' => h (lt_of_map_lt hf h')


/-! ## `BEq`: removable -/


-- `List.Perm.count` (`inst`, idx 2): count a = countP (· == a), and countP is invariant under Perm for any predicate
theorem Perm_count_h2 :
    ∀ {α : Type u_1} [inst : BEq α] {l₁ l₂ : List α}, l₁.Perm l₂ → ∀ (a : α), List.count a l₁ = List.count a l₂ :=
  fun h a => h.countP_eq _

-- `List.Pairwise.erase` (`inst`, idx 3): l.erase a is a sublist of l for any BEq
theorem Pairwise_erase_h3 :
    ∀ {α : Type u_1} [inst : BEq α] {p : α → α → Prop} {l : List α} (a : α), List.Pairwise p l → List.Pairwise p (l.erase a) :=
  fun a h => h.sublist List.erase_sublist

-- `List.Nodup.erase` (`inst`, idx 3): l.erase a is a sublist of l for any BEq
theorem Nodup_erase_h3 :
    ∀ {α : Type u_1} [inst : BEq α] {l : List α} (a : α), l.Nodup → (l.erase a).Nodup :=
  fun a h => h.sublist List.erase_sublist

-- `List.erase_eq_eraseIdx_of_idxOf` (`inst`, idx 2): erase and idxOf both test x == a, so they stop at the same position for any BEq
theorem erase_eq_eraseIdx_of_idxOf_h2 :
    ∀ {α : Type u_1} [inst : BEq α] {l : List α} {a : α} {i : Nat}, List.idxOf a l = i → l.erase a = l.eraseIdx i :=
  by
    intro α _ l a i h
    subst h
    induction l with
    | nil => rfl
    | cons x xs ih => by_cases hx : (x == a) = true <;> simp [List.erase_cons, List.idxOf_cons, hx, ih]

-- `List.replace_replicate_ne` (`inst`, idx 3): replace b c tests b == x, which is false for every x = a by hypothesis; no law needed
theorem replace_replicate_ne_h3 :
    ∀ {α : Type u_1} [inst : BEq α] {n : Nat} {a b c : α},
      (!b == a) = Bool.true → (List.replicate n a).replace b c = List.replicate n a :=
  by
    intro α _ n a b c h
    have h' : (b == a) = false := by simpa using h
    induction n with
    | zero => rfl
    | succ n ih => simp only [List.replicate_succ, List.replace, h', ih]

-- `List.Perm.insert` (`inst`, idx 2): contains is invariant under Perm for any BEq (List.Perm.contains_eq), so both inserts take the same branch
theorem Perm_insert_h2 :
    ∀ {α : Type u_1} [inst : BEq α] (a : α) {l₁ l₂ : List α}, l₁.Perm l₂ → (List.insert a l₁).Perm (List.insert a l₂) :=
  by
    intro α _ a l₁ l₂ h
    unfold List.insert
    rw [h.contains_eq]
    split
    · exact h
    · exact h.cons a

-- `List.length_le_length_insert` (`inst`, idx 2): insert a l is l or a :: l
theorem length_le_length_insert_h2 :
    ∀ {α : Type u_1} [inst : BEq α] {l : List α} {a : α}, l.length ≤ (List.insert a l).length :=
  by
    intro α _ l a
    unfold List.insert
    split <;> simp

-- `List.length_insert_pos` (`inst`, idx 2): insert a l is l (then l contains a, so l ≠ []) or a :: l
theorem length_insert_pos_h2 :
    ∀ {α : Type u_1} [inst : BEq α] {l : List α} {a : α}, 0 < (List.insert a l).length :=
  by
    intro α _ l a
    unfold List.insert
    split
    · rename_i h
      cases l with
      | nil => simp at h
      | cons => simp
    · simp

-- `List.mem_insert_of_mem` (`inst`, idx 2): insert b l is l or b :: l
theorem mem_insert_of_mem_h2 :
    ∀ {α : Type u_1} [inst : BEq α] {a b : α} {l : List α}, a ∈ l → a ∈ List.insert b l :=
  by
    intro α _ a b l h
    unfold List.insert
    split
    · exact h
    · exact List.mem_cons_of_mem _ h

-- `List.insert_replicate_ne` (`inst`, idx 2): contains b tests b == x, false for every x = a by hypothesis, so insert conses
theorem insert_replicate_ne_h2 :
    ∀ {α : Type u_1} [inst : BEq α] {n : Nat} {a b : α},
      (!b == a) = Bool.true → List.insert b (List.replicate n a) = b :: List.replicate n a :=
  by
    intro α _ n a b h
    have h' : (b == a) = false := by simpa using h
    unfold List.insert
    rw [contains_replicate_of_beq_false h' n]
    rfl

-- `List.count_erase_self` (`inst`, idx 2): erase a removes the first x with x == a, which count a counts; for any BEq
theorem count_erase_self_h2 :
    ∀ {α : Type u_1} [inst : BEq α] {a : α} {l : List α}, List.count a (l.erase a) = List.count a l - 1 :=
  by
    intro α _ a l
    induction l with
    | nil => rfl
    | cons x xs ih => by_cases hx : (x == a) = true <;> simp [List.erase_cons, List.count_cons, hx, ih]

-- `List.eq_or_mem_of_mem_insert` (`inst`, idx 2): insert b l is l or b :: l
theorem eq_or_mem_of_mem_insert_h2 :
    ∀ {α : Type u_1} [inst : BEq α] {b a : α} {l : List α}, a ∈ List.insert b l → a = b ∨ a ∈ l :=
  by
    intro α _ b a l h
    unfold List.insert at h
    split at h
    · exact .inr h
    · exact List.mem_cons.mp h

-- `List.count_replicate` (`inst`, idx 2): count a = countP (· == a) and countP_replicate needs no law
theorem count_replicate_h2 :
    ∀ {α : Type u_1} [inst : BEq α] {a b : α} {n : Nat},
      List.count a (List.replicate n b) = if (b == a) = Bool.true then n else 0 :=
  by
    intro α _ a b n
    exact List.countP_replicate

-- `List.le_length_erase` (`inst`, idx 2): erase removes at most one element
theorem le_length_erase_h2 :
    ∀ {α : Type u_1} [inst : BEq α] {a : α} {l : List α}, l.length - 1 ≤ (l.erase a).length :=
  by
    intro α _ a l
    induction l with
    | nil => simp
    | cons x xs ih => by_cases hx : (x == a) = true <;> simp [List.erase_cons, hx] <;> omega


/-! ## Sums, products and folds: removable -/


-- `List.sum_reverse` (`inst`, idx 5): with + associative and commutative, both sides are the sum of all elements and 0 in any order; the identity law is not needed
theorem sum_reverse_h5 :
    ∀ {α : Type u_1} [inst : Zero α] [inst_1 : Add α] [Std.Associative fun (x1 x2 : α) => x1 + x2]
      [Std.Commutative fun (x1 x2 : α) => x1 + x2] (xs : List α), xs.reverse.sum = xs.sum :=
  by
    intro α _ _ _ _ xs
    induction xs with
    | nil => rfl
    | cons x xs ih => rw [List.reverse_cons, sum_append_singleton, ih]; rfl

-- `List.prod_reverse` (`inst`, idx 5): with * associative and commutative, both sides are the product of all elements and 1 in any order; the identity law is not needed
theorem prod_reverse_h5 :
    ∀ {α : Type u_1} [inst : One α] [inst_1 : Mul α] [Std.Associative fun (x1 x2 : α) => x1 * x2]
      [Std.Commutative fun (x1 x2 : α) => x1 * x2] (xs : List α), xs.reverse.prod = xs.prod :=
  by
    intro α _ _ _ _ xs
    induction xs with
    | nil => rfl
    | cons x xs ih => rw [List.reverse_cons, prod_append_singleton, ih]; rfl

-- `List.foldl_max_eq_max` (`inst`, idx 2): l ≠ [], so foldl max a (x :: t) = foldl max (max a x) t = max a (foldl max x t) by associativity alone (List.foldl_assoc)
theorem foldl_max_eq_max_h2 :
    ∀ {α : Type u_1} [inst : Max α] [Std.Associative (Max.max : α → α → α)] {l : List α} (hl : l ≠ []) {a : α},
      List.foldl Max.max a l = Max.max a (l.max hl) :=
  by
    intro α _ _ l hl a
    match l, hl with
    | x :: t, _ => exact List.foldl_assoc

-- `List.foldl_min_eq_min` (`inst`, idx 2): l ≠ [], so foldl min a (x :: t) = min a (foldl min x t) by associativity alone (List.foldl_assoc)
theorem foldl_min_eq_min_h2 :
    ∀ {α : Type u_1} [inst : Min α] [Std.Associative (Min.min : α → α → α)] {l : List α} (hl : l ≠ []) {a : α},
      List.foldl Min.min a l = Min.min a (l.min hl) :=
  by
    intro α _ _ l hl a
    match l, hl with
    | x :: t, _ => exact List.foldl_assoc

