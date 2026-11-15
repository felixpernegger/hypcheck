import Lean

/-!
Hand resolution of the 126 hypotheses in `Init.Data.List.*` (Attach, Monadic, Sort.Lemmas, Perm,
Lex, MapIdx, Pairwise, Lemmas, Nat.InsertIdx, Nat.Pairwise, FinRange, OfFn, Scan.Lemmas, Find,
MinMax, MinMaxOn, MinMaxIdx, ToArray; cluster `List`, hand pass 5) that `HypCheck.lean` left
unresolved. For each hypothesis `hᵢ` of theorem `T`, this file proves `T'` (removable), `¬T'`
(necessary), or, for a dependent hypothesis, `∀ indep, Hᵢ` resp. `¬∀ indep, Hᵢ`.

Removable (17):
* `[LawfulMonad m]` (14): `mapM_map`, `foldrM_map`, `mapM_subtype`, `filterMapM_subtype`,
  `flatMapM_subtype`, `foldrM_subtype`, `mapM_unattach`, `filterMapM_unattach`, `flatMapM_unattach`,
  `foldrM_unattach`, `foldrM_attachWith`, `scanlM_map`, `scanrM_map`, `Fin.foldrM_eq_foldrM_finRange`:
  both sides run the same loop (`mapM.loop`, `filterMapM.loop`, `flatMapM.loop`, `foldlM` on the
  reverse, the private `scanAuxM.go` and `Fin.foldrM.loop`) over `l.map f` resp. `l` with the
  function composed with `f`, so they are equal step by step in any monad.
* `insertIdx_comm` (`j ≤ l.length`) and `insertIdx_eraseIdx_of_le` (`i < as.length`): out of range,
  `insertIdx`/`eraseIdx` are no-ops on both sides.
* `head_insert` (`w : l.insert a ≠ []`, dependent): always true, without `LawfulBEq`.

Necessary (109): 52 dependent ones (the `pmap`/`attachWith` side conditions `∀ a ∈ l, p a`, index
bounds, `xs ≠ []`, equations used in casts), refuted as `∀ indep, Hᵢ` with `p := False` and a
one-element list etc.; the other 57 by counterexamples with the models below.

Models (in `RestListHand`):
* `SynM`: a "syntax" monad, value plus the tree of `pure`/`bind`/`map`/effects that built it. No
  monad law holds, but programs of the same shape are equal (`foldrM_cons`, `ofFnM_succ`,
  `ofFnM_succ_last`, `forIn'_pure_yield_eq_foldl`, `forIn'_eq_foldlM`).
* `TyM`: values are numbers, `bind x _ = x`, `pure _ = 0`, and `map` returns `1` exactly when its
  result type is `ForInStep Bool` (classical type case). Refutes `forIn_yield_eq_foldlM` and
  `forIn'_yield_eq_foldlM`, whose sides differ only in mapping into `ForInStep β` vs `β`.
* `rps` (total, not transitive), `lt01`, `le00` (transitive, not total), `leF` (usual) on `Fin 3`
  for the `mergeSort`/`merge` lemmas (evaluated with `simp`, since `mergeSort` is well-founded).
* `E0` (`Nat` with empty `<`), `U1` (one element, empty `<`) for the `Lex` lemmas; `BB` (pairs of
  booleans, componentwise order, `max` = componentwise or; a non-linear lattice) for
  `max?_eq_some_iff_legacy`; `PS` (one round of disjoint adjacent swaps, closed under `Perm.nil`,
  `cons`, `swap'` but not `trans`) for `Perm.recOnSwap'`.

Run with the lean4 repo's stage1 binary: `lean checks/RestListHand.lean` (imports `Lean` for the
`priv%` elaborator that names the private loops in helper lemmas).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u u_1 u_2 u_3 u_4

namespace RestListHand

open Lean Elab Term Meta in
/-- `priv% M n`: the private constant `n` of module `M` (to state helper lemmas about the private
`List.scanAuxM.go`; not used in any verdict statement). -/
elab "priv%" mod:ident n:ident : term => do
  let c := mkPrivateNameCore mod.getId n.getId
  unless (← getEnv).contains c do throwError "unknown private constant {c}"
  mkConstWithFreshMVarLevels c

/-! ## Models -/

/-- Syntax trees of monadic programs: `p` = `pure`, `b` = `bind`, `m` = `map`, `e n` = an effect. -/
inductive Tr where
  | p | b (x y : Tr) | m (x : Tr) | e (n : Nat)
  deriving DecidableEq

/-- The "syntax" monad: a value together with the tree of operations that produced it. No monad law
holds (`pure a >>= f` has tree `b p _`, `x >>= pure` has tree `b _ p`, `f <$> x` has tree `m _`,
`x >>= pure ∘ f` has tree `b _ p`), but two programs built from the same operations in the same
shape are equal. -/
def SynM (α : Type) : Type := Tr × α

instance : Monad SynM where
  pure a := (.p, a)
  bind x f := (.b x.1 (f x.2).1, (f x.2).2)
  map f x := (.m x.1, f x.2)

instance [DecidableEq α] : DecidableEq (SynM α) := inferInstanceAs (DecidableEq (Tr × α))

/-- An effect `e n` returning `a`. -/
def ev (n : Nat) (a : α) : SynM α := (.e n, a)

/-- A monad whose values are numbers and whose `map` looks at its result type: `f <$> x` is `1` if
the result type is `ForInStep Bool`, else `x`; `bind x _ = x`, `pure _ = 0`. Lawfulness fails
(`pure a >>= f ≠ f a`, `id <$> x ≠ x` at `ForInStep Bool`); it separates programs that only differ
in the type they `map` into. -/
def TyM (_ : Type) : Type := Nat

noncomputable instance : Monad TyM where
  pure _ := (0 : Nat)
  bind x _ := x
  map {_ β} _ x := @ite Nat (β = ForInStep Bool) (Classical.propDecidable _) (1 : Nat) x

theorem bool_ne_forInStep : ¬ (Bool = ForInStep Bool) := by
  intro h
  have key : ∀ x y z : Bool, x = y ∨ y = z ∨ x = z := by decide
  have key' : ∀ x y z : ForInStep Bool, x = y ∨ y = z ∨ x = z :=
    cast (congrArg (fun T : Type => ∀ x y z : T, x = y ∨ y = z ∨ x = z) h) key
  have := key' (.done false) (.done true) (.yield false)
  simp at this

/-- Rock–paper–scissors `≤` on `Fin 3`: `a ≤ b ↔ b - a ≡ 0 or 1 (mod 3)`. Total, not transitive. -/
def rps (a b : Fin 3) : Bool := (b.val + 3 - a.val) % 3 ≤ 1

/-- `le a b ↔ a = 0 ∧ b = 1` on `Fin 3`: transitive (vacuously), not total. -/
def lt01 (a b : Fin 3) : Bool := a == 0 && b == 1

/-- `le a b ↔ a = 0 ∧ b = 0` on `Fin 3`: transitive, not total. -/
def le00 (a b : Fin 3) : Bool := a == 0 && b == 0

/-- The usual `≤` on `Fin 3` as a `Bool` relation. -/
def leF (a b : Fin 3) : Bool := decide (a ≤ b)

/-- `Nat` with the empty `<`. -/
def E0 := Nat
instance : LT E0 := ⟨fun _ _ => False⟩
instance : DecidableEq E0 := inferInstanceAs (DecidableEq Nat)
instance : DecidableLT E0 := fun _ _ => instDecidableFalse
instance : OfNat E0 n := ⟨(n : Nat)⟩

/-- A one-element type with the empty `<` (trichotomous since all elements are equal). -/
def U1 := Unit
instance : LT U1 := ⟨fun _ _ => False⟩
instance : DecidableEq U1 := inferInstanceAs (DecidableEq Unit)
instance : DecidableLT U1 := fun _ _ => instDecidableFalse
instance : Std.Trichotomous (· < · : U1 → U1 → Prop) := ⟨fun _ _ _ _ => rfl⟩
def U1.star : U1 := ()

/-- Pairs of booleans ordered componentwise, `max` = componentwise `||`: a lattice that is not
linear, so `max a b` need not be `a` or `b`. -/
structure BB where
  x : Bool
  y : Bool
  deriving DecidableEq
instance : LE BB := ⟨fun a b => (!a.x || b.x) = true ∧ (!a.y || b.y) = true⟩
instance : DecidableLE BB := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : Max BB := ⟨fun a b => ⟨a.x || b.x, a.y || b.y⟩⟩
instance : Std.Antisymm (· ≤ · : BB → BB → Prop) := ⟨by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩; revert a1 a2 b1 b2; decide⟩
theorem BB.le_refl : ∀ a : BB, a ≤ a := by intro ⟨a1, a2⟩; revert a1 a2; decide
theorem BB.max_le_iff : ∀ a b c : BB, max b c ≤ a ↔ b ≤ a ∧ c ≤ a := by
  intro ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨c1, c2⟩; revert a1 a2 b1 b2 c1 c2; decide

/-- `PS l₁ l₂`: `l₂` arises from `l₁` by swapping some disjoint pairs of adjacent entries. Closed
under `Perm.nil`, `Perm.cons` and `Perm.swap'`, but not under `Perm.trans`. -/
def PS : List Nat → List Nat → Bool
  | [], [] => true
  | a :: c :: l, b :: d :: l' => (a == b && PS (c :: l) (d :: l')) || (a == d && c == b && PS l l')
  | a :: l, b :: l' => a == b && PS l l'
  | _, _ => false

theorem PS_cons (x : Nat) (l₁ l₂ : List Nat) (h : PS l₁ l₂ = true) : PS (x :: l₁) (x :: l₂) = true := by
  cases l₁ <;> cases l₂ <;> simp_all [PS]

theorem PS_swap (x y : Nat) (l₁ l₂ : List Nat) (h : PS l₁ l₂ = true) :
    PS (y :: x :: l₁) (x :: y :: l₂) = true := by
  simp [PS, h]

/-! ## Helper lemmas for the removable `[LawfulMonad m]` verdicts (no monad laws used) -/

theorem foldrM_map' {m : Type u_1 → Type u_2} {β₁ : Type u_3} {β₂ : Type u_4} {α : Type u_1} [Monad m]
    {f : β₁ → β₂} {g : β₂ → α → m α} {l : List β₁} {init : α} :
    List.foldrM g init (List.map f l) = List.foldrM (fun x y => g (f x) y) init l := by
  unfold List.foldrM
  rw [← List.map_reverse, List.foldlM_map]

theorem foldrM_append_singleton {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [Monad m]
    (f : α → β → m β) (x : β) (l : List α) (a : α) :
    List.foldrM f x (l ++ [a]) = f a x >>= fun s => List.foldrM f s l := by
  unfold List.foldrM
  rw [List.reverse_append]
  rfl

theorem mapM_loop_map {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_4} {γ : Type u_1} [Monad m]
    (f : α → β) (g : β → m γ) (l : List α) (acc : List γ) :
    List.mapM.loop g (l.map f) acc = List.mapM.loop (g ∘ f) l acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih =>
    show g (f a) >>= _ = g (f a) >>= _
    congr 1; funext r; exact ih _

theorem mapM_map' {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_4} {γ : Type u_1} [Monad m]
    {f : α → β} {g : β → m γ} {l : List α} : List.mapM g (List.map f l) = List.mapM (g ∘ f) l :=
  mapM_loop_map f g l []

theorem filterMapM_loop_map {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_4} {γ : Type u_1}
    [Monad m] (f : α → β) (g : β → m (Option γ)) (l : List α) (acc : List γ) :
    List.filterMapM.loop g (l.map f) acc = List.filterMapM.loop (g ∘ f) l acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih =>
    show g (f a) >>= _ = g (f a) >>= _
    congr 1; funext r; cases r <;> exact ih _

theorem filterMapM_map' {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_4} {γ : Type u_1}
    [Monad m] {f : α → β} {g : β → m (Option γ)} {l : List α} :
    List.filterMapM g (List.map f l) = List.filterMapM (g ∘ f) l :=
  filterMapM_loop_map f g l []

theorem flatMapM_loop_map {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_4} {γ : Type u_1}
    [Monad m] (f : α → β) (g : β → m (List γ)) (l : List α) (acc : List (List γ)) :
    List.flatMapM.loop g (l.map f) acc = List.flatMapM.loop (g ∘ f) l acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih =>
    show g (f a) >>= _ = g (f a) >>= _
    congr 1; funext r; exact ih _

theorem flatMapM_map' {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_4} {γ : Type u_1}
    [Monad m] {f : α → β} {g : β → m (List γ)} {l : List α} :
    List.flatMapM g (List.map f l) = List.flatMapM (g ∘ f) l :=
  flatMapM_loop_map f g l []

theorem scanAuxM_go_map {m : Type u_1 → Type u_2} [Monad m] {α₁ : Type u_3} {α₂ : Type u_4} {β : Type u_1}
    (f : α₁ → α₂) (g : β → α₂ → m β) (as : List α₁) (last : β) (acc : List β) :
    (priv% Init.Data.List.Scan.Basic List.scanAuxM.go) g (as.map f) last acc
      = (priv% Init.Data.List.Scan.Basic List.scanAuxM.go) (fun b a => g b (f a)) as last acc := by
  induction as generalizing last acc with
  | nil => rfl
  | cons a as ih =>
    show g last (f a) >>= _ = g last (f a) >>= _
    congr 1; funext r; exact ih ..

theorem finFoldrM_loop {m : Type u_1 → Type u_2} {α : Type u_1} [Monad m] {n : Nat}
    (f : Fin n → α → m α) (i : Nat) (h : i ≤ n) (x : α) :
    (priv% Init.Data.Fin.Fold Fin.foldrM.loop) n f ⟨i, h⟩ x
      = List.foldrM f x ((List.finRange i).map (Fin.castLE h)) := by
  induction i generalizing x with
  | zero => rw [(priv% Init.Data.Fin.Fold Fin.foldrM_loop_zero)]; simp
  | succ i ih =>
    rw [(priv% Init.Data.Fin.Fold Fin.foldrM_loop_succ) f x h, List.finRange_succ_last,
      List.map_append, List.map_map, List.map_singleton, foldrM_append_singleton]
    congr 1
    funext s
    exact ih (Nat.le_of_succ_le h) s

end RestListHand
open RestListHand


/-! ## `Init.Data.List.Attach` -/

-- `List.pmap_cons` (`h`, idx 6): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and `a :: l = [0]`
theorem pmap_cons_h6 :
    ¬ (∀ {α : Type} {P : α → Prop} {a : α} {l : List α} (b : α), b ∈ a :: l → P b) :=
  fun H0 => H0 (α := Nat) (P := fun _ => False) (a := 0) (l := []) 0 (by simp)

-- `List.pmap_congr_left` (`H₁`, idx 7): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem pmap_congr_left_h7 :
    ¬ (∀ {α : Type} {p : α → Prop} (l : List α) (a : α), a ∈ l → p a) :=
  fun H0 => H0 (α := Nat) (p := fun _ => False) (l := [0]) 0 (by simp)

-- `List.pmap_congr_left` (`H₂`, idx 8): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem pmap_congr_left_h8 :
    ¬ (∀ {α : Type} {q : α → Prop} (l : List α) (a : α), a ∈ l → q a) :=
  fun H0 => H0 (α := Nat) (q := fun _ => False) (l := [0]) 0 (by simp)

-- `List.pmap_congr_left` (`h`, idx 9): `f = 0`, `g = 1`, `l = [0]`
theorem pmap_congr_left_h9 :
    ¬ (∀ {α : Type} {β : Type} {p q : α → Prop} {f : (a : α) → p a → β} {g : (a : α) → q a → β} (l : List α)
        {H₁ : ∀ (a : α), a ∈ l → p a} {H₂ : ∀ (a : α), a ∈ l → q a}, List.pmap f l H₁ = List.pmap g l H₂) :=
  fun H0 => absurd (H0 (α := Nat) (β := Nat) (p := fun _ => True) (q := fun _ => True) (f := fun _ _ => 0)
      (g := fun _ _ => 1) [0] (H₁ := fun _ _ => trivial) (H₂ := fun _ _ => trivial)) (by decide)

-- `List.map_pmap` (`H`, idx 7): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem map_pmap_h7 :
    ¬ (∀ {α : Type} {p : α → Prop} {l : List α} (a : α), a ∈ l → p a) :=
  fun H0 => H0 (α := Nat) (p := fun _ => False) (l := [0]) 0 (by simp)

-- `List.pmap_map` (`H`, idx 7): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and `f = id`, `l = [0]`
theorem pmap_map_h7 :
    ¬ (∀ {β : Type} {α : Type} {p : β → Prop} {f : α → β} {l : List α} (a : β), a ∈ List.map f l → p a) :=
  fun H0 => H0 (β := Nat) (α := Nat) (p := fun _ => False) (f := id) (l := [0]) 0 (by simp)

-- `List.pmap_eq_map_attach` (`H`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem pmap_eq_map_attach_h5 :
    ¬ (∀ {α : Type} {p : α → Prop} {l : List α} (a : α), a ∈ l → p a) :=
  fun H0 => H0 (α := Nat) (p := fun _ => False) (l := [0]) 0 (by simp)

-- `List.mem_pmap` (`H`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem mem_pmap_h5 :
    ¬ (∀ {α : Type} {p : α → Prop} {l : List α} (a : α), a ∈ l → p a) :=
  fun H0 => H0 (α := Nat) (p := fun _ => False) (l := [0]) 0 (by simp)

-- `List.mem_pmap_of_mem` (`H`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem mem_pmap_of_mem_h5 :
    ¬ (∀ {α : Type} {p : α → Prop} {l : List α} (a : α), a ∈ l → p a) :=
  fun H0 => H0 (α := Nat) (p := fun _ => False) (l := [0]) 0 (by simp)

-- `List.mem_pmap_of_mem` (`h`, idx 7): dependent; `∀ l a, a ∈ l` fails for `l = []`
theorem mem_pmap_of_mem_h7 :
    ¬ (∀ {α : Type} {l : List α} {a : α}, a ∈ l) :=
  fun H0 => absurd (H0 (α := Nat) (l := []) (a := 0)) (by simp)

-- `List.length_pmap` (`H`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem length_pmap_h5 :
    ¬ (∀ {α : Type} {p : α → Prop} {l : List α} (a : α), a ∈ l → p a) :=
  fun H0 => H0 (α := Nat) (p := fun _ => False) (l := [0]) 0 (by simp)

-- `List.pmap_eq_nil_iff` (`H`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem pmap_eq_nil_iff_h5 :
    ¬ (∀ {α : Type} {p : α → Prop} {l : List α} (a : α), a ∈ l → p a) :=
  fun H0 => H0 (α := Nat) (p := fun _ => False) (l := [0]) 0 (by simp)

-- `List.pmap_ne_nil_iff` (`H`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem pmap_ne_nil_iff_h5 :
    ¬ (∀ {α : Type} {P : α → Prop} {xs : List α} (a : α), a ∈ xs → P a) :=
  fun H0 => H0 (α := Nat) (P := fun _ => False) (xs := [0]) 0 (by simp)

-- `List.pmap_eq_self` (`hp`, idx 3): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem pmap_eq_self_h3 :
    ¬ (∀ {α : Type} {l : List α} {p : α → Prop} (a : α), a ∈ l → p a) :=
  fun H0 => H0 (α := Nat) (p := fun _ => False) (l := [0]) 0 (by simp)

-- `List.getElem?_pmap` (`h`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem getElemQ_pmap_h5 :
    ¬ (∀ {α : Type} {p : α → Prop} {l : List α} (a : α), a ∈ l → p a) :=
  fun H0 => H0 (α := Nat) (p := fun _ => False) (l := [0]) 0 (by simp)

-- `List.getElem_pmap` (`h`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem getElem_pmap_h5 :
    ¬ (∀ {α : Type} {p : α → Prop} {l : List α} (a : α), a ∈ l → p a) :=
  fun H0 => H0 (α := Nat) (p := fun _ => False) (l := [0]) 0 (by simp)

-- `List.getElem_pmap` (`hn`, idx 7): dependent (index bound); `∀ … i, i < (pmap f l h).length` fails for `l = []`, `i = 0`
theorem getElem_pmap_h7 :
    ¬ (∀ {α : Type} {β : Type} {p : α → Prop} (f : (a : α) → p a → β) {l : List α} (h : ∀ (a : α), a ∈ l → p a)
        {i : Nat}, i < (List.pmap f l h).length) :=
  fun H0 => absurd (H0 (α := Nat) (β := Nat) (p := fun _ => True) (fun a _ => a) (l := []) (fun _ _ => trivial)
      (i := 0)) (by simp)

-- `List.pmap_attach` (`H`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and `l = [0]`
theorem pmap_attach_h5 :
    ¬ (∀ {α : Type} {l : List α} {p : { x : α // x ∈ l } → Prop} (a : { x : α // x ∈ l }), a ∈ l.attach → p a) :=
  fun H0 => H0 (α := Nat) (l := [0]) (p := fun _ => False) ⟨0, by simp⟩ (by simp)

-- `List.pmap_attachWith` (`H₁`, idx 6): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem pmap_attachWith_h6 :
    ¬ (∀ {α : Type} {q : α → Prop} {l : List α} (x : α), x ∈ l → q x) :=
  fun H0 => H0 (α := Nat) (q := fun _ => False) (l := [0]) 0 (by simp)

-- `List.pmap_attachWith` (`H₂`, idx 7): dependent; `∀ indep, H₂` fails for `q := True`, `p := False`, `l = [0]`
theorem pmap_attachWith_h7 :
    ¬ (∀ {α : Type} {q : α → Prop} {l : List α} {p : { x : α // q x } → Prop} (H₁ : ∀ (x : α), x ∈ l → q x)
        (a : { x : α // q x }), a ∈ l.attachWith q H₁ → p a) :=
  fun H0 => H0 (α := Nat) (q := fun _ => True) (l := [0]) (p := fun _ => False) (fun _ _ => trivial)
      ⟨0, trivial⟩ (by simp)

-- `List.head?_pmap` (`H`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem headQ_pmap_h5 :
    ¬ (∀ {α : Type} {P : α → Prop} {xs : List α} (a : α), a ∈ xs → P a) :=
  fun H0 => H0 (α := Nat) (P := fun _ => False) (xs := [0]) 0 (by simp)

-- `List.head_pmap` (`H`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem head_pmap_h5 :
    ¬ (∀ {α : Type} {P : α → Prop} {xs : List α} (a : α), a ∈ xs → P a) :=
  fun H0 => H0 (α := Nat) (P := fun _ => False) (xs := [0]) 0 (by simp)

-- `List.head_pmap` (`h`, idx 6): dependent; `∀ … xs H, pmap f xs H ≠ []` fails for `xs = []`
theorem head_pmap_h6 :
    ¬ (∀ {α : Type} {β : Type} {P : α → Prop} {f : (a : α) → P a → β} {xs : List α} (H : ∀ (a : α), a ∈ xs → P a),
        List.pmap f xs H ≠ []) :=
  fun H0 => H0 (α := Nat) (β := Nat) (P := fun _ => True) (f := fun a _ => a) (xs := [])
      (fun _ _ => trivial) rfl

-- `List.tail_pmap` (`H`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem tail_pmap_h5 :
    ¬ (∀ {α : Type} {P : α → Prop} {xs : List α} (a : α), a ∈ xs → P a) :=
  fun H0 => H0 (α := Nat) (P := fun _ => False) (xs := [0]) 0 (by simp)

-- `List.foldl_pmap` (`H`, idx 6): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem foldl_pmap_h6 :
    ¬ (∀ {α : Type} {l : List α} {P : α → Prop} (a : α), a ∈ l → P a) :=
  fun H0 => H0 (α := Nat) (P := fun _ => False) (l := [0]) 0 (by simp)

-- `List.foldr_pmap` (`H`, idx 6): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem foldr_pmap_h6 :
    ¬ (∀ {α : Type} {l : List α} {P : α → Prop} (a : α), a ∈ l → P a) :=
  fun H0 => H0 (α := Nat) (P := fun _ => False) (l := [0]) 0 (by simp)

-- `List.pmap_pmap` (`H₁`, idx 8): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem pmap_pmap_h8 :
    ¬ (∀ {α : Type} {p : α → Prop} {l : List α} (a : α), a ∈ l → p a) :=
  fun H0 => H0 (α := Nat) (p := fun _ => False) (l := [0]) 0 (by simp)

-- `List.pmap_pmap` (`H₂`, idx 9): dependent; `∀ indep, H₂` fails for `p := True`, `q := False`, `g a _ := a`, `l = [0]`
theorem pmap_pmap_h9 :
    ¬ (∀ {α : Type} {β : Type} {p : α → Prop} {q : β → Prop} {g : (a : α) → p a → β} {l : List α}
        (H₁ : ∀ (a : α), a ∈ l → p a) (a : β), a ∈ List.pmap g l H₁ → q a) :=
  fun H0 => H0 (α := Nat) (β := Nat) (p := fun _ => True) (q := fun _ => False) (g := fun a _ => a)
      (l := [0]) (fun _ _ => trivial) 0 (by simp)

-- `List.pmap_append` (`h`, idx 6): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and `l₁ = [0]`, `l₂ = []`
theorem pmap_append_h6 :
    ¬ (∀ {ι : Type} {p : ι → Prop} {l₁ l₂ : List ι} (a : ι), a ∈ l₁ ++ l₂ → p a) :=
  fun H0 => H0 (ι := Nat) (p := fun _ => False) (l₁ := [0]) (l₂ := []) 0 (by simp)

-- `List.pmap_append'` (`h₁`, idx 6): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem pmap_append__h6 :
    ¬ (∀ {α : Type} {p : α → Prop} {l₁ : List α} (a : α), a ∈ l₁ → p a) :=
  fun H0 => H0 (α := Nat) (p := fun _ => False) (l₁ := [0]) 0 (by simp)

-- `List.pmap_append'` (`h₂`, idx 7): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem pmap_append__h7 :
    ¬ (∀ {α : Type} {p : α → Prop} {l₂ : List α} (a : α), a ∈ l₂ → p a) :=
  fun H0 => H0 (α := Nat) (p := fun _ => False) (l₂ := [0]) 0 (by simp)

-- `List.pmap_reverse` (`H`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem pmap_reverse_h5 :
    ¬ (∀ {α : Type} {P : α → Prop} {xs : List α} (a : α), a ∈ xs.reverse → P a) :=
  fun H0 => H0 (α := Nat) (P := fun _ => False) (xs := [0]) 0 (by simp)

-- `List.reverse_pmap` (`H`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem reverse_pmap_h5 :
    ¬ (∀ {α : Type} {P : α → Prop} {xs : List α} (a : α), a ∈ xs → P a) :=
  fun H0 => H0 (α := Nat) (P := fun _ => False) (xs := [0]) 0 (by simp)

-- `List.getLast?_pmap` (`H`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem getLastQ_pmap_h5 :
    ¬ (∀ {α : Type} {P : α → Prop} {xs : List α} (a : α), a ∈ xs → P a) :=
  fun H0 => H0 (α := Nat) (P := fun _ => False) (xs := [0]) 0 (by simp)

-- `List.getLast_pmap` (`H`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem getLast_pmap_h5 :
    ¬ (∀ {α : Type} {P : α → Prop} {xs : List α} (a : α), a ∈ xs → P a) :=
  fun H0 => H0 (α := Nat) (P := fun _ => False) (xs := [0]) 0 (by simp)

-- `List.getLast_pmap` (`h`, idx 6): dependent; `∀ … xs H, pmap f xs H ≠ []` fails for `xs = []`
theorem getLast_pmap_h6 :
    ¬ (∀ {α : Type} {β : Type} {P : α → Prop} {f : (a : α) → P a → β} {xs : List α} (H : ∀ (a : α), a ∈ xs → P a),
        List.pmap f xs H ≠ []) :=
  fun H0 => H0 (α := Nat) (β := Nat) (P := fun _ => True) (f := fun a _ => a) (xs := [])
      (fun _ _ => trivial) rfl

-- `List.countP_pmap` (`H₁`, idx 6): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem countP_pmap_h6 :
    ¬ (∀ {α : Type} {p : α → Prop} {l : List α} (a : α), a ∈ l → p a) :=
  fun H0 => H0 (α := Nat) (p := fun _ => False) (l := [0]) 0 (by simp)

/-! ## `Init.Data.List.Find` -/

-- `List.find?_pmap` (`H`, idx 5): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem findQ_pmap_h5 :
    ¬ (∀ {α : Type} {P : α → Prop} {xs : List α} (a : α), a ∈ xs → P a) :=
  fun H0 => H0 (α := Nat) (P := fun _ => False) (xs := [0]) 0 (by simp)

/-! ## `Init.Data.List.Pairwise` -/

-- `List.Pairwise.forall_of_forall_of_flip` (`h₂`, idx 4): `R = (≥)` on `Nat`, `l = [0, 1]`: `flip R` is `≤`, but `¬ 0 ≥ 1`
theorem Pairwise_forall_of_forall_of_flip_h4 :
    ¬ (∀ {α : Type} {l : List α} {R : α → α → Prop},
        (∀ (x : α), x ∈ l → R x x) → List.Pairwise (flip R) l → ∀ ⦃x : α⦄, x ∈ l → ∀ ⦃y : α⦄, y ∈ l → R x y) :=
  fun H0 => absurd (H0 (α := Nat) (l := [0, 1]) (R := fun a b => b ≤ a) (by decide) (by simp [flip]) (x := 0) (by simp)
      (y := 1) (by simp)) (by decide)

-- `List.pairwise_pmap` (`h`, idx 6): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem pairwise_pmap_h6 :
    ¬ (∀ {β : Type} {p : β → Prop} {l : List β} (x : β), x ∈ l → p x) :=
  fun H0 => H0 (β := Nat) (p := fun _ => False) (l := [0]) 0 (by simp)

-- `List.Pairwise.pmap` (`hl`, idx 4): `R = S = False`, `l = [0, 0]`: `hS` holds vacuously
theorem Pairwise_pmap_h4 :
    ¬ (∀ {α : Type} {R : α → α → Prop} {β : Type} {l : List α} {p : α → Prop} {f : (a : α) → p a → β}
        (h : ∀ (x : α), x ∈ l → p x) {S : β → β → Prop},
        (∀ ⦃x : α⦄ (hx : p x) ⦃y : α⦄ (hy : p y), R x y → S (f x hx) (f y hy)) → List.Pairwise S (List.pmap f l h)) :=
  fun H0 => absurd (H0 (α := Nat) (R := fun _ _ => False) (β := Nat) (l := [0, 0]) (p := fun _ => True)
      (f := fun a _ => a) (fun _ _ => trivial) (S := fun _ _ => False) (fun _ _ _ _ h => h)) (by decide)

-- `List.Pairwise.pmap` (`h`, idx 7): dependent (the conclusion uses the proof); `∀ indep, Hᵢ` fails for `p := fun _ => False` and a one-element list
theorem Pairwise_pmap_h7 :
    ¬ (∀ {α : Type} {l : List α} {p : α → Prop} (x : α), x ∈ l → p x) :=
  fun H0 => H0 (α := Nat) (p := fun _ => False) (l := [0]) 0 (by simp)

-- `List.Pairwise.pmap` (`hS`, idx 9): `R = True`, `S = False`, `l = [0, 0]`
theorem Pairwise_pmap_h9 :
    ¬ (∀ {α : Type} {R : α → α → Prop} {β : Type} {l : List α},
        List.Pairwise R l →
          ∀ {p : α → Prop} {f : (a : α) → p a → β} (h : ∀ (x : α), x ∈ l → p x) {S : β → β → Prop},
            List.Pairwise S (List.pmap f l h)) :=
  fun H0 => absurd (H0 (α := Nat) (R := fun _ _ => True) (β := Nat) (l := [0, 0]) (by decide) (p := fun _ => True)
      (f := fun a _ => a) (fun _ _ => trivial) (S := fun _ _ => False)) (by decide)

/-! ## `Init.Data.List.Perm` -/

-- `List.Perm.recOnSwap'` (`p`, idx 4): dependent; `∀ l₁ l₂, l₁ ~ l₂` fails for `[0]`, `[]`
theorem Perm_recOnSwap__h4 :
    ¬ (∀ {α : Type} {l₁ l₂ : List α}, l₁.Perm l₂) :=
  fun H0 => absurd (H0 (α := Nat) (l₁ := [0]) (l₂ := [])) (by decide)

-- `List.Perm.recOnSwap'` (`nil`, idx 5): `motive l₁ _ _ := l₁ ≠ []` satisfies `cons`, `swap'`, `trans`, fails at `[] ~ []`
theorem Perm_recOnSwap__h5 :
    ¬ (∀ {α : Type} {motive : (l₁ l₂ : List α) → l₁.Perm l₂ → Prop} {l₁ l₂ : List α} (p : l₁.Perm l₂),
        (∀ (x : α) {l₁ l₂ : List α} (h : l₁.Perm l₂), motive l₁ l₂ h → motive (x :: l₁) (x :: l₂) (List.Perm.cons x h)) →
          (∀ (x y : α) {l₁ l₂ : List α} (h : l₁.Perm l₂),
              motive l₁ l₂ h → motive (y :: x :: l₁) (x :: y :: l₂) (List.Perm.swap' x y h)) →
            (∀ {l₁ l₂ l₃ : List α} (h₁ : l₁.Perm l₂) (h₂ : l₂.Perm l₃),
                motive l₁ l₂ h₁ → motive l₂ l₃ h₂ → motive l₁ l₃ (List.Perm.trans h₁ h₂)) →
              motive l₁ l₂ p) :=
  fun H0 => by
    have := H0 (α := Nat) (motive := fun l₁ _ _ => l₁ ≠ []) (l₁ := []) (l₂ := []) List.Perm.nil
      (fun _ _ _ _ _ => by simp) (fun _ _ _ _ _ _ => by simp) (fun _ _ h _ => h)
    simp at this

-- `List.Perm.recOnSwap'` (`cons`, idx 6): `motive l₁ _ _ := l₁ = [] ∨ 2 ≤ l₁.length` satisfies `nil`, `swap'`, `trans`, fails at `[0] ~ [0]`
theorem Perm_recOnSwap__h6 :
    ¬ (∀ {α : Type} {motive : (l₁ l₂ : List α) → l₁.Perm l₂ → Prop} {l₁ l₂ : List α} (p : l₁.Perm l₂),
        motive [] [] List.Perm.nil →
          (∀ (x y : α) {l₁ l₂ : List α} (h : l₁.Perm l₂),
              motive l₁ l₂ h → motive (y :: x :: l₁) (x :: y :: l₂) (List.Perm.swap' x y h)) →
            (∀ {l₁ l₂ l₃ : List α} (h₁ : l₁.Perm l₂) (h₂ : l₂.Perm l₃),
                motive l₁ l₂ h₁ → motive l₂ l₃ h₂ → motive l₁ l₃ (List.Perm.trans h₁ h₂)) →
              motive l₁ l₂ p) :=
  fun H0 => by
    have := H0 (α := Nat) (motive := fun l₁ _ _ => l₁ = [] ∨ 2 ≤ l₁.length) (l₁ := [0]) (l₂ := [0])
      (List.Perm.refl _) (by simp) (fun _ _ _ _ _ _ => by simp) (fun _ _ h _ => h)
    simp at this

-- `List.Perm.recOnSwap'` (`swap'`, idx 7): `motive l₁ l₂ _ := l₁ = l₂` satisfies `nil`, `cons`, `trans`, fails at `[0, 1] ~ [1, 0]`
theorem Perm_recOnSwap__h7 :
    ¬ (∀ {α : Type} {motive : (l₁ l₂ : List α) → l₁.Perm l₂ → Prop} {l₁ l₂ : List α} (p : l₁.Perm l₂),
        motive [] [] List.Perm.nil →
          (∀ (x : α) {l₁ l₂ : List α} (h : l₁.Perm l₂), motive l₁ l₂ h → motive (x :: l₁) (x :: l₂) (List.Perm.cons x h)) →
            (∀ {l₁ l₂ l₃ : List α} (h₁ : l₁.Perm l₂) (h₂ : l₂.Perm l₃),
                motive l₁ l₂ h₁ → motive l₂ l₃ h₂ → motive l₁ l₃ (List.Perm.trans h₁ h₂)) →
              motive l₁ l₂ p) :=
  fun H0 => by
    have := H0 (α := Nat) (motive := fun l₁ l₂ _ => l₁ = l₂) (l₁ := [0, 1]) (l₂ := [1, 0])
      (List.Perm.swap 1 0 []) rfl (fun _ _ _ _ h => by rw [h]) (fun _ _ h₁ h₂ => h₁.trans h₂)
    simp at this

-- `List.Perm.recOnSwap'` (`trans`, idx 8): `motive l₁ l₂ _ := PS l₁ l₂` (one round of disjoint adjacent swaps) satisfies `nil`, `cons`, `swap'`, fails at `[0, 1, 2] ~ [2, 1, 0]`
theorem Perm_recOnSwap__h8 :
    ¬ (∀ {α : Type} {motive : (l₁ l₂ : List α) → l₁.Perm l₂ → Prop} {l₁ l₂ : List α} (p : l₁.Perm l₂),
        motive [] [] List.Perm.nil →
          (∀ (x : α) {l₁ l₂ : List α} (h : l₁.Perm l₂), motive l₁ l₂ h → motive (x :: l₁) (x :: l₂) (List.Perm.cons x h)) →
            (∀ (x y : α) {l₁ l₂ : List α} (h : l₁.Perm l₂),
                motive l₁ l₂ h → motive (y :: x :: l₁) (x :: y :: l₂) (List.Perm.swap' x y h)) →
              motive l₁ l₂ p) :=
  fun H0 => by
    have := H0 (α := Nat) (motive := fun l₁ l₂ _ => PS l₁ l₂ = true) (l₁ := [0, 1, 2]) (l₂ := [2, 1, 0])
      (by decide) rfl (fun x l₁ l₂ _ h => PS_cons x l₁ l₂ h) (fun x y l₁ l₂ _ h => PS_swap x y l₁ l₂ h)
    revert this; decide

-- `List.Perm.pmap` (`p`, idx 6): `l₁ = [0]`, `l₂ = []`
theorem Perm_pmap_h6 :
    ¬ (∀ {α : Type} {β : Type} {p : α → Prop} (f : (a : α) → p a → β) {l₁ l₂ : List α} {H₁ : ∀ (a : α), a ∈ l₁ → p a}
        {H₂ : ∀ (a : α), a ∈ l₂ → p a}, (List.pmap f l₁ H₁).Perm (List.pmap f l₂ H₂)) :=
  fun H0 => absurd (H0 (α := Nat) (β := Nat) (p := fun _ => True) (fun a _ => a) (l₁ := [0]) (l₂ := [])
      (H₁ := fun _ _ => trivial) (H₂ := fun _ _ => trivial)) (by decide)

-- `List.Perm.foldl_eq'` (`comm`, idx 6): `f z x = x` (keeps the last element), `[0, 1] ~ [1, 0]`
theorem Perm_foldl_eq__h6 :
    ¬ (∀ {β : Type} {α : Type} {f : β → α → β} {l₁ l₂ : List α},
        l₁.Perm l₂ → ∀ (init : β), List.foldl f init l₁ = List.foldl f init l₂) :=
  fun H0 => absurd (H0 (β := Nat) (α := Nat) (f := fun _ x => x) (l₁ := [0, 1]) (l₂ := [1, 0]) (by decide) 0)
      (by decide)

-- `List.Perm.rec_heq` (`hl`, idx 6): `β = Nat`, `b = 0`, `f a l b = b + 1`: satisfies `f_congr`, `f_swap`; `[0]` vs `[]` gives `1 ≠ 0`
theorem Perm_rec_heq_h6 :
    ¬ (∀ {α : Type} {β : List α → Type} {f : (a : α) → (l : List α) → β l → β (a :: l)} {b : β []} {l l' : List α},
        (∀ {a : α} {l l' : List α} {b : β l} {b' : β l'}, l.Perm l' → b ≍ b' → f a l b ≍ f a l' b') →
          (∀ {a a' : α} {l : List α} {b : β l}, f a (a' :: l) (f a' l b) ≍ f a' (a :: l) (f a l b)) →
            List.rec (motive := β) b f l ≍ List.rec (motive := β) b f l') :=
  fun H0 => by
    have h := H0 (α := Nat) (β := fun _ => Nat) (f := fun _ _ b => b + 1) (b := 0) (l := [0]) (l' := [])
      (fun _ h => heq_of_eq (by rw [eq_of_heq h])) HEq.rfl
    have := eq_of_heq h; revert this; decide

-- `List.Perm.rec_heq` (`f_congr`, idx 7): `β = Nat`, `f a l b = b + (l.drop 1).headD 0` (depends on `l` beyond its head, so `f_swap` holds): `[0, 1, 2] ↦ 2`, `[0, 2, 1] ↦ 1`
theorem Perm_rec_heq_h7 :
    ¬ (∀ {α : Type} {β : List α → Type} {f : (a : α) → (l : List α) → β l → β (a :: l)} {b : β []} {l l' : List α},
        l.Perm l' →
          (∀ {a a' : α} {l : List α} {b : β l}, f a (a' :: l) (f a' l b) ≍ f a' (a :: l) (f a l b)) →
            List.rec (motive := β) b f l ≍ List.rec (motive := β) b f l') :=
  fun H0 => by
    have h := H0 (α := Nat) (β := fun _ => Nat) (f := fun _ l b => b + (l.drop 1).headD 0) (b := 0)
      (l := [0, 1, 2]) (l' := [0, 2, 1]) (by decide) HEq.rfl
    have := eq_of_heq h; revert this; decide

-- `List.Perm.rec_heq` (`f_swap`, idx 8): `β = Nat`, `f a l b = a` (satisfies `f_congr`): `[0, 1] ↦ 0`, `[1, 0] ↦ 1`
theorem Perm_rec_heq_h8 :
    ¬ (∀ {α : Type} {β : List α → Type} {f : (a : α) → (l : List α) → β l → β (a :: l)} {b : β []} {l l' : List α},
        l.Perm l' →
          (∀ {a : α} {l l' : List α} {b : β l} {b' : β l'}, l.Perm l' → b ≍ b' → f a l b ≍ f a l' b') →
            List.rec (motive := β) b f l ≍ List.rec (motive := β) b f l') :=
  fun H0 => by
    have h := H0 (α := Nat) (β := fun _ => Nat) (f := fun a _ _ => a) (b := 0) (l := [0, 1]) (l' := [1, 0])
      (by decide) (fun _ _ => HEq.rfl)
    have := eq_of_heq h; revert this; decide

/-! ## `Init.Data.List.Lemmas` -/

-- `List.replicateRecOn` (`h0`, idx 3): `p l := l ≠ []` satisfies `hr` and `hi`, fails at `[]`
theorem replicateRecOn_h3 :
    ¬ (∀ {α : Type} {p : List α → Prop} (l : List α),
        (∀ (a : α) (n : Nat), 0 < n → p (List.replicate n a)) →
          (∀ (a b : α) (n : Nat) (l : List α), a ≠ b → 0 < n → p (b :: l) → p (List.replicate n a ++ b :: l)) → p l) :=
  fun H0 => absurd (H0 (α := Nat) (p := fun l => l ≠ []) [] (fun _ n hn => by simp; omega) (fun _ _ _ _ _ _ _ => by simp))
      (by simp)

-- `List.replicateRecOn` (`hr`, idx 4): `p l := l = [] ∨ ∃ x ∈ l, ∃ y ∈ l, x ≠ y` satisfies `h0` and `hi`, fails at `[0]`
theorem replicateRecOn_h4 :
    ¬ (∀ {α : Type} {p : List α → Prop} (l : List α),
        p [] → (∀ (a b : α) (n : Nat) (l : List α), a ≠ b → 0 < n → p (b :: l) → p (List.replicate n a ++ b :: l)) → p l) :=
  fun H0 => absurd (H0 (α := Nat) (p := fun l => l = [] ∨ ∃ x ∈ l, ∃ y ∈ l, x ≠ y) [0] (Or.inl rfl)
      (fun a b n l hab hn _ => Or.inr ⟨a, by simp; omega, b, by simp, hab⟩)) (by simp)

-- `List.replicateRecOn` (`hi`, idx 5): `p l := ∀ x ∈ l, ∀ y ∈ l, x = y` satisfies `h0` and `hr`, fails at `[0, 1]`
theorem replicateRecOn_h5 :
    ¬ (∀ {α : Type} {p : List α → Prop} (l : List α), p [] → (∀ (a : α) (n : Nat), 0 < n → p (List.replicate n a)) → p l) :=
  fun H0 => absurd (H0 (α := Nat) (p := fun l => ∀ x ∈ l, ∀ y ∈ l, x = y) [0, 1] (by simp)
      (fun a n _ x hx y hy => by rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy])) (by decide)

-- `List.foldrM_cons` (`inst`, idx 4): `SynM` (no monad law): `foldrM f b [0]` is `f 0 b >>= pure`, the right side `pure b >>= f 0`
theorem foldrM_cons_h4 :
    ¬ (∀ {m : Type → Type} {α : Type} {β : Type} [inst : Monad m] {a : α} {l : List α} {f : α → β → m β}
        {b : β}, List.foldrM f b (a :: l) = List.foldrM f b l >>= f a) :=
  fun H0 => absurd (H0 (m := SynM) (α := Nat) (β := Nat) (a := 0) (l := []) (f := ev) (b := 7)) (by decide)

-- `List.head_insert` (`w`, idx 5): dependent, derivable: `l.insert a` is `l` when `l.elem a` (so `l ≠ []`) and `a :: l` otherwise; no `LawfulBEq` needed
theorem head_insert_h5 :
    ∀ {α : Type u_1} [inst : BEq α] {l : List α} {a : α}, List.insert a l ≠ [] :=
  by
    intro α _ l a h
    unfold List.insert at h
    split at h
    · subst h; simp_all
    · simp at h

-- `List.get_of_eq` (`h`, idx 3): dependent; `∀ l l', l = l'` fails
theorem get_of_eq_h3 :
    ¬ (∀ {α : Type} {l l' : List α}, l = l') :=
  fun H0 => absurd (H0 (α := Nat) (l := []) (l' := [0])) (by simp)

/-! ## `Init.Data.List.Nat.InsertIdx` -/

-- `List.insertIdx_eraseIdx_of_le` (`a`, idx 5): if `i ≥ as.length`, both `eraseIdx`s are no-ops (the insertion makes the list at most one longer)
theorem insertIdx_eraseIdx_of_le_h5 :
    ∀ {α : Type u} {a : α} {i j : Nat} {as : List α},
      j ≤ i → (as.eraseIdx i).insertIdx j a = (as.insertIdx j a).eraseIdx (i + 1) :=
  by
    intro α a i j as hji
    by_cases hi : i < as.length
    · exact List.insertIdx_eraseIdx_of_le hi hji
    · rw [List.eraseIdx_of_length_le (by omega), List.eraseIdx_of_length_le]
      rw [List.length_insertIdx]
      split <;> omega

-- `List.insertIdx_comm` (`x`, idx 7): if `j > l.length`, inserting at `j` (resp. `j + 1` after inserting at `i ≤ j`) is a no-op, so both sides are `l.insertIdx i a`
theorem insertIdx_comm_h7 :
    ∀ {α : Type u} (a b : α) {i j : Nat} {l : List α},
      i ≤ j → (l.insertIdx i a).insertIdx (j + 1) b = (l.insertIdx j b).insertIdx i a :=
  by
    intro α a b i j l hij
    by_cases hj : j ≤ l.length
    · exact List.insertIdx_comm a b hij hj
    · rw [List.insertIdx_of_length_lt (i := j) (by omega)]
      apply List.insertIdx_of_length_lt
      rw [List.length_insertIdx]
      split <;> omega

/-! ## `Init.Data.List.Nat.Pairwise` -/

-- `List.map_getElem_sublist` (`h`, idx 3): `l = [0, 1]`, `is = [1, 0]`: `[1, 0]` is not a sublist of `[0, 1]`
theorem map_getElem_sublist_h3 :
    ¬ (∀ {α : Type} {l : List α} {is : List (Fin l.length)}, (List.map (fun (x : Fin l.length) => l[x]) is).Sublist l) :=
  fun H0 => absurd (H0 (α := Nat) (l := [0, 1]) (is := [1, 0])) (by decide)

-- `List.sublist_eq_map_getElem` (`h`, idx 3): `l = []`, `l' = [0]`: `is : List (Fin 0)` must be empty
theorem sublist_eq_map_getElem_h3 :
    ¬ (∀ {α : Type} {l l' : List α},
        ∃ (is : List (Fin l.length)),
          l' = List.map (fun (x : Fin l.length) => l[x]) is ∧ List.Pairwise (fun (x1 x2 : Fin l.length) => x1 < x2) is) :=
  fun H0 => by
    obtain ⟨is, h1, _⟩ := H0 (α := Nat) (l := []) (l' := [0])
    cases is with
    | nil => simp at h1
    | cons i _ => exact Fin.elim0 i

/-! ## `Init.Data.List.MapIdx` -/

-- `List.mapFinIdx_congr` (`w`, idx 4): dependent; `∀ xs ys, xs = ys` fails
theorem mapFinIdx_congr_h4 :
    ¬ (∀ {α : Type} {xs ys : List α}, xs = ys) :=
  fun H0 => absurd (H0 (α := Nat) (xs := []) (ys := [0])) (by simp)

-- `List.length_mapFinIdx_go` (`h`, idx 6): dependent; `bs.length + acc.size = as.length` fails for `bs = []`, `acc = #[]`, `as = [0]`
theorem length_mapFinIdx_go_h6 :
    ¬ (∀ {α : Type} {as : List α} {α_1 : Type} {bs : List α} {acc : Array α_1}, bs.length + acc.size = as.length) :=
  fun H0 => absurd (H0 (α := Nat) (as := [0]) (α_1 := Nat) (bs := []) (acc := #[])) (by simp)

-- `List.getElem_mapFinIdx_go` (`h`, idx 7): dependent; `bs.length + acc.size = as.length` fails for `bs = []`, `acc = #[]`, `as = [0]`
theorem getElem_mapFinIdx_go_h7 :
    ¬ (∀ {α : Type} {β : Type} {bs : List α} {acc : Array β} {as : List α}, bs.length + acc.size = as.length) :=
  fun H0 => absurd (H0 (α := Nat) (β := Nat) (bs := []) (acc := #[]) (as := [0])) (by simp)

-- `List.getElem_mapFinIdx_go` (`w`, idx 8): dependent (index bound); fails for `as = bs = []`, `acc = #[]`, `i = 0`
theorem getElem_mapFinIdx_go_h8 :
    ¬ (∀ {α : Type} {β : Type} {bs : List α} {acc : Array β} {as : List α} {f : (i : Nat) → α → i < as.length → β}
        {i : Nat} {h : bs.length + acc.size = as.length}, i < (List.mapFinIdx.go as f bs acc h).length) :=
  fun H0 => absurd (H0 (α := Nat) (β := Nat) (bs := []) (acc := #[]) (as := []) (f := fun _ a _ => a) (i := 0)
      (h := by simp)) (by simp)

-- `List.getElem_mapFinIdx` (`h`, idx 5): dependent (index bound); fails for `as = []`, `i = 0`
theorem getElem_mapFinIdx_h5 :
    ¬ (∀ {α : Type} {β : Type} {as : List α} {f : (i : Nat) → α → i < as.length → β} {i : Nat},
        i < (as.mapFinIdx f).length) :=
  fun H0 => absurd (H0 (α := Nat) (β := Nat) (as := []) (f := fun _ a _ => a) (i := 0)) (by simp)

-- `List.exists_of_mem_mapFinIdx` (`h`, idx 5): `l = []`: no index exists
theorem exists_of_mem_mapFinIdx_h5 :
    ¬ (∀ {β : Type} {α : Type} {b : β} {l : List α} {f : (i : Nat) → α → i < l.length → β},
        ∃ (i : Nat), ∃ (h : i < l.length), f i l[i] h = b) :=
  fun H0 => by obtain ⟨i, hi, _⟩ := H0 (β := Nat) (α := Nat) (b := 0) (l := []) (f := fun _ a _ => a); simp at hi

-- `List.mapFinIdx_eq_mapIdx` (`h`, idx 5): `l = [0]`, `f = 0`, `g = 1`
theorem mapFinIdx_eq_mapIdx_h5 :
    ¬ (∀ {α : Type} {β : Type} {l : List α} {f : (i : Nat) → α → i < l.length → β} {g : Nat → α → β},
        l.mapFinIdx f = List.mapIdx g l) :=
  fun H0 => absurd (H0 (α := Nat) (β := Nat) (l := [0]) (f := fun _ _ _ => 0) (g := fun _ _ => 1)) (by decide)

/-! ## `Init.Data.List.MinMax` -/

-- `List.max?_eq_some_iff_legacy` (`max_eq_or`, idx 6): `BB` (componentwise order on `Bool × Bool`, `max` = componentwise or): `[(1,0), (0,1)].max? = some (1,1)` but `(1,1)` is not in the list
theorem maxQ_eq_some_iff_legacy_h6 :
    ¬ (∀ {α : Type} {a : α} [inst : Max α] [inst_1 : LE α] [anti : Std.Antisymm fun (x1 x2 : α) => x1 ≤ x2],
        (∀ (a : α), a ≤ a) →
          (∀ (a b c : α), Max.max b c ≤ a ↔ b ≤ a ∧ c ≤ a) →
            ∀ {xs : List α}, xs.max? = Option.some a ↔ a ∈ xs ∧ ∀ (b : α), b ∈ xs → b ≤ a) :=
  fun H0 => absurd ((H0 (α := BB) (a := ⟨true, true⟩) BB.le_refl BB.max_le_iff (xs := [⟨true, false⟩, ⟨false, true⟩])).mp rfl).1
      (by decide)

/-! ## `Init.Data.List.MinMaxOn` -/

-- `List.maxOn_eq_minOn` (`h`, idx 6): dependent; `∀ xs, xs ≠ []` fails for `xs = []`
theorem maxOn_eq_minOn_h6 :
    ¬ (∀ {α : Type} {xs : List α}, xs ≠ []) :=
  fun H0 => H0 (α := Nat) (xs := []) rfl

/-! ## `Init.Data.List.MinMaxIdx` -/

-- `List.maxIdxOn_eq_minIdxOn` (`h`, idx 6): dependent; `∀ xs, xs ≠ []` fails for `xs = []`
theorem maxIdxOn_eq_minIdxOn_h6 :
    ¬ (∀ {α : Type} {xs : List α}, xs ≠ []) :=
  fun H0 => H0 (α := Nat) (xs := []) rfl

/-! ## `Init.Data.List.ToArray` -/

-- `List.forIn'_loop_toArray` (`h`, idx 7): dependent; `∀ l i, i ≤ l.length` fails for `l = []`, `i = 1`
theorem forIn__loop_toArray_h7 :
    ¬ (∀ {α : Type} (l : List α) (i : Nat), i ≤ l.length) :=
  fun H0 => absurd (H0 (α := Nat) [] 1) (by decide)

/-! ## `Init.Data.List.Lex` -/

-- `List.map_lt_map_iff_of_injective` (`hf`, idx 5): `f = id : Nat → E0` (`E0`: `Nat` with empty `<`), injective: `[0] < [1]` but not after mapping
theorem map_lt_map_iff_of_injective_h5 :
    ¬ (∀ {α : Type} {β : Type} [inst : LT α] [inst_1 : LT β] (f : α → β),
        Function.Injective f → ∀ {l₁ l₂ : List α}, List.map f l₁ < List.map f l₂ ↔ l₁ < l₂) :=
  fun H0 => absurd (H0 (α := Nat) (β := E0) (fun n => (n : E0)) (fun _ _ h => h) (l₁ := [0]) (l₂ := [1])) (by decide)

-- `List.map_lt_map_iff_of_injective` (`hfinj`, idx 6): `f : E0 → U1` constant (both `<` empty, so `hf` holds): `[0, 0] ↦ [(), ()] < [(), (), ()] ↤ [1, 0, 0]`, but `¬ [0, 0] < [1, 0, 0]`
theorem map_lt_map_iff_of_injective_h6 :
    ¬ (∀ {α : Type} {β : Type} [inst : LT α] [inst_1 : LT β] (f : α → β),
        (∀ (a b : α), f a < f b ↔ a < b) → ∀ {l₁ l₂ : List α}, List.map f l₁ < List.map f l₂ ↔ l₁ < l₂) :=
  fun H0 => absurd (H0 (α := E0) (β := U1) (fun _ => U1.star) (fun _ _ => Iff.rfl) (l₁ := [0, 0]) (l₂ := [1, 0, 0]))
      (by decide)

-- `List.map_le_map_iff_of_injective` (`hf`, idx 5): `f = id : Nat → E0`, injective: `[1] ≤ [0]` fails in `Nat`, holds in `E0`
theorem map_le_map_iff_of_injective_h5 :
    ¬ (∀ {α : Type} {β : Type} [inst : LT α] [inst_1 : LT β] (f : α → β),
        Function.Injective f → ∀ {l₁ l₂ : List α}, List.map f l₁ ≤ List.map f l₂ ↔ l₁ ≤ l₂) :=
  fun H0 => absurd (H0 (α := Nat) (β := E0) (fun n => (n : E0)) (fun _ _ h => h) (l₁ := [1]) (l₂ := [0])) (by decide)

-- `List.map_le_map_iff_of_injective` (`hfinj`, idx 6): `f : E0 → U1` constant: `[1, 0, 0] ≤ [0, 0]` holds in `E0`, fails after mapping
theorem map_le_map_iff_of_injective_h6 :
    ¬ (∀ {α : Type} {β : Type} [inst : LT α] [inst_1 : LT β] (f : α → β),
        (∀ (a b : α), f a < f b ↔ a < b) → ∀ {l₁ l₂ : List α}, List.map f l₁ ≤ List.map f l₂ ↔ l₁ ≤ l₂) :=
  fun H0 => absurd (H0 (α := E0) (β := U1) (fun _ => U1.star) (fun _ _ => Iff.rfl) (l₁ := [1, 0, 0]) (l₂ := [0, 0]))
      (by decide)

-- `List.flatMap_lt_flatMap_iff` (`hp`, idx 8): `α = Fin 2`, `f 0 = [0]`, `f 1 = [0, 0]` (monotone, nonempty, `f 0 <+: f 1`): `[0, 0]` and `[1]` have the same `flatMap`
theorem flatMap_lt_flatMap_iff_h8 :
    ¬ (∀ {α : Type} {β : Type} [inst : LT α] [Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
        [Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → List β),
        (∀ (a b : α), a < b → f a < f b) →
          (∀ (a : α), f a ≠ []) → ∀ {l₁ l₂ : List α}, List.flatMap f l₁ < List.flatMap f l₂ ↔ l₁ < l₂) :=
  fun H0 => absurd (H0 (α := Fin 2) (β := Nat) (fun a => if a = 0 then [0] else [0, 0]) (by decide) (by decide)
      (l₁ := [0, 0]) (l₂ := [1])) (by decide)

-- `List.flatMap_lt_flatMap_iff` (`hx`, idx 9): `α = U1` (one element), `f _ = []` (`hp` holds trivially): `[] < [()]` but both `flatMap`s are `[]`
theorem flatMap_lt_flatMap_iff_h9 :
    ¬ (∀ {α : Type} {β : Type} [inst : LT α] [Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
        [Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → List β),
        (∀ (a b : α), a < b → f a < f b) →
          (∀ (a b : α), f a <+: f b → a = b) → ∀ {l₁ l₂ : List α}, List.flatMap f l₁ < List.flatMap f l₂ ↔ l₁ < l₂) :=
  fun H0 => absurd (H0 (α := U1) (β := Nat) (fun _ => []) (fun _ _ (h : False) => h.elim) (fun _ _ _ => rfl) (l₁ := [])
      (l₂ := [U1.star])) (by decide)

-- `List.flatMap_le_flatMap_iff` (`hp`, idx 8): `α = Fin 2`, `f 0 = [0]`, `f 1 = [0, 0]`: `[1]` and `[0, 0]` have the same `flatMap`, but `¬ [1] ≤ [0, 0]`
theorem flatMap_le_flatMap_iff_h8 :
    ¬ (∀ {α : Type} {β : Type} [inst : LT α] [Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
        [Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → List β),
        (∀ (a b : α), a < b → f a < f b) →
          (∀ (a : α), f a ≠ []) → ∀ {l₁ l₂ : List α}, List.flatMap f l₁ ≤ List.flatMap f l₂ ↔ l₁ ≤ l₂) :=
  fun H0 => absurd (H0 (α := Fin 2) (β := Nat) (fun a => if a = 0 then [0] else [0, 0]) (by decide) (by decide)
      (l₁ := [1]) (l₂ := [0, 0])) (by decide)

-- `List.flatMap_le_flatMap_iff` (`hx`, idx 9): `α = U1`, `f _ = []`: `[()] ≤ []` fails but both `flatMap`s are `[]`
theorem flatMap_le_flatMap_iff_h9 :
    ¬ (∀ {α : Type} {β : Type} [inst : LT α] [Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
        [Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → List β),
        (∀ (a b : α), a < b → f a < f b) →
          (∀ (a b : α), f a <+: f b → a = b) → ∀ {l₁ l₂ : List α}, List.flatMap f l₁ ≤ List.flatMap f l₂ ↔ l₁ ≤ l₂) :=
  fun H0 => absurd (H0 (α := U1) (β := Nat) (fun _ => []) (fun _ _ (h : False) => h.elim) (fun _ _ _ => rfl) (l₁ := [U1.star])
      (l₂ := [])) (by decide)

/-! ## `Init.Data.List.Monadic` -/

-- `List.mapM_map` (`inst`, idx 5): `mapM.loop` over `l.map f` unfolds step by step to the loop with `g ∘ f`; no monad law used
theorem mapM_map_h5 :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_4} {γ : Type u_1} [inst : Monad m] {f : α → β} {g : β → m γ}
      {l : List α}, List.mapM g (List.map f l) = List.mapM (g ∘ f) l :=
  fun {m α β γ} _ {f g l} => mapM_map'

-- `List.foldrM_map` (`inst`, idx 5): `foldrM` is `foldlM` over the reverse, and `foldlM_map` holds in any monad
theorem foldrM_map_h5 :
    ∀ {m : Type u_1 → Type u_2} {β₁ : Type u_3} {β₂ : Type u_4} {α : Type u_1} [inst : Monad m] {f : β₁ → β₂}
      {g : β₂ → α → m α} {l : List β₁} {init : α},
      List.foldrM g init (List.map f l) = List.foldrM (fun (x : β₁) (y : α) => g (f x) y) init l :=
  fun {m β₁ β₂ α} _ {f g l init} => foldrM_map'

-- `List.foldrM_attachWith` (`inst`, idx 4): `l.attachWith q H = l.attach.map (fun a => ⟨a.1, H _ a.2⟩)` (`pmap_eq_map_attach`), then `foldrM` over `map`
theorem foldrM_attachWith_h4 :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {l : List α} {q : α → Prop}
      (H : ∀ (a : α), a ∈ l → q a) {f : { x : α // q x } → β → m β} {b : β},
      List.foldrM f b (l.attachWith q H) =
        List.foldrM (fun (a : { x : α // x ∈ l }) (acc : β) => f ⟨a.val, H a.val a.property⟩ acc) b l.attach :=
  by
    intro m α β _ l q H f b
    rw [show l.attachWith q H = l.attach.map (fun a => ⟨a.1, H _ a.2⟩) from List.pmap_eq_map_attach _,
      foldrM_map']

-- `List.forIn'_loop_congr` (`ha`, idx 10): dependent; `∀ xs as, ∃ ys, ys ++ xs = as` fails for `xs = [0]`, `as = []`
theorem forIn__loop_congr_h10 :
    ¬ (∀ {α : Type} {xs as : List α}, ∃ (ys : List α), ys ++ xs = as) :=
  fun H0 => by obtain ⟨ys, hy⟩ := H0 (α := Nat) (xs := [0]) (as := []); simp at hy

-- `List.forIn'_loop_congr` (`hb`, idx 11): dependent; `∀ xs bs, ∃ ys, ys ++ xs = bs` fails for `xs = [0]`, `bs = []`
theorem forIn__loop_congr_h11 :
    ¬ (∀ {α : Type} {xs bs : List α}, ∃ (ys : List α), ys ++ xs = bs) :=
  fun H0 => by obtain ⟨ys, hy⟩ := H0 (α := Nat) (xs := [0]) (bs := []); simp at hy

-- `List.forIn'_loop_congr` (`h`, idx 12): `xs = as = bs = [0]`, `f` returns `.done 0`, `g` returns `.done 1`
theorem forIn__loop_congr_h12 :
    ¬ (∀ {m : Type → Type} {α : Type} {β : Type} {xs : List α} [inst : Monad m] {as bs : List α}
        {f : (a' : α) → a' ∈ as → β → m (ForInStep β)} {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)} {b : β}
        (ha : ∃ (ys : List α), ys ++ xs = as) (hb : ∃ (ys : List α), ys ++ xs = bs),
        List.forIn'.loop as f xs b ha = List.forIn'.loop bs g xs b hb) :=
  fun H0 => absurd (H0 (m := Option) (α := Nat) (β := Nat) (xs := [0]) (as := [0]) (bs := [0])
      (f := fun _ _ _ => some (.done 0)) (g := fun _ _ _ => some (.done 1)) (b := 0) ⟨[], rfl⟩ ⟨[], rfl⟩) (by decide)

-- `List.forIn'_congr` (`w`, idx 6): dependent (used in `h`'s statement); `∀ as bs, as = bs` fails
theorem forIn__congr_h6 :
    ¬ (∀ {α : Type} {as bs : List α}, as = bs) :=
  fun H0 => absurd (H0 (α := Nat) (as := []) (bs := [0])) (by simp)

-- `List.forIn'_congr` (`hb`, idx 9): `as = bs = []`, `b = 0`, `b' = 1` in `Option`: the loops return `b` and `b'`
theorem forIn__congr_h9 :
    ¬ (∀ {m : Type → Type} {α : Type} {β : Type} [inst : Monad m] {as bs : List α} (w : as = bs) {b b' : β}
        {f : (a' : α) → a' ∈ as → β → m (ForInStep β)} {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)},
        (∀ (a : α) (m_1 : a ∈ bs) (b : β), f a (List.forIn'_congr._proof_1 w a m_1) b = g a m_1 b) →
          ForIn'.forIn' as b f = ForIn'.forIn' bs b' g) :=
  fun H0 => absurd (H0 (m := Option) (α := Nat) (β := Nat) (as := []) (bs := []) rfl (b := 0) (b' := 1)
      (f := fun _ _ _ => some (.done 0)) (g := fun _ _ _ => some (.done 0)) (fun _ h _ => by simp at h)) (by decide)

-- `List.forIn'_congr` (`h`, idx 12): `as = bs = [0]`, `f` returns `.done 0`, `g` returns `.done 1`
theorem forIn__congr_h12 :
    ¬ (∀ {m : Type → Type} {α : Type} {β : Type} [inst : Monad m] {as bs : List α},
        as = bs →
          ∀ {b b' : β},
            b = b' →
              ∀ {f : (a' : α) → a' ∈ as → β → m (ForInStep β)} {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)},
                ForIn'.forIn' as b f = ForIn'.forIn' bs b' g) :=
  fun H0 => absurd (H0 (m := Option) (α := Nat) (β := Nat) (as := [0]) (bs := [0]) rfl (b := 0) (b' := 0) rfl
      (f := fun _ _ _ => some (.done 0)) (g := fun _ _ _ => some (.done 1))) (by decide)

-- `List.forIn'_eq_foldlM` (`inst`, idx 4): `SynM`, `l = []`: `pure init` vs `ForInStep.value <$> pure (.yield init)`
theorem forIn__eq_foldlM_h4 :
    ¬ (∀ {m : Type → Type} {α : Type} {β : Type} [inst : Monad m] {l : List α}
        (f : (a : α) → a ∈ l → β → m (ForInStep β)) (init : β),
        ForIn'.forIn' l init f =
          ForInStep.value <$>
            List.foldlM
              (fun (b : ForInStep β) (x : { x : α // x ∈ l }) =>
                match x with
                | ⟨a, m_1⟩ =>
                  match b with
                  | ForInStep.yield b => f a m_1 b
                  | ForInStep.done b => (Pure.pure (ForInStep.done b) : m (ForInStep β)))
              (ForInStep.yield init) l.attach) :=
  fun H0 => absurd (H0 (m := SynM) (α := Nat) (β := Nat) (l := []) (fun a _ b => ev a (ForInStep.yield (a + b))) 0)
      (by decide)

-- `List.forIn'_yield_eq_foldlM` (`inst`, idx 5): `TyM` (map looks at its result type), `β = γ = Bool`, `l = [0]`: the loop maps into `ForInStep Bool` (value `1`), the fold into `Bool` (value `0`)
theorem forIn__yield_eq_foldlM_h5 :
    ¬ (∀ {m : Type → Type} {α : Type} {β γ : Type} [inst : Monad m] {l : List α}
        (f : (a : α) → a ∈ l → β → m γ) (g : (a : α) → a ∈ l → β → γ → β) (init : β),
        (ForIn'.forIn' l init fun (a : α) (m_1 : a ∈ l) (b : β) =>
            (fun (c : γ) => ForInStep.yield (g a m_1 b c)) <$> f a m_1 b) =
          List.foldlM
            (fun (b : β) (x : { x : α // x ∈ l }) =>
              match x with
              | ⟨a, m_1⟩ => g a m_1 b <$> f a m_1 b)
            init l.attach) :=
  fun H0 => by
    have h := H0 (m := TyM) (α := Nat) (β := Bool) (γ := Bool) (l := [0]) (fun _ _ _ => (0 : Nat)) (fun _ _ _ c => c) false
    have h' : @ite Nat (ForInStep Bool = ForInStep Bool) (Classical.propDecidable _) 1 0
        = @ite Nat (Bool = ForInStep Bool) (Classical.propDecidable _) 1 0 := h
    rw [ite_eq_left rfl, ite_eq_right bool_ne_forInStep] at h'
    exact absurd h' (by decide)

-- `List.forIn'_pure_yield_eq_foldl` (`inst`, idx 4): `SynM`, `l = [1]`: the loop binds once, the right side is a bare `pure`
theorem forIn__pure_yield_eq_foldl_h4 :
    ¬ (∀ {m : Type → Type} {α : Type} {β : Type} [inst : Monad m] {l : List α} (f : (a : α) → a ∈ l → β → β)
        (init : β),
        (ForIn'.forIn' l init fun (a : α) (m_1 : a ∈ l) (b : β) => (Pure.pure (ForInStep.yield (f a m_1 b)) : m (ForInStep β))) =
          (Pure.pure
            (List.foldl
              (fun (b : β) (x : { x : α // x ∈ l }) =>
                match x with
                | ⟨a, h⟩ => f a h b)
              init l.attach) : m β)) :=
  fun H0 => absurd (H0 (m := SynM) (α := Nat) (β := Nat) (l := [1]) (fun a _ b => a + b) 0) (by decide)

-- `List.forIn_yield_eq_foldlM` (`inst`, idx 5): `TyM` (map looks at its result type), `β = γ = Bool`, `l = [0]`: the loop maps into `ForInStep Bool` (value `1`), the fold into `Bool` (value `0`)
theorem forIn_yield_eq_foldlM_h5 :
    ¬ (∀ {m : Type → Type} {α : Type} {β γ : Type} [inst : Monad m] {l : List α} (f : α → β → m γ)
        (g : α → β → γ → β) (init : β),
        (ForIn.forIn l init fun (a : α) (b : β) => (fun (c : γ) => ForInStep.yield (g a b c)) <$> f a b) =
          List.foldlM (fun (b : β) (a : α) => g a b <$> f a b) init l) :=
  fun H0 => by
    have h := H0 (m := TyM) (α := Nat) (β := Bool) (γ := Bool) (l := [0]) (fun _ _ => (0 : Nat)) (fun _ _ c => c) false
    have h' : @ite Nat (ForInStep Bool = ForInStep Bool) (Classical.propDecidable _) 1 0
        = @ite Nat (Bool = ForInStep Bool) (Classical.propDecidable _) 1 0 := h
    rw [ite_eq_left rfl, ite_eq_right bool_ne_forInStep] at h'
    exact absurd h' (by decide)

-- `List.foldrM_subtype` (`inst`, idx 4): `f = fun a b => g a.1 b` by `hf`, then `foldrM` over `map` (no monad law)
theorem foldrM_subtype_h4 :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {p : α → Prop} {l : List { x : α // p x }}
      {f : { x : α // p x } → β → m β} {g : α → β → m β} {x : β},
      (∀ (x : α) (h : p x) (b : β), f ⟨x, h⟩ b = g x b) → List.foldrM f x l = List.foldrM g x l.unattach :=
  by
    intro m α β _ p l f g x hf
    have : f = fun a b => g a.1 b := funext fun ⟨x, h⟩ => funext fun b => hf x h b
    subst this
    exact foldrM_map'.symm

-- `List.foldrM_unattach` (`inst`, idx 4): the right side's function is `fun x b => f x.1 b` (by structure eta), then `foldrM` over `map`
theorem foldrM_unattach_h4 :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {P : α → Prop} {xs : List (Subtype P)}
      {f : α → β → m β} {init : β},
      List.foldrM f init xs.unattach =
        List.foldrM
          (fun (x : Subtype P) (b : β) =>
            match x with
            | ⟨x, h⟩ => binderNameHint x f (binderNameHint h () (binderNameHint b (f x) (f (wfParam x) b))))
          init xs :=
  fun {m α β} _ {P xs f init} => foldrM_map'

-- `List.mapM_subtype` (`inst`, idx 4): `f = g ∘ Subtype.val` by `hf`, then `mapM` over `map` (no monad law)
theorem mapM_subtype_h4 :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {p : α → Prop} {l : List { x : α // p x }}
      {f : { x : α // p x } → m β} {g : α → m β},
      (∀ (x : α) (h : p x), f ⟨x, h⟩ = g x) → List.mapM f l = List.mapM g l.unattach :=
  by
    intro m α β _ p l f g hf
    have : f = g ∘ Subtype.val := funext fun ⟨x, h⟩ => hf x h
    subst this
    exact mapM_map'.symm

-- `List.mapM_unattach` (`inst`, idx 4): the right side's function is `f ∘ Subtype.val` (by structure eta), then `mapM` over `map`
theorem mapM_unattach_h4 :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {P : α → Prop} {xs : List (Subtype P)}
      {f : α → m β},
      List.mapM f xs.unattach =
        List.mapM
          (fun (x : Subtype P) =>
            match x with
            | ⟨x, h⟩ => binderNameHint x f (binderNameHint h () (f (wfParam x))))
          xs :=
  fun {m α β} _ {P xs f} => mapM_map'

-- `List.filterMapM_subtype` (`inst`, idx 4): `f = g ∘ Subtype.val` by `hf`, then `filterMapM.loop` over `map` (no monad law)
theorem filterMapM_subtype_h4 :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {p : α → Prop} {l : List { x : α // p x }}
      {f : { x : α // p x } → m (Option β)} {g : α → m (Option β)},
      (∀ (x : α) (h : p x), f ⟨x, h⟩ = g x) → List.filterMapM f l = List.filterMapM g l.unattach :=
  by
    intro m α β _ p l f g hf
    have : f = g ∘ Subtype.val := funext fun ⟨x, h⟩ => hf x h
    subst this
    exact filterMapM_map'.symm

-- `List.filterMapM_unattach` (`inst`, idx 4): the right side's function is `f ∘ Subtype.val` (by structure eta), then `filterMapM` over `map`
theorem filterMapM_unattach_h4 :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {P : α → Prop} {xs : List (Subtype P)}
      {f : α → m (Option β)},
      List.filterMapM f xs.unattach =
        List.filterMapM
          (fun (x : Subtype P) =>
            match x with
            | ⟨x, h⟩ => binderNameHint x f (binderNameHint h () (f (wfParam x))))
          xs :=
  fun {m α β} _ {P xs f} => filterMapM_map'

-- `List.flatMapM_subtype` (`inst`, idx 4): `f = g ∘ Subtype.val` by `hf`, then `flatMapM.loop` over `map` (no monad law)
theorem flatMapM_subtype_h4 :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {p : α → Prop} {l : List { x : α // p x }}
      {f : { x : α // p x } → m (List β)} {g : α → m (List β)},
      (∀ (x : α) (h : p x), f ⟨x, h⟩ = g x) → List.flatMapM f l = List.flatMapM g l.unattach :=
  by
    intro m α β _ p l f g hf
    have : f = g ∘ Subtype.val := funext fun ⟨x, h⟩ => hf x h
    subst this
    exact flatMapM_map'.symm

-- `List.flatMapM_unattach` (`inst`, idx 4): the right side's function is `f ∘ Subtype.val` (by structure eta), then `flatMapM` over `map`
theorem flatMapM_unattach_h4 :
    ∀ {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [inst : Monad m] {P : α → Prop} {xs : List (Subtype P)}
      {f : α → m (List β)},
      List.flatMapM f xs.unattach =
        List.flatMapM
          (fun (x : Subtype P) =>
            match x with
            | ⟨x, h⟩ => binderNameHint x f (binderNameHint h () (f (wfParam x))))
          xs :=
  fun {m α β} _ {P xs f} => flatMapM_map'

/-! ## `Init.Data.List.FinRange` -/

-- `Fin.foldrM_eq_foldrM_finRange` (`inst`, idx 4): `Fin.foldrM.loop` and `foldrM` over `finRange` make the same binds in the same order (`foldrM_loop_zero`/`_succ` need no laws)
theorem Fin_foldrM_eq_foldrM_finRange_h4 :
    ∀ {m : Type u_1 → Type u_2} {n : Nat} {α : Type u_1} [inst : Monad m] (f : Fin n → α → m α) (x : α),
      Fin.foldrM n f x = List.foldrM f x (List.finRange n) :=
  by
    intro m n α _ f x
    unfold Fin.foldrM
    rw [finFoldrM_loop]
    congr 1
    apply List.ext_getElem <;> simp

-- `List.ofFnM_succ` (`inst`, idx 4): `SynM`, `n = 0`: the two sides build different programs (`map` and `bind` nested differently)
theorem ofFnM_succ_h4 :
    ¬ (∀ {m : Type → Type} {α : Type} {n : Nat} [inst : Monad m] {f : Fin (n + 1) → m α},
        List.ofFnM f = do
          let a ← f 0
          let as ← List.ofFnM fun (i : Fin n) => f i.succ
          Pure.pure (a :: as)) :=
  fun H0 => absurd (H0 (m := SynM) (α := Nat) (n := 0) (f := fun i => ev i.val i.val)) (by decide)

/-! ## `Init.Data.List.OfFn` -/

-- `List.ofFnM_succ_last` (`inst`, idx 4): `SynM`, `n = 0`: the two sides build different programs
theorem ofFnM_succ_last_h4 :
    ¬ (∀ {m : Type → Type} {α : Type} {n : Nat} [inst : Monad m] {f : Fin (n + 1) → m α},
        List.ofFnM f = do
          let as ← List.ofFnM fun (i : Fin n) => f i.castSucc
          let a ← f (Fin.last n)
          Pure.pure (as ++ [a])) :=
  fun H0 => absurd (H0 (m := SynM) (α := Nat) (n := 0) (f := fun i => ev i.val i.val)) (by decide)

/-! ## `Init.Data.List.Scan.Lemmas` -/

-- `List.scanlM_map` (`inst`, idx 6): the private loop `scanAuxM.go` over `as.map f` unfolds step by step to the loop with `g · (f ·)`; no monad law used
theorem scanlM_map_h6 :
    ∀ {m : Type u_1 → Type u_2} {α₁ : Type u_3} {α₂ : Type u_4} {β : Type u_1} {init : β} [inst : Monad m] {f : α₁ → α₂}
      {g : β → α₂ → m β} {as : List α₁},
      List.scanlM g init (List.map f as) = List.scanlM (fun (x1 : β) (x2 : α₁) => g x1 (f x2)) init as :=
  by
    intro m α₁ α₂ β init _ f g as
    unfold List.scanlM
    exact congrArg _ (scanAuxM_go_map f g as init [])

-- `List.scanrM_map` (`inst`, idx 6): `(as.map f).reverse = as.reverse.map f`, then the private loop `scanAuxM.go` over `map`; no monad law used
theorem scanrM_map_h6 :
    ∀ {m : Type u_1 → Type u_2} {α₁ : Type u_3} {α₂ : Type u_4} {β : Type u_1} {init : β} [inst : Monad m] {f : α₁ → α₂}
      {g : α₂ → β → m β} {as : List α₁},
      List.scanrM g init (List.map f as) = List.scanrM (fun (a : α₁) (b : β) => g (f a) b) init as :=
  by
    intro m α₁ α₂ β init _ f g as
    unfold List.scanrM
    rw [← List.map_reverse]
    exact scanAuxM_go_map f (flip g) as.reverse init []

/-! ## `Init.Data.List.Sort.Lemmas` -/

-- `List.MergeSort.Internal.splitInTwo_snd_pairwise` (`h`, idx 4): `le` empty, `l = [0, 0, 0, 0]`: the second half `[0, 0]` is not pairwise related
theorem MergeSort_Internal_splitInTwo_snd_pairwise_h4 :
    ¬ (∀ {α : Type} {n : Nat} {le : α → α → Prop} (l : { l : List α // l.length = n }),
        List.Pairwise le (List.MergeSort.Internal.splitInTwo l).snd.val) :=
  fun H0 => absurd (H0 (α := Nat) (n := 4) (le := fun _ _ => False) ⟨[0, 0, 0, 0], rfl⟩) (by decide)

-- `List.merge_stable` (`x`, idx 4): `le` constantly true, `xs = [(0, 1)]`, `ys = [(1, 0)]`: `zipIdxLE` puts `ys` first
theorem merge_stable_h4 :
    ¬ (∀ {α : Type} {le : α → α → Bool} (xs ys : List (α × Nat)),
        List.map (fun (x : α × Nat) => x.fst) (xs.merge ys (List.zipIdxLE le)) =
          (List.map (fun (x : α × Nat) => x.fst) xs).merge (List.map (fun (x : α × Nat) => x.fst) ys) le) :=
  fun H0 => absurd (H0 (α := Nat) (le := fun _ _ => true) [(0, 1)] [(1, 0)]) (by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF] <;> decide)

-- `List.pairwise_merge` (`trans`, idx 2): `rps`, `l₁ = [0]`, `l₂ = [1, 2]`: the merge `[0, 1, 2]` has `¬ rps 0 2`
theorem pairwise_merge_h2 :
    ¬ (∀ {α : Type} {le : α → α → Bool},
        (∀ (a b : α), (le a b || le b a) = Bool.true) →
          ∀ (l₁ l₂ : List α),
            List.Pairwise (fun (a b : α) => le a b = Bool.true) l₁ →
              List.Pairwise (fun (a b : α) => le a b = Bool.true) l₂ →
                List.Pairwise (fun (a b : α) => le a b = Bool.true) (l₁.merge l₂ le)) :=
  fun H0 => absurd (H0 (α := Fin 3) (le := rps) (by decide) [0] [1, 2] (by decide) (by decide)) (by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF] <;> decide)

-- `List.pairwise_merge` (`h₁`, idx 6): usual `≤`, `l₁ = [1, 0]`, `l₂ = []`
theorem pairwise_merge_h6 :
    ¬ (∀ {α : Type} {le : α → α → Bool},
        (∀ (a b c : α), le a b = Bool.true → le b c = Bool.true → le a c = Bool.true) →
          (∀ (a b : α), (le a b || le b a) = Bool.true) →
            ∀ (l₁ l₂ : List α),
              List.Pairwise (fun (a b : α) => le a b = Bool.true) l₂ →
                List.Pairwise (fun (a b : α) => le a b = Bool.true) (l₁.merge l₂ le)) :=
  fun H0 => absurd (H0 (α := Fin 3) (le := leF) (by decide) (by decide) [1, 0] [] (by decide)) (by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF] <;> decide)

-- `List.pairwise_merge` (`h₂`, idx 7): usual `≤`, `l₁ = []`, `l₂ = [1, 0]`
theorem pairwise_merge_h7 :
    ¬ (∀ {α : Type} {le : α → α → Bool},
        (∀ (a b c : α), le a b = Bool.true → le b c = Bool.true → le a c = Bool.true) →
          (∀ (a b : α), (le a b || le b a) = Bool.true) →
            ∀ (l₁ l₂ : List α),
              List.Pairwise (fun (a b : α) => le a b = Bool.true) l₁ →
                List.Pairwise (fun (a b : α) => le a b = Bool.true) (l₁.merge l₂ le)) :=
  fun H0 => absurd (H0 (α := Fin 3) (le := leF) (by decide) (by decide) [] [1, 0] (by decide)) (by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF] <;> decide)

-- `List.mergeSort_append` (`h₁`, idx 4): `le00`, `l₁ = [0]`, `l₂ = [1, 0]`: the split of `[0, 1, 0]` is `[0, 1] | [0]`, not `[0] | [1, 0]`
theorem mergeSort_append_h4 :
    ¬ (∀ {α : Type} {le : α → α → Bool} (l₁ l₂ : List α),
        l₁.length ≤ l₂.length + 1 → (l₁ ++ l₂).mergeSort le = (l₁.mergeSort le).merge (l₂.mergeSort le) le) :=
  fun H0 => absurd (H0 (α := Fin 3) (le := le00) [0] [1, 0] (by decide)) (by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF] <;> decide)

-- `List.mergeSort_append` (`h₂`, idx 5): `le00`, `l₁ = [0, 0, 1]`, `l₂ = [0]`
theorem mergeSort_append_h5 :
    ¬ (∀ {α : Type} {le : α → α → Bool} (l₁ l₂ : List α),
        l₂.length ≤ l₁.length → (l₁ ++ l₂).mergeSort le = (l₁.mergeSort le).merge (l₂.mergeSort le) le) :=
  fun H0 => absurd (H0 (α := Fin 3) (le := le00) [0, 0, 1] [0] (by decide)) (by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF] <;> decide)

-- `List.pairwise_mergeSort` (`trans`, idx 2): `rps`, `l = [2, 1, 0]`: `mergeSort l = [0, 1, 2]` and `¬ rps 0 2`
theorem pairwise_mergeSort_h2 :
    ¬ (∀ {α : Type} {le : α → α → Bool},
        (∀ (a b : α), (le a b || le b a) = Bool.true) →
          ∀ (l : List α), List.Pairwise (fun (a b : α) => le a b = Bool.true) (l.mergeSort le)) :=
  fun H0 => absurd (H0 (α := Fin 3) (le := rps) (by decide) [2, 1, 0]) (by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF] <;> decide)

-- `List.mergeSort_cons` (`trans`, idx 2): `rps`, `a = 2`, `l = [1, 0]`: `mergeSort [2, 1, 0] = [0, 1, 2]`, `mergeSort [1, 0] = [0, 1]`, so `l₁ = [0, 1]`, but `rps 2 0`
theorem mergeSort_cons_h2 :
    ¬ (∀ {α : Type} {le : α → α → Bool},
        (∀ (a b : α), (le a b || le b a) = Bool.true) →
          ∀ (a : α) (l : List α),
            ∃ (l₁ : List α),
              ∃ (l₂ : List α),
                (a :: l).mergeSort le = l₁ ++ a :: l₂ ∧ l.mergeSort le = l₁ ++ l₂ ∧ ∀ (b : α), b ∈ l₁ → (!le a b) = Bool.true) :=
  fun H0 => by
    obtain ⟨l₁, l₂, h1, h2, h3⟩ := H0 (α := Fin 3) (le := rps) (by decide) 2 [1, 0]
    have e1 : ([2, 1, 0] : List (Fin 3)).mergeSort rps = [0, 1, 2] := by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF]
    have e2 : ([1, 0] : List (Fin 3)).mergeSort rps = [0, 1] := by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF]
    rw [e1] at h1; rw [e2] at h2
    have key : ∃ k, k < 3 ∧ ([0, 1, 2] : List (Fin 3)) = ([0, 1] : List (Fin 3)).take k ++ 2 :: ([0, 1] : List (Fin 3)).drop k ∧
        ∀ b ∈ ([0, 1] : List (Fin 3)).take k, (!rps 2 b) = true :=
      ⟨l₁.length, by have := congrArg List.length h2; simp at this; omega, by rw [h2]; simpa using h1,
        by rw [h2]; simpa using h3⟩
    revert key; decide

-- `List.mergeSort_cons` (`total`, idx 3): `le00` (`le a b ↔ a = b = 0`), `a = 0`, `l = [1, 0]`: `mergeSort [0, 1, 0] = [0, 1, 0]`, `mergeSort [1, 0] = [0, 1]`, so `l₁ = [0, 1]`, but `le00 0 0`
theorem mergeSort_cons_h3 :
    ¬ (∀ {α : Type} {le : α → α → Bool},
        (∀ (a b c : α), le a b = Bool.true → le b c = Bool.true → le a c = Bool.true) →
          ∀ (a : α) (l : List α),
            ∃ (l₁ : List α),
              ∃ (l₂ : List α),
                (a :: l).mergeSort le = l₁ ++ a :: l₂ ∧ l.mergeSort le = l₁ ++ l₂ ∧ ∀ (b : α), b ∈ l₁ → (!le a b) = Bool.true) :=
  fun H0 => by
    obtain ⟨l₁, l₂, h1, h2, h3⟩ := H0 (α := Fin 3) (le := le00) (by decide) 0 [1, 0]
    have e1 : ([0, 1, 0] : List (Fin 3)).mergeSort le00 = [0, 1, 0] := by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF]
    have e2 : ([1, 0] : List (Fin 3)).mergeSort le00 = [0, 1] := by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF]
    rw [e1] at h1; rw [e2] at h2
    have key : ∃ k, k < 3 ∧ ([0, 1, 0] : List (Fin 3)) = ([0, 1] : List (Fin 3)).take k ++ 0 :: ([0, 1] : List (Fin 3)).drop k ∧
        ∀ b ∈ ([0, 1] : List (Fin 3)).take k, (!le00 0 b) = true :=
      ⟨l₁.length, by have := congrArg List.length h2; simp at this; omega, by rw [h2]; simpa using h1,
        by rw [h2]; simpa using h3⟩
    revert key; decide

-- `List.sublist_mergeSort` (`trans`, idx 3): `rps` (total, not transitive) on `Fin 3`, `xs = [2, 1, 0]`, `ys = [2, 0]`: `mergeSort xs = [0, 1, 2]`
theorem sublist_mergeSort_h3 :
    ¬ (∀ {α : Type} {le : α → α → Bool} {xs : List α},
        (∀ (a b : α), (le a b || le b a) = Bool.true) →
          ∀ {ys : List α},
            List.Pairwise (fun (a b : α) => le a b = Bool.true) ys → ys.Sublist xs → ys.Sublist (xs.mergeSort le)) :=
  fun H0 => absurd (H0 (α := Fin 3) (le := rps) (xs := [2, 1, 0]) (by decide) (ys := [2, 0]) (by decide) (by decide))
      (by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF] <;> decide)

-- `List.sublist_mergeSort` (`total`, idx 4): `lt01` (`le a b ↔ a = 0 ∧ b = 1`; transitive, not total), `xs = [0, 2, 1]`, `ys = [0, 1]`
theorem sublist_mergeSort_h4 :
    ¬ (∀ {α : Type} {le : α → α → Bool} {xs : List α},
        (∀ (a b c : α), le a b = Bool.true → le b c = Bool.true → le a c = Bool.true) →
          ∀ {ys : List α},
            List.Pairwise (fun (a b : α) => le a b = Bool.true) ys → ys.Sublist xs → ys.Sublist (xs.mergeSort le)) :=
  fun H0 => absurd (H0 (α := Fin 3) (le := lt01) (xs := [0, 2, 1]) (by decide) (ys := [0, 1]) (by decide) (by decide))
      (by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF] <;> decide)

-- `List.sublist_mergeSort` (`x`, idx 6): usual `≤` on `Fin 3`, `xs = ys = [1, 0]` (not sorted)
theorem sublist_mergeSort_h6 :
    ¬ (∀ {α : Type} {le : α → α → Bool} {xs : List α},
        (∀ (a b c : α), le a b = Bool.true → le b c = Bool.true → le a c = Bool.true) →
          (∀ (a b : α), (le a b || le b a) = Bool.true) → ∀ {ys : List α}, ys.Sublist xs → ys.Sublist (xs.mergeSort le)) :=
  fun H0 => absurd (H0 (α := Fin 3) (le := leF) (xs := [1, 0]) (by decide) (by decide) (ys := [1, 0]) (by decide))
      (by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF] <;> decide)

-- `List.pair_sublist_mergeSort` (`trans`, idx 5): `rps`, `a = 2`, `b = 0`, `l = [2, 1, 0]`
theorem pair_sublist_mergeSort_h5 :
    ¬ (∀ {α : Type} {le : α → α → Bool} {a b : α} {l : List α},
        (∀ (a b : α), (le a b || le b a) = Bool.true) →
          le a b = Bool.true → [a, b].Sublist l → [a, b].Sublist (l.mergeSort le)) :=
  fun H0 => absurd (H0 (α := Fin 3) (le := rps) (a := 2) (b := 0) (l := [2, 1, 0]) (by decide) (by decide) (by decide))
      (by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF] <;> decide)

-- `List.pair_sublist_mergeSort` (`total`, idx 6): `lt01`, `a = 0`, `b = 1`, `l = [0, 2, 1]`
theorem pair_sublist_mergeSort_h6 :
    ¬ (∀ {α : Type} {le : α → α → Bool} {a b : α} {l : List α},
        (∀ (a b c : α), le a b = Bool.true → le b c = Bool.true → le a c = Bool.true) →
          le a b = Bool.true → [a, b].Sublist l → [a, b].Sublist (l.mergeSort le)) :=
  fun H0 => absurd (H0 (α := Fin 3) (le := lt01) (a := 0) (b := 1) (l := [0, 2, 1]) (by decide) (by decide) (by decide))
      (by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF] <;> decide)

-- `List.pair_sublist_mergeSort` (`hab`, idx 7): usual `≤` on `Fin 3`, `a = 1`, `b = 0`, `l = [1, 0]`
theorem pair_sublist_mergeSort_h7 :
    ¬ (∀ {α : Type} {le : α → α → Bool} {a b : α} {l : List α},
        (∀ (a b c : α), le a b = Bool.true → le b c = Bool.true → le a c = Bool.true) →
          (∀ (a b : α), (le a b || le b a) = Bool.true) → [a, b].Sublist l → [a, b].Sublist (l.mergeSort le)) :=
  fun H0 => absurd (H0 (α := Fin 3) (le := leF) (a := 1) (b := 0) (l := [1, 0]) (by decide) (by decide) (by decide))
      (by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF] <;> decide)

-- `List.map_merge` (`hl`, idx 7): `r = ≤`, `s = ≥`, `f = id`, `l = [0]`, `l' = [1]`
theorem map_merge_h7 :
    ¬ (∀ {α : Type} {β : Type} {f : α → β} {r : α → α → Bool} {s : β → β → Bool} {l l' : List α},
        List.map f (l.merge l' r) = (List.map f l).merge (List.map f l') s) :=
  fun H0 => absurd (H0 (α := Fin 3) (β := Fin 3) (f := id) (r := leF) (s := fun a b => leF b a) (l := [0]) (l' := [1]))
      (by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF] <;> decide)

-- `List.map_mergeSort` (`hl`, idx 6): `r = ≤`, `s = ≥`, `f = id`, `l = [1, 0]`
theorem map_mergeSort_h6 :
    ¬ (∀ {α : Type} {β : Type} {r : α → α → Bool} {s : β → β → Bool} {f : α → β} {l : List α},
        List.map f (l.mergeSort r) = (List.map f l).mergeSort s) :=
  fun H0 => absurd (H0 (α := Fin 3) (β := Fin 3) (r := leF) (s := fun a b => leF b a) (f := id) (l := [1, 0]))
      (by simp [List.mergeSort, List.merge, List.MergeSort.Internal.splitInTwo, List.zipIdxLE, rps, lt01, le00, leF] <;> decide)

