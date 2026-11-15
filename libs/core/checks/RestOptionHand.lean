/-!
Hand resolution of the hypotheses in `Init.Data.Option.*` (Lemmas, Monadic, Attach, Basic,
Function, List, Array) that `HypCheck.lean` left unresolved (cluster `Option`). For each hypothesis
`hᵢ` of theorem `T`, this file proves `T'` (removable), `¬T'` (necessary), or, for a dependent
hypothesis, `¬∀ indep, Hᵢ`.

All 92 hypotheses (78 theorems) are decided: 87 necessary, 5 removable.

Removable (5, all `[LawfulMonad m]` in `Option.Monadic`, none derivable):
* `forIn'_some`, `forIn_some`: `forIn' (some a) b f` is by definition `bind (f a rfl b) k` with a
  continuation `k` that equals `pure ∘ ForInStep.value` on both constructors (`funext` + `cases`).
* `forIn'_map`, `forIn_map`: `Option.map g` keeps the constructor, so both loops unfold to the same
  term (`cases o <;> rfl`).
* `forIn'_congr`: after substituting `w` and `hb`, `h` says `f = g` pointwise (membership proofs
  agree by proof irrelevance), so the two loops are equal in any monad.

Necessary (87): 34 dependent ones (`isSome` side conditions of `get` on `ite`/`dite`/`pbind`/
`pfilter`/`pmap`, `∀ a, o = some a → p a` for `pmap`, `o = o'`/`p ↔ p'` in the congruence lemmas,
`x = some a` in `pbind_some'`/`pelim_some'`/`pmap_some'`), refuted as `¬∀ indep, Hᵢ` with `o = none`,
`o = some 0` and `p = False`, or `p = True`/`False`; the other 53 by counterexamples with the models
below.

Models (in `RestOptionHand`):
* `NatM`, a non-lawful monad whose values are `Nat`s counting the outer binds (`bind x _ = x + 1`,
  `pure _ = 0`, `map` free): `bind x (pure ∘ f) ≠ f <$> x`, `bind (pure a) f ≠ f a`, `bind` not
  associative. Its `MonadAttach` has `CanReturn` empty and `attach` the identity, so it is a
  `LawfulMonadAttach` (`map` is free); `OptionT NatM` is not even weakly lawful.
* `CntA`, a non-lawful applicative counting maps (`map _ x = x + 1`, `pure _ = 0`): `id <$> x ≠ x`.
* `BadOpt`, `Option` (a lawful monad) with `attach _ = none`: not weakly lawful, and neither is
  `OptionT BadOpt`.
* Plain `Nat` instances given inline: `LE`/`LT` empty or `<`, `Max` as `x + y + 1` or `+`,
  constant `BEq`s, non-commutative/non-associative/non-idempotent operations (`-`, `+`), the full
  relation on `Unit` (not well-founded), `Bool`/`Empty` for `choice`.

Run with the lean4 repo's stage1 binary: `lean checks/RestOptionHand.lean`.
-/

set_option linter.unusedVariables false

universe u_1 u_2 u_3 u_4

namespace RestOptionHand

/-! ## Models -/

/-- Non-lawful monad: values are `Nat`s counting the outer binds; `map` is free. -/
def NatM (_ : Type) : Type := Nat

instance : Monad NatM where
  pure _ := (0 : Nat)
  bind x _ := (show Nat from x) + 1
  map _ x := (show Nat from x)

/-- `CanReturn` empty, `attach` the identity: lawful as a `MonadAttach` because `map` is free. -/
instance : MonadAttach NatM where
  CanReturn _ _ := False
  attach x := (show Nat from x)

instance : LawfulMonadAttach NatM where
  map_attach := rfl
  canReturn_map_imp h := h.elim

/-- Non-lawful applicative: values are `Nat`s counting the maps. -/
def CntA (_ : Type) : Type := Nat

instance : Applicative CntA where
  pure _ := (0 : Nat)
  map _ x := (show Nat from x) + 1
  seq f x := (show Nat from f) + (show Nat from x ())

/-- `Option` with an `attach` that always fails. -/
def BadOpt (α : Type) : Type := Option α

instance : Monad BadOpt := inferInstanceAs (Monad Option)
instance : LawfulMonad BadOpt := inferInstanceAs (LawfulMonad Option)
instance : MonadAttach BadOpt where
  CanReturn _ _ := True
  attach _ := (none : Option _)

/-- A relation with a reflexive point is not well-founded. -/
theorem not_wf_of_refl {α : Sort _} {r : α → α → Prop} (a : α) (ha : r a a) : ¬ WellFounded r := by
  intro h
  have : ∀ x, Acc r x → x ≠ a := fun x hx => by
    induction hx with
    | intro x _ ih => intro hxa; subst hxa; exact ih x ha rfl
  exact this a (h.apply a) rfl

theorem choice_empty : Option.choice Empty = none :=
  Option.choice_eq_none_iff_not_nonempty.2 fun ⟨e⟩ => nomatch e

/-! ## `Option.Lemmas`: order hypotheses -/

-- `Option.left_le_max` (`le_refl`, idx 3): `≤` is `<`, `max x y = x + y + 1`; `some 0 ≤ max (some 0) none` fails
theorem left_le_max_h3 : ¬ ∀ {α : Type} [LE α] [Max α], (∀ x y : α, x ≤ max x y) → ∀ {a b : Option α}, a ≤ max a b :=
  fun h => absurd (@h Nat ⟨(· < ·)⟩ ⟨fun x y => x + y + 1⟩ (fun x y => by show x < x + y + 1; omega)
    (some 0) none) (by show ¬ (0 < 0); decide)

-- `Option.right_le_max` (`le_refl`, idx 3): `≤` is `<`, `max x y = x + y + 1`; `some 0 ≤ max none (some 0)` fails
theorem right_le_max_h3 : ¬ ∀ {α : Type} [LE α] [Max α], (∀ x y : α, y ≤ max x y) → ∀ {a b : Option α}, b ≤ max a b :=
  fun h => absurd (@h Nat ⟨(· < ·)⟩ ⟨fun x y => x + y + 1⟩ (fun x y => by show y < x + y + 1; omega)
    none (some 0)) (by show ¬ (0 < 0); decide)

-- `Option.filter_le` (`le_refl`, idx 2): empty `≤`, `o = some 0`, `p = true`
theorem filter_le_h2 : ¬ ∀ {α : Type} [LE α] {o : Option α} {p : α → Bool}, Option.filter p o ≤ o :=
  fun h => absurd (@h Nat ⟨fun _ _ => False⟩ (some 0) (fun _ => true)) (by simp [Option.filter, LE.le, Option.le])

-- `Option.le_filter` (`le_refl`, idx 2): empty `≤`, `o = some 0`, `p = true`
theorem le_filter_h2 : ¬ ∀ {α : Type} [LE α] {o : Option α} {p : α → Bool}, o ≤ Option.filter p o ↔ Option.all p o = true :=
  fun h => absurd (@h Nat ⟨fun _ _ => False⟩ (some 0) (fun _ => true)) (by simp [Option.filter, LE.le, Option.le])

-- `Option.pfilter_le` (`le_refl`, idx 2): empty `≤`, `o = some 0`, `p = true`
theorem pfilter_le_h2 : ¬ ∀ {α : Type} [LE α] {o : Option α} {p : (a : α) → o = some a → Bool}, o.pfilter p ≤ o :=
  fun h => absurd (@h Nat ⟨fun _ _ => False⟩ (some 0) (fun _ _ => true)) (by simp [Option.pfilter, LE.le, Option.le])

-- `Option.filter_lt` (`lt_irrefl`, idx 2): full `<`, `o = some 0`, `p = true`
theorem filter_lt_h2 : ¬ ∀ {α : Type} [LT α] {o : Option α} {p : α → Bool},
    Option.filter p o < o ↔ Option.any (fun a => !p a) o = true :=
  fun h => absurd (@h Nat ⟨fun _ _ => True⟩ (some 0) (fun _ => true)) (by simp [Option.filter, LT.lt, Option.lt])

-- `Option.not_lt_filter` (`lt_irrefl`, idx 2): full `<`, `o = some 0`, `p = true`
theorem not_lt_filter_h2 : ¬ ∀ {α : Type} [LT α] {o : Option α} {p : α → Bool}, ¬o < Option.filter p o :=
  fun h => absurd (@h Nat ⟨fun _ _ => True⟩ (some 0) (fun _ => true)) (by simp [Option.filter, LT.lt, Option.lt])

-- `Option.not_lt_pfilter` (`lt_irrefl`, idx 2): full `<`, `o = some 0`, `p = true`
theorem not_lt_pfilter_h2 : ¬ ∀ {α : Type} [LT α] {o : Option α} {p : (a : α) → o = some a → Bool}, ¬o < o.pfilter p :=
  fun h => absurd (@h Nat ⟨fun _ _ => True⟩ (some 0) (fun _ _ => true)) (by simp [Option.pfilter, LT.lt, Option.lt])

/-! ## `Option.Lemmas`: operation laws -/

-- `Option.max_pfilter_left` (`inst`, idx 2): `max = +`, `o = some 1`, `p = true`
theorem max_pfilter_left_h2 : ¬ ∀ {α : Type} [Max α] {o : Option α} {p : (a : α) → o = some a → Bool}, max (o.pfilter p) o = o :=
  fun h => absurd (@h Nat ⟨(· + ·)⟩ (some 1) (fun _ _ => true)) (by simp [Option.pfilter, max, Option.max])

-- `Option.max_pfilter_right` (`inst`, idx 2): `max = +`, `o = some 1`, `p = true`
theorem max_pfilter_right_h2 : ¬ ∀ {α : Type} [Max α] {o : Option α} {p : (a : α) → o = some a → Bool}, max o (o.pfilter p) = o :=
  fun h => absurd (@h Nat ⟨(· + ·)⟩ (some 1) (fun _ _ => true)) (by simp [Option.pfilter, max, Option.max])

-- `Option.min_pfilter_left` (`inst`, idx 2): `min = +`, `o = some 1`, `p = true`
theorem min_pfilter_left_h2 : ¬ ∀ {α : Type} [Min α] {o : Option α} {p : (a : α) → o = some a → Bool},
    min (o.pfilter p) o = o.pfilter p :=
  fun h => absurd (@h Nat ⟨(· + ·)⟩ (some 1) (fun _ _ => true)) (by simp [Option.pfilter, min, Option.min])

-- `Option.min_pfilter_right` (`inst`, idx 2): `min = +`, `o = some 1`, `p = true`
theorem min_pfilter_right_h2 : ¬ ∀ {α : Type} [Min α] {o : Option α} {p : (a : α) → o = some a → Bool},
    min o (o.pfilter p) = o.pfilter p :=
  fun h => absurd (@h Nat ⟨(· + ·)⟩ (some 1) (fun _ _ => true)) (by simp [Option.pfilter, min, Option.min])

-- `Option.instIdempotentOpMax` (`inst`, idx 2): `max = +`; `max (some 1) (some 1) = some 2`
theorem instIdempotentOpMax_h2 : ¬ ∀ {α : Type} [Max α], Std.IdempotentOp (α := Option α) max :=
  fun h => absurd ((@h Nat ⟨(· + ·)⟩).idempotent (some 1)) (by simp [max, Option.max])

-- `Option.idempotentOp_merge` (`inst`, idx 2): `f = +`
theorem idempotentOp_merge_h2 : ¬ ∀ {α : Type} (f : α → α → α), Std.IdempotentOp (Option.merge f) :=
  fun h => absurd ((h (α := Nat) (· + ·)).idempotent (some 1)) (by simp [Option.merge])

-- `Option.associative_merge` (`inst`, idx 2): `f = -`
theorem associative_merge_h2 : ¬ ∀ {α : Type} (f : α → α → α), Std.Associative (Option.merge f) :=
  fun h => absurd ((h (α := Nat) (· - ·)).assoc (some 1) (some 1) (some 1)) (by simp [Option.merge])

-- `Option.commutative_merge` (`inst`, idx 2): `f = -`
theorem commutative_merge_h2 : ¬ ∀ {α : Type} (f : α → α → α), Std.Commutative (Option.merge f) :=
  fun h => absurd ((h (α := Nat) (· - ·)).comm (some 1) (some 0)) (by simp [Option.merge])

/-! ## `Option.Lemmas`: `choice`, `guard`, well-foundedness -/

-- `Option.choice_eq_some` (`inst`, idx 1): `α = Bool`, `a = true` and `a = false`
theorem choice_eq_some_h1 : ¬ ∀ {α : Type} (a : α), Option.choice α = some a :=
  fun h => absurd ((h true).symm.trans (h false)) (by simp)

-- `Option.choice_eq_default` (`inst`, idx 1): `α = Bool` with `default = true` and `default = false`
theorem choice_eq_default_h1 : ¬ ∀ {α : Type} [inst : Inhabited α], Option.choice α = some default :=
  fun h => absurd ((@h Bool ⟨true⟩).symm.trans (@h Bool ⟨false⟩)) (by simp)

-- `Option.isSome_choice` (`inst`, idx 1): `α = Empty`
theorem isSome_choice_h1 : ¬ ∀ {α : Type}, (Option.choice α).isSome = true :=
  fun h => absurd (@h Empty) (by rw [choice_empty]; simp)

-- `Option.isNone_choice_eq_false` (`inst`, idx 1): `α = Empty`
theorem isNone_choice_eq_false_h1 : ¬ ∀ {α : Type}, (Option.choice α).isNone = false :=
  fun h => absurd (@h Empty) (by rw [choice_empty]; simp)

-- `Option.length_toList_choice_eq_one` (`inst`, idx 1): `α = Empty`
theorem length_toList_choice_eq_one_h1 : ¬ ∀ {α : Type}, (Option.choice α).toList.length = 1 :=
  fun h => absurd (@h Empty) (by rw [choice_empty]; simp)

-- `Option.size_toArray_choice_eq_one` (`inst`, idx 1): `α = Empty`
theorem size_toArray_choice_eq_one_h1 : ¬ ∀ {α : Type}, (Option.choice α).toArray.size = 1 :=
  fun h => absurd (@h Empty) (by rw [choice_empty]; simp)

-- `Option.guard_congr` (`h`, idx 3): `f = true`, `g = false`
theorem guard_congr_h3 : ¬ ∀ {α : Type} {f g : α → Bool}, Option.guard f = Option.guard g :=
  fun h => absurd (congrFun (@h Nat (fun _ => true) (fun _ => false)) 0) (by simp [Option.guard])

-- `Option.wellFounded_lt` (`h`, idx 2): the full relation on `Unit`
theorem wellFounded_lt_h2 : ¬ ∀ {α : Type} {rel : α → α → Prop}, WellFounded (Option.lt rel) :=
  fun h => not_wf_of_refl (some ()) trivial (@h Unit (fun _ _ => True))

-- `Option.SomeLtNone.wellFounded_lt` (`h`, idx 2): the full relation on `Unit`
theorem wellFounded_lt_h2_2 : ¬ ∀ {α : Type} {r : α → α → Prop}, WellFounded (Option.SomeLtNone.lt r) :=
  fun h => not_wf_of_refl (some ()) trivial (@h Unit (fun _ _ => True))

/-! ## `Option.Basic`, `Option.Function` -/

-- `Option.instReflBEq` (`inst`, idx 2): constant-`false` `BEq Nat`
theorem instReflBEq_h2 : ¬ ∀ (α : Type) [BEq α], ReflBEq (Option α) :=
  fun h => absurd (@ReflBEq.rfl _ _ (@h Nat ⟨fun _ _ => false⟩) (some 0)) (by decide)

-- `Option.instLawfulBEq` (`inst`, idx 2): constant-`true` `BEq Nat`
theorem instLawfulBEq_h2 : ¬ ∀ (α : Type) [BEq α], LawfulBEq (Option α) :=
  fun h => absurd (@LawfulBEq.eq_of_beq _ _ (@h Nat ⟨fun _ _ => true⟩) (some 0) (some 1) rfl) (by decide)

-- `Option.map_injective` (`hf`, idx 3): constant `f`
theorem map_injective_h3 : ¬ ∀ {α : Type} {β : Type} {f : α → β}, Function.Injective (Option.map f) :=
  fun h => absurd (@h Nat Unit (fun _ => ()) (some 0) (some 1) rfl) (by simp)

/-! ## `Option.Lemmas`: `ite`/`dite`, `pbind`, `pelim`, `pfilter` -/

-- `Option.get_dite` (`w`, idx 4): dependent; `∀ β p _ b, (if h : p then some (b h) else none).isSome` fails for `p = False`
theorem get_dite_h4 : ¬ ∀ {β : Type} {p : Prop} {x : Decidable p} (b : p → β),
    (if h : p then some (b h) else none).isSome = true :=
  fun h => by have := @h Nat False instDecidableFalse False.elim; simp at this

-- `Option.get_dite'` (`w`, idx 4): dependent; fails for `p = True`
theorem get_dite'_h4 : ¬ ∀ {β : Type} {p : Prop} {x : Decidable p} (b : ¬p → β),
    (if h : p then none else some (b h)).isSome = true :=
  fun h => by have := @h Nat True instDecidableTrue (fun h => absurd trivial h); simp at this

-- `Option.get_ite` (`h`, idx 4): dependent; fails for `p = False`
theorem get_ite_h4 : ¬ ∀ {α : Type} {b : α} {p : Prop} {x : Decidable p}, (if p then some b else none).isSome = true :=
  fun h => by have := @h Nat 0 False instDecidableFalse; simp at this

-- `Option.get_ite'` (`h`, idx 4): dependent; fails for `p = True`
theorem get_ite'_h4 : ¬ ∀ {α : Type} {b : α} {p : Prop} {x : Decidable p}, (if p then none else some b).isSome = true :=
  fun h => by have := @h Nat 0 True instDecidableTrue; simp at this

-- `Option.pbind_none'` (`h`, idx 4): `x = some 0`, `f = some 0`
theorem pbind_none'_h4 : ¬ ∀ {α : Type} {x : Option α} {α_1 : Type} {f : (a : α) → x = some a → Option α_1}, x.pbind f = none :=
  fun h => absurd (@h Nat (some 0) Nat (fun _ _ => some 0)) (by simp)

-- `Option.pbind_some'` (`h`, idx 5): dependent; `∀ x a, x = some a` fails
theorem pbind_some'_h5 : ¬ ∀ {α : Type} {x : Option α} {a : α}, x = some a :=
  fun h => absurd (@h Nat none 0) (by simp)

-- `Option.pelim_none'` (`h`, idx 5): `x = some 0`, `b = 0`, `f = 1`
theorem pelim_none'_h5 : ¬ ∀ {α : Type} {x : Option α} {α_1 : Type} {b : α_1} {f : (a : α) → x = some a → α_1}, x.pelim b f = b :=
  fun h => absurd (@h Nat (some 0) Nat 0 (fun _ _ => 1)) (by simp)

-- `Option.pelim_some'` (`h`, idx 6): dependent; `∀ x a, x = some a` fails
theorem pelim_some'_h6 : ¬ ∀ {α : Type} {x : Option α} {a : α}, x = some a :=
  fun h => absurd (@h Nat none 0) (by simp)

-- `Option.pbind_congr` (`ho`, idx 4): dependent; `∀ o o', o = o'` fails
theorem pbind_congr_h4 : ¬ ∀ {α : Type} {o o' : Option α}, o = o' :=
  fun h => absurd (@h Nat none (some 0)) (by simp)

-- `Option.pbind_congr` (`hf`, idx 7): `o = o' = some 0`, `f = none`, `g = some 0`
theorem pbind_congr_h7 : ¬ ∀ {α : Type} {β : Type} {o o' : Option α} (ho : o = o')
    {f : (a : α) → o = some a → Option β} {g : (a : α) → o' = some a → Option β}, o.pbind f = o'.pbind g :=
  fun h => absurd (@h Nat Nat (some 0) (some 0) rfl (fun _ _ => none) (fun _ _ => some 0)) (by simp)

-- `Option.pelim_congr` (`ho`, idx 8): dependent; `∀ o o', o = o'` fails
-- `Option.pfilter_congr` (`ho`, idx 3): dependent; `∀ o o', o = o'` fails
-- `Option.pelim_congr_left` (`h`, idx 6): dependent; `∀ o o', o = o'` fails
-- `Option.pmap_congr` (`ho`, idx 10): dependent; `∀ o o', o = o'` fails
theorem pelim_congr_h8 : ¬ ∀ {α : Type} {o o' : Option α}, o = o' :=
  fun h => absurd (@h Nat none (some 0)) (by simp)

-- `Option.pelim_congr` (`hb`, idx 9): `o = o' = none`, `b = 0`, `b' = 1`
theorem pelim_congr_h9 : ¬ ∀ {α : Type} {β : Type} {o o' : Option α} {b b' : β} {f : (a : α) → o = some a → β}
    {g : (a : α) → o' = some a → β} (ho : o = o'),
    (∀ (a : α) (ha : o' = some a), f a (Eq.trans ho ha) = g a ha) → o.pelim b f = o'.pelim b' g :=
  fun h => absurd (@h Nat Nat none none 0 1 (fun _ _ => 0) (fun _ _ => 0) rfl (fun _ _ => rfl)) (by simp)

-- `Option.pelim_congr` (`hf`, idx 10): `o = o' = some 0`, `f = 0`, `g = 1`
theorem pelim_congr_h10 : ¬ ∀ {α : Type} {β : Type} {o o' : Option α} {b b' : β} {f : (a : α) → o = some a → β}
    {g : (a : α) → o' = some a → β} (ho : o = o'), b = b' → o.pelim b f = o'.pelim b' g :=
  fun h => absurd (@h Nat Nat (some 0) (some 0) 0 0 (fun _ _ => 0) (fun _ _ => 1) rfl rfl) (by simp)

-- `Option.pfilter_congr` (`hf`, idx 6): `o = o' = some 0`, `f = true`, `g = false`
theorem pfilter_congr_h6 : ¬ ∀ {α : Type} {o o' : Option α} (ho : o = o') {f : (a : α) → o = some a → Bool}
    {g : (a : α) → o' = some a → Bool}, o.pfilter f = o'.pfilter g :=
  fun h => absurd (@h Nat (some 0) (some 0) rfl (fun _ _ => true) (fun _ _ => false)) (by simp [Option.filter])

-- `Option.isSome_get_of_isSome_pbind` (`h`, idx 4): dependent; `(none.pbind f).isSome` is false
-- `Option.get_pbind` (`h`, idx 4): dependent; `(none.pbind f).isSome` is false
theorem isSome_get_of_isSome_pbind_h4 : ¬ ∀ {α : Type} {β : Type} {o : Option α} {f : (a : α) → o = some a → Option β},
    (o.pbind f).isSome = true :=
  fun h => absurd (@h Nat Nat none (fun _ _ => none)) (by simp)

-- `Option.get_pfilter` (`h`, idx 3): dependent; `(none.pfilter p).isSome` is false
theorem get_pfilter_h3 : ¬ ∀ {α : Type} {o : Option α} {p : (a : α) → o = some a → Bool}, (o.pfilter p).isSome = true :=
  fun h => absurd (@h Nat none (fun _ _ => true)) (by simp)

-- `Option.eq_some_of_pfilter_eq_some` (`h`, idx 4): `o = none`
theorem eq_some_of_pfilter_eq_some_h4 : ¬ ∀ {α : Type} {o : Option α} {p : (a : α) → o = some a → Bool} {a : α}, o = some a :=
  fun h => absurd (@h Nat none (fun _ _ => true) 0) (by simp)

-- `Option.unattach_pfilter` (`hf`, idx 5): `o = some ⟨0, _⟩`, `f = true`, `g = false`
theorem unattach_pfilter_h5 : ¬ ∀ {α : Type} {p : α → Prop} {o : Option { x : α // p x }}
    {f : (a : { x : α // p x }) → o = some a → Bool} {g : (a : α) → o.unattach = some a → Bool},
    (o.pfilter f).unattach = o.unattach.pfilter g :=
  fun h => absurd (@h Nat (fun _ => True) (some ⟨0, trivial⟩) (fun _ _ => true) (fun _ _ => false)) (by simp [Option.filter])

/-! ## `Option.Lemmas`, `Option.Attach`: `pmap` -/

-- `Option.pmap_some` (`h`, idx 5): dependent; fails for `p = False`
theorem pmap_some_h5 : ¬ ∀ {α : Type} {a : α} {p : α → Prop}, ∀ (a_1 : α), some a = some a_1 → p a_1 :=
  fun h => @h Nat 0 (fun _ => False) 0 rfl

-- `Option.pmap_none'` (`he`, idx 5): `x = some 0`, `p = True`
theorem pmap_none'_h5 : ¬ ∀ {α : Type} {β : Type} {x : Option α} {p : α → Prop} {f : (a : α) → p a → β}
    {h : ∀ (a : α), x = some a → p a}, Option.pmap f x h = none :=
  fun h => absurd (@h Nat Nat (some 0) (fun _ => True) (fun _ _ => 0) (fun _ _ => trivial)) (by simp)

-- `Option.pmap_some'` (`he`, idx 6): dependent; `∀ x a, x = some a` fails
theorem pmap_some'_h6 : ¬ ∀ {α : Type} {x : Option α} {a : α}, x = some a :=
  fun h => absurd (@h Nat none 0) (by simp)

-- `Option.pmap_some'` (`h`, idx 7): dependent; fails for `x = some 0`, `p = False`
-- `Option.pmap_eq_none_iff` (`h`, idx 5): dependent; fails for `o = some 0`, `p = False`
-- `Option.isSome_pmap` (`h`, idx 5): dependent; fails for `o = some 0`, `p = False`
-- `Option.isNone_pmap` (`h`, idx 5): dependent; fails for `o = some 0`, `p = False`
-- `Option.pmap_eq_some_iff` (`h`, idx 6): dependent; fails for `o = some 0`, `p = False`
-- `Option.map_pmap` (`H`, idx 7): dependent; fails for `o = some 0`, `p = False`
-- `Option.elim_pmap` (`H`, idx 6): dependent; fails for `o = some 0`, `p = False`
-- `Option.filter_pmap` (`h`, idx 5): dependent; fails for `o = some 0`, `p = False`
-- `Option.pmap_congr` (`h`, idx 11): dependent; fails for `o = some 0`, `p = False`
-- `Option.toList_pmap` (`h`, idx 5): dependent; fails for `o = some 0`, `p = False`
-- `Option.toArray_pmap` (`h`, idx 5): dependent; fails for `o = some 0`, `p = False`
theorem pmap_some'_h7 : ¬ ∀ {α : Type} {x : Option α} {p : α → Prop}, ∀ (a : α), x = some a → p a :=
  fun h => @h Nat (some 0) (fun _ => False) 0 rfl

-- `Option.pmap_eq_none_iff` (`h`, idx 5): dependent; fails for `o = some 0`, `p = False`
-- `Option.filter_pmap` (`h`, idx 5): dependent; fails for `o = some 0`, `p = False`
theorem pmap_eq_none_iff_h5 : ¬ ∀ {α : Type} {o : Option α} {p : α → Prop}, ∀ (a : α), o = some a → p a :=
  fun h => @h Nat (some 0) (fun _ => False) 0 rfl

-- `Option.isSome_pmap` (`h`, idx 5): dependent; fails for `o = some 0`, `p = False`
-- `Option.isNone_pmap` (`h`, idx 5): dependent; fails for `o = some 0`, `p = False`
-- `Option.pmap_eq_some_iff` (`h`, idx 6): dependent; fails for `o = some 0`, `p = False`
-- `Option.map_pmap` (`H`, idx 7): dependent; fails for `o = some 0`, `p = False`
-- `Option.elim_pmap` (`H`, idx 6): dependent; fails for `o = some 0`, `p = False`
-- `Option.toList_pmap` (`h`, idx 5): dependent; fails for `o = some 0`, `p = False`
-- `Option.toArray_pmap` (`h`, idx 5): dependent; fails for `o = some 0`, `p = False`
-- `Option.pmap_congr` (`h`, idx 11): dependent; fails for `o = some 0`, `p = False`
theorem isSome_pmap_h5 : ¬ ∀ {α : Type} {p : α → Prop} {o : Option α}, ∀ (a : α), o = some a → p a :=
  fun h => @h Nat (fun _ => False) (some 0) 0 rfl

-- `Option.pmap_map` (`H`, idx 7): dependent; fails for `o = some 0`, `f = id`, `p = False`
theorem pmap_map_h7 : ¬ ∀ {α : Type} {β : Type} (o : Option α) (f : α → β) {p : β → Prop},
    ∀ (a : β), Option.map f o = some a → p a :=
  fun h => @h Nat Nat (some 0) id (fun _ => False) 0 rfl

-- `Option.pmap_or` (`h`, idx 6): dependent; fails for `o = some 0`, `p = False`
theorem pmap_or_h6 : ¬ ∀ {α : Type} {p : α → Prop} {o o' : Option α}, ∀ (a : α), o.or o' = some a → p a :=
  fun h => @h Nat (fun _ => False) (some 0) none 0 rfl

-- `Option.pmap_guard` (`h`, idx 6): dependent; fails for `q = true`, `p = False`
theorem pmap_guard_h6 : ¬ ∀ {α : Type} {q : α → Bool} {p : α → Prop} {x : α}, ∀ (a : α), Option.guard q x = some a → p a :=
  fun h => @h Nat (fun _ => true) (fun _ => False) 0 0 rfl

-- `Option.pmap_congr` (`hp`, idx 4): dependent; `∀ p p', ∀ x, p x ↔ p' x` fails
theorem pmap_congr_h4 : ¬ ∀ {α : Type} {p p' : α → Prop}, ∀ (x : α), p x ↔ p' x :=
  fun h => (@h Nat (fun _ => True) (fun _ => False) 0).1 trivial

-- `Option.pmap_congr` (`hf`, idx 7): `p = p' = True`, `o = o' = some 0`, `f = 0`, `f' = 1`
theorem pmap_congr_h7 : ¬ ∀ {α : Type} {β : Type} {p p' : α → Prop} (hp : ∀ (x : α), p x ↔ p' x)
    {f : (x : α) → p x → β} {f' : (x : α) → p' x → β} {o o' : Option α} (ho : o = o')
    {h : ∀ (x : α), o = some x → p x},
    Option.pmap f o h = Option.pmap f' o' (Option.pmap_pred_congr hp ho h) :=
  fun h => absurd (@h Nat Nat (fun _ => True) (fun _ => True) (fun _ => Iff.rfl) (fun _ _ => 0)
    (fun _ _ => 1) (some 0) (some 0) rfl (fun _ _ => trivial)) (by simp)

-- `Option.get_pmap` (`h`, idx 5): dependent; fails for `o = some 0`, `p = false`
theorem get_pmap_h5 : ¬ ∀ {α : Type} {p : α → Bool} {o : Option α}, ∀ (a : α), o = some a → p a = true :=
  fun h => absurd (@h Nat (fun _ => false) (some 0) 0 rfl) (by simp)

-- `Option.get_pmap` (`h'`, idx 6): dependent; `(pmap f none h).isSome` is false
theorem get_pmap_h6 : ¬ ∀ {α : Type} {β : Type} {p : α → Bool} {f : (x : α) → p x = true → β} {o : Option α}
    {h : ∀ (a : α), o = some a → p a = true}, (Option.pmap f o h).isSome = true :=
  fun h => absurd (@h Nat Nat (fun _ => true) (fun _ _ => 0) none (fun _ h => nomatch h)) (by simp)

/-! ## `Option.Monadic` -/

-- `Option.forIn'_congr` (`inst`, idx 4): removable. With `as = bs` and `b = b'` substituted, `h`
-- says `f = g` pointwise (the membership proofs agree by proof irrelevance), so both loops are equal
-- in any monad.
theorem forIn'_congr_h4 {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [Monad m]
    {as bs : Option α} (w : as = bs) {b b' : β} (hb : b = b')
    {f : (a' : α) → a' ∈ as → β → m (ForInStep β)}
    {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)}
    (h : ∀ a m b, f a (by simpa [w] using m) b = g a m b) :
    forIn' as b f = forIn' bs b' g := by
  subst w; subst hb
  have : f = g := funext fun a => funext fun hm => funext fun b => h a hm b
  rw [this]

-- `Option.forIn'_congr` (`w`, idx 7): dependent; `∀ as bs, as = bs` fails
theorem forIn'_congr_h7 : ¬ ∀ {α : Type} {as bs : Option α}, as = bs :=
  fun h => absurd (@h Nat none (some 0)) (by simp)

-- `Option.forIn'_congr` (`hb`, idx 10): `as = bs = none` in `Id`, `b = 0`, `b' = 1`
theorem forIn'_congr_h10 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [Monad m] [LawfulMonad m]
    {as bs : Option α} (w : as = bs) {b b' : β}
    {f : (a' : α) → a' ∈ as → β → m (ForInStep β)}
    {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)},
    (∀ a m b, f a (by simpa [w] using m) b = g a m b) →
    forIn' as b f = forIn' bs b' g :=
  fun h => absurd (show (0 : Nat) = 1 from @h Id Nat Nat _ _ none none rfl 0 1 (fun _ _ b => pure (.yield b))
    (fun _ _ b => pure (.yield b)) (fun _ _ _ => rfl)) (by decide)

-- `Option.forIn'_congr` (`h`, idx 13): `as = bs = some 0` in `Id`, `f` returns `0`, `g` returns `1`
theorem forIn'_congr_h13 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [Monad m] [LawfulMonad m]
    {as bs : Option α} (w : as = bs) {b b' : β}, b = b' →
    ∀ {f : (a' : α) → a' ∈ as → β → m (ForInStep β)}
    {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)},
    forIn' as b f = forIn' bs b' g :=
  fun h => absurd (show (0 : Nat) = 1 from @h Id Nat Nat _ _ (some 0) (some 0) rfl 0 0 rfl (fun _ _ _ => pure (.done 0))
    (fun _ _ _ => pure (.done 1))) (by decide)

-- `Option.forIn'_some` (`inst`, idx 4): removable. `forIn' (some a)` is by definition `bind` of
-- `f a rfl b` with a continuation that agrees with `pure ∘ ForInStep.value` on both constructors.
theorem forIn'_some_h4 {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [Monad m] (a : α)
    (b : β) (f : (a' : α) → a' ∈ some a → β → m (ForInStep β)) :
    forIn' (some a) b f = bind (f a rfl b) (fun r => pure (ForInStep.value r)) := by
  show bind _ _ = bind _ _
  congr 1; funext r; cases r <;> rfl

-- `Option.forIn_some` (`inst`, idx 4): removable, as `forIn'_some` (`forIn` is `forIn'` by definition).
theorem forIn_some_h4 {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_1} [Monad m] (a : α)
    (b : β) (f : α → β → m (ForInStep β)) :
    forIn (some a) b f = bind (f a b) (fun r => pure (ForInStep.value r)) := by
  show bind _ _ = bind _ _
  congr 1; funext r; cases r <;> rfl

-- `Option.forIn'_map` (`inst`, idx 6): removable. `Option.map g` preserves the constructor, so both
-- loops unfold to the same term (the membership proofs agree by proof irrelevance).
theorem forIn'_map_h6 {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_4} {γ : Type u_1} {init : γ}
    [Monad m] (o : Option α) (g : α → β) (f : (b : β) → b ∈ o.map g → γ → m (ForInStep γ)) :
    forIn' (o.map g) init f = forIn' o init fun a h y => f (g a) (Option.mem_map_of_mem g h) y := by
  cases o <;> rfl

-- `Option.forIn_map` (`inst`, idx 6): removable, as `forIn'_map`.
theorem forIn_map_h6 {m : Type u_1 → Type u_2} {α : Type u_3} {β : Type u_4} {γ : Type u_1} {init : γ}
    [Monad m] (o : Option α) (g : α → β) (f : β → γ → m (ForInStep γ)) :
    forIn (o.map g) init f = forIn o init fun a y => f (g a) y := by
  cases o <;> rfl

-- `Option.forIn'_eq_pelim` (`inst`, idx 4): `NatM`, `o = some 0`: `bind` counts 1, `<$>` counts 0
theorem forIn'_eq_pelim_h4 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [Monad m]
    (o : Option α) (f : (a : α) → a ∈ o → β → m (ForInStep β)) (b : β),
    forIn' o b f = o.pelim (pure b) (fun a h => ForInStep.value <$> f a h b) :=
  fun h => absurd (show (1 : Nat) = 0 from @h NatM Nat Nat _ (some 0) (fun _ _ _ => pure (.yield 0)) 0) (by decide)

-- `Option.forIn'_yield_eq_pelim` (`inst`, idx 5): `NatM`, `o = some 0`
theorem forIn'_yield_eq_pelim_h5 : ¬ ∀ {m : Type → Type} {α : Type} {β γ : Type} [Monad m] (o : Option α)
    (f : (a : α) → a ∈ o → β → m γ) (g : (a : α) → a ∈ o → β → γ → β) (b : β),
    (forIn' o b fun a hm b => (fun c => ForInStep.yield (g a hm b c)) <$> f a hm b) =
      o.pelim (pure b) (fun a h => g a h b <$> f a h b) :=
  fun h => absurd (show (1 : Nat) = 0 from @h NatM Nat Nat Nat _ (some 0) (fun _ _ _ => pure 0) (fun _ _ _ _ => 0) 0) (by decide)

-- `Option.forIn'_pure_yield_eq_pelim` (`inst`, idx 4): `NatM`, `o = some 0`
theorem forIn'_pure_yield_eq_pelim_h4 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [Monad m]
    (o : Option α) (f : (a : α) → a ∈ o → β → β) (b : β),
    (forIn' o b fun a hm b => pure (ForInStep.yield (f a hm b))) =
      pure (f := m) (o.pelim b (fun a h => f a h b)) :=
  fun h => absurd (show (1 : Nat) = 0 from @h NatM Nat Nat _ (some 0) (fun _ _ _ => 0) 0) (by decide)

-- `Option.forIn'_join` (`inst`, idx 4): `NatM`, `o = some (some 0)`: one bind on the left, two on the right
theorem forIn'_join_h4 : ¬ ∀ {m : Type → Type} {β : Type} {α : Type} [Monad m] (b : β)
    (o : Option (Option α)) (f : (a : α) → a ∈ o.join → β → m (ForInStep β)),
    forIn' o.join b f = forIn' o b (fun o' ho' b => ForInStep.yield <$>
      forIn' o' b (fun a ha b' => f a (by simp_all) b')) :=
  fun h => absurd (show (1 : Nat) = 2 from @h NatM Nat Nat _ 0 (some (some 0)) (fun _ _ _ => pure (.yield 0)))
    (by decide)

-- `Option.forIn_eq_elim` (`inst`, idx 4): `NatM`, `o = some 0`
theorem forIn_eq_elim_h4 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [Monad m]
    (o : Option α) (f : (a : α) → β → m (ForInStep β)) (b : β),
    forIn o b f = o.elim (pure b) (fun a => ForInStep.value <$> f a b) :=
  fun h => absurd (show (1 : Nat) = 0 from @h NatM Nat Nat _ (some 0) (fun _ _ => pure (.yield 0)) 0) (by decide)

-- `Option.elimM_bind` (`inst`, idx 5): `NatM`: two binds on the left, one on the right
theorem elimM_bind_h5 : ¬ ∀ {m : Type → Type} {α β γ : Type} [Monad m] (x : m α)
    (f : α → m (Option β)) (y : m γ) (z : β → m γ),
    Option.elimM (x >>= f) y z = (do Option.elimM (f (← x)) y z) :=
  fun h => absurd (show (2 : Nat) = 1 from @h NatM Nat Nat Nat _ (show Nat from 0) (fun _ => show Nat from 0) (show Nat from 0)
    (fun _ => show Nat from 0)) (by decide)

-- `Option.sequence_join` (`inst`, idx 3): `CntA`, `o = some none`: no map on the left, two on the right
theorem sequence_join_h3 : ¬ ∀ {m : Type → Type} {α : Type} [Applicative m] {o : Option (Option (m α))},
    o.join.sequence = Option.join <$> (Option.map Option.sequence o).sequence :=
  fun h => absurd (show (0 : Nat) = 2 from @h CntA Nat _ (some none)) (by decide)

-- `Option.mapM_join` (`inst`, idx 4): `CntA`, `o = some none`
theorem mapM_join_h4 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [Applicative m] {f : α → m β}
    {o : Option (Option α)}, Option.mapM f o.join = Option.join <$> Option.mapM (Option.mapM f) o :=
  fun h => absurd (show (0 : Nat) = 2 from @h CntA Nat Nat _ (fun _ => show Nat from 0) (some none)) (by decide)

/-! ## `Option.Attach` -/

-- `Option.filterM_unattach` (`inst`, idx 3): `CntA`, `o = none`: no map on the left, one on the right
theorem filterM_unattach_h3 : ¬ ∀ {m : Type → Type} {α : Type} [Applicative m] {P : α → Prop} {o : Option (Subtype P)}
    {p : α → m Bool},
    o.unattach.filterM p = Option.unattach <$> o.filterM fun ⟨x, h⟩ =>
      binderNameHint x p <| binderNameHint h () <| p (wfParam x) :=
  fun h => absurd (show (0 : Nat) = 1 from @h CntA Nat _ (fun _ => True) none (fun _ => show Nat from 0))
    (by decide)

-- `OptionT.instWeaklyLawfulMonadAttachOfLawfulMonad` (`inst`, idx 3): `NatM` (lawful attach,
-- non-lawful monad); in `OptionT NatM`, `Subtype.val <$> attach x` adds a bind
theorem instWeaklyLawfulMonadAttachOfLawfulMonad_h3 : ¬ ∀ {m : Type → Type} [Monad m] [MonadAttach m] [WeaklyLawfulMonadAttach m],
    WeaklyLawfulMonadAttach (OptionT m) :=
  fun h => absurd (show (1 : Nat) = 0 from (@h NatM _ _ _).map_attach (α := Nat) (x := show Nat from 0)) (by decide)

-- `OptionT.instLawfulMonadAttachOfLawfulMonad` (`inst`, idx 3): `NatM`, as above
theorem instLawfulMonadAttachOfLawfulMonad_h3 : ¬ ∀ {m : Type → Type} [Monad m] [MonadAttach m] [LawfulMonadAttach m],
    LawfulMonadAttach (OptionT m) :=
  fun h => absurd (show (1 : Nat) = 0 from (@h NatM _ _ _).map_attach (α := Nat) (x := show Nat from 0)) (by decide)

-- `OptionT.instWeaklyLawfulMonadAttachOfLawfulMonad` (`inst`, idx 4): `BadOpt` (lawful monad,
-- `attach` always `none`)
theorem instWeaklyLawfulMonadAttachOfLawfulMonad_h4 : ¬ ∀ {m : Type → Type} [Monad m] [MonadAttach m] [LawfulMonad m],
    WeaklyLawfulMonadAttach (OptionT m) :=
  fun h => absurd (show (none : Option (Option Nat)) = some (some 0) from (@h BadOpt _ _ _).map_attach (x := (some (some 0) : Option (Option Nat)))) (by decide)

-- `OptionT.instLawfulMonadAttachOfLawfulMonad` (`inst`, idx 4): `BadOpt`, as above
theorem instLawfulMonadAttachOfLawfulMonad_h4 : ¬ ∀ {m : Type → Type} [Monad m] [MonadAttach m] [LawfulMonad m],
    LawfulMonadAttach (OptionT m) :=
  fun h => absurd (show (none : Option (Option Nat)) = some (some 0) from (@h BadOpt _ _ _).map_attach (x := (some (some 0) : Option (Option Nat)))) (by decide)

end RestOptionHand
