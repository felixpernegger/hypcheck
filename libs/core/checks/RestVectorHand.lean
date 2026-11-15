import Lean

/-!
Hand resolution of the 86 remaining unresolved hypotheses of `Init.Data.Vector.*` (cluster
`Vector`, todo list `runs/hand5/todo_Vector.jsonl`). For each hypothesis `hᵢ` of theorem `T`, this
file proves `T'` (removable), `¬T'` (necessary), or, for a dependent hypothesis, `¬∀ indep, Hᵢ`
(in the variant that quantifies only over the binders `Hᵢ` mentions, closed under their types).

Removable (5):
* `Vector.flatMap_lt_flatMap_iff`, `Vector.flatMap_le_flatMap_iff` (`hm : 0 < m`): for `m = 0`
  every `f a` is the empty vector, so `hf` forces `<` on `α` to be empty; then both sides of `<`
  are false (vectors of equal length can only be lexicographically smaller at some `a < b`), and
  both sides of `≤` are true. The `Array`/`List` versions need `hm`, because there the lengths of
  `xs` and `ys` may differ.
* `Vector.foldrM_map`, `Vector.foldrM_attachWith` (`[LawfulMonad m]`): `Array.foldrM` runs the same
  loop on both arrays (same size) and calls the step function on `as[i]`; the step functions agree
  pointwise (`f` applied to `(xs.map g)[i]` is `f (g xs[i])`), so the two folds are equal in every
  monad (`foldrM_congr`).
* `Vector.mapM_map` (`[LawfulMonad m]`): likewise, `Vector.mapM` is a loop (`mapM.go`, private)
  that calls `g (xs.map f)[k] = g (f xs[k])`; induction over the loop (`mapM_go_map`). The private
  `Vector.mapM.go` and its equation are reached by two tiny term elaborators (hence `import Lean`).

All 81 others are necessary. Models:
* `WM`: `Nat × α` with `pure a = (0, a)` and `bind x f = (2 * x.1 + (f x.2).1 + 1, (f x.2).2)`
  (violates `pure_bind`, `bind_pure`, `bind_assoc`; `map` is the default `bind x (pure ∘ f)`, so
  it violates `id_map` too). Decidable equality, so loops evaluate with `decide +kernel`.
* `TM t`: `Nat × α`, writer `pure`/`bind` (lawful as a monad), but `map f x` adds `t β` where `β`
  is the result type (violates `id_map` and `bind_pure_comp`). With `t := tag`
  (`tag β = if β = Unit then 1 else 0`, classical) `map` behaves differently when mapping into
  `ForInStep Unit` and into `Unit`, which separates `forIn'`/`forIn` with a mapped body from
  `foldlM` (both run the same binds; only the result types of the `map`s differ, so no
  parametric monad separates them).
* `Option` for the congruence lemmas `forIn'_congr`, `forM_congr`.
* Orders: `NH` (`Nat` with `a < b ↔ a / 2 < b / 2`; `f = (· / 2) : NH → Nat` reflects and
  preserves `<` but is not injective), `NF` (`<` everywhere false; `id : Nat → NF` is injective,
  not monotone).
* Algebra on `Nat` (all with `n = 1`): `a + b + 1` (no identity), left projection
  (not commutative), `2a + b` (not associative), `-a = a + 1` (`-0 ≠ 0`), `-a = a`
  (`-1 + 1 ≠ 0`, `1 - 1 ≠ 1 + -1`), `*`/`•`/heterogeneous `*` as `+` (no absorbing `0`, not
  distributive).
* Dependent side conditions (`∀ a ∈ xs, p a`, `i < n`, `xs.size = n`, `xs = ys`, `a ∈ xs`) are
  refuted with `p := fun _ => False`, `xs := #v[0]`, `n = 0`, etc.

Run with the lean4 repo's stage1 binary: `lean checks/RestVectorHand.lean`.
-/

set_option warn.classDefReducibility false
set_option linter.unusedVariables false

universe u v w x

namespace RestVectorHand

/-! ## Monads -/

/-- Weighted bind count: `bind x f = (2 * x.1 + (f x.2).1 + 1, _)`, `pure a = (0, a)`. -/
def WM (α : Type) : Type := Nat × α
instance : Monad WM where
  pure a := ((0 : Nat), a)
  bind x f := (2 * (show Nat × _ from x).1 + (show Nat × _ from f x.2).1 + 1,
    (show Nat × _ from f x.2).2)
instance [DecidableEq α] : DecidableEq (WM α) := inferInstanceAs (DecidableEq (Nat × α))
def wm (k : Nat) (a : α) : WM α := (k, a)

/-- Writer `pure`/`bind`, but `map` adds `t β` for the result type `β`. -/
def TM (t : Type → Nat) (α : Type) : Type := Nat × α
instance (t : Type → Nat) : Monad (TM t) where
  pure a := ((0 : Nat), a)
  bind x f := ((show Nat × _ from x).1 + (show Nat × _ from f x.2).1, (show Nat × _ from f x.2).2)
  map {_ β} f x := (t β + (show Nat × _ from x).1, f x.2)

theorem forInStep_ne_unit : ForInStep Unit ≠ Unit := by
  intro h
  have e : cast h (ForInStep.yield ()) = cast h (ForInStep.done ()) := Subsingleton.elim _ _
  have : ForInStep.yield () = (ForInStep.done () : ForInStep Unit) := by
    have := congrArg (cast h.symm) e
    simp at this
  cases this

open Classical in
/-- Separates `Unit` from `ForInStep Unit`. -/
noncomputable def tag (β : Type) : Nat := if β = Unit then 1 else 0

theorem tag_unit : tag Unit = 1 := by simp [tag]
theorem tag_fis : tag (ForInStep Unit) = 0 := by simp [tag, forInStep_ne_unit]

/-! ## Order models -/

def half (a : Nat) : Nat := a / 2

/-- `Nat` ordered by `half a < half b`. -/
def NH := Nat
instance : LT NH := ⟨fun a b => half a < half b⟩
instance : DecidableLT NH := fun a b => Nat.decLt (half a) (half b)
instance : DecidableEq NH := inferInstanceAs (DecidableEq Nat)
instance : OfNat NH n := ⟨(n : Nat)⟩

/-- `Nat` with `<` everywhere false. -/
def NF := Nat
instance : LT NF := ⟨fun _ _ => False⟩
instance : DecidableLT NF := fun _ _ => (isFalse id : Decidable False)
instance : DecidableEq NF := inferInstanceAs (DecidableEq Nat)
instance : OfNat NF n := ⟨(n : Nat)⟩

/-! ## Algebra models on `Nat` -/

/-- `a + b + 1`: no identity. -/
def addS : Add Nat := ⟨fun a b => a + b + 1⟩
/-- Left projection: not commutative. -/
def addL : Add Nat := ⟨fun a _ => a⟩
def mulL : Mul Nat := ⟨fun a _ => a⟩
/-- `2a + b`: not associative. -/
def add2 : Add Nat := ⟨fun a b => 2 * a + b⟩
def mul2 : Mul Nat := ⟨fun a b => 2 * a + b⟩
/-- `-a = a + 1`: `-0 ≠ 0`. -/
def negS : Neg Nat := ⟨fun a => a + 1⟩
/-- `-a = a`. -/
def negId : Neg Nat := ⟨id⟩
/-- Products as sums: `0` is not absorbing, no distributivity. -/
def mulA : Mul Nat := ⟨fun a b => a + b⟩
def hmulA : HMul Nat Nat Nat := ⟨fun a b => a + b⟩
def smulA : SMul Nat Nat := ⟨fun a b => a + b⟩

/-! ## Removable -/

/-- A lexicographic order with an empty element relation is empty on lists of equal length. -/
theorem not_lex_of_empty {α : Type u} {r : α → α → Prop} (hr : ∀ a b, ¬ r a b) :
    ∀ {l₁ l₂ : List α}, l₁.length = l₂.length → ¬ List.Lex r l₁ l₂ := by
  intro l₁ l₂ hl h
  induction h with
  | nil => simp at hl
  | rel h => exact hr _ _ h
  | cons _ ih => exact ih (by simpa using hl)

theorem vector_not_lt_of_empty {α : Type u} [LT α] (hr : ∀ a b : α, ¬ a < b) {n : Nat}
    (xs ys : Vector α n) : ¬ xs < ys :=
  not_lex_of_empty hr (by simp)

theorem vec0_not_lt {β : Type v} [LT β] (xs ys : Vector β 0) : ¬ xs < ys := by
  intro h
  have h' : xs.toList < ys.toList := h
  have hx : xs.toList = [] := by simp
  have hy : ys.toList = [] := by simp
  rw [hx, hy] at h'
  exact List.not_lt_nil _ h'

-- `Vector.flatMap_lt_flatMap_iff` (`hm : 0 < m`): removable. For `m = 0`, `hf` makes `<` on `α`
-- empty, and both sides are false.
theorem flatMap_lt_flatMap_iff {α : Type u} {β : Type v} {m n : Nat} [inst : LT α]
    [Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
    [Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → Vector β m)
    (hf : ∀ (a b : α), a < b → f a < f b) {xs ys : Vector α n} :
    xs.flatMap f < ys.flatMap f ↔ xs < ys := by
  by_cases hm : 0 < m
  · exact Vector.flatMap_lt_flatMap_iff f hf hm
  · have hm0 : m = 0 := by omega
    subst hm0
    have hr : ∀ a b : α, ¬ a < b := fun a b h => vec0_not_lt _ _ (hf a b h)
    exact ⟨fun h => absurd h (vec0_not_lt _ _), fun h => absurd h (vector_not_lt_of_empty hr _ _)⟩

-- `Vector.flatMap_le_flatMap_iff` (`hm : 0 < m`): removable. For `m = 0`, `hf` makes `<` on `α`
-- empty, and both sides are true.
theorem flatMap_le_flatMap_iff {α : Type u} {β : Type v} {m n : Nat} [inst : LT α]
    [Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
    [Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → Vector β m)
    (hf : ∀ (a b : α), a < b → f a < f b) {xs ys : Vector α n} :
    xs.flatMap f ≤ ys.flatMap f ↔ xs ≤ ys := by
  by_cases hm : 0 < m
  · exact Vector.flatMap_le_flatMap_iff f hf hm
  · have hm0 : m = 0 := by omega
    subst hm0
    have hr : ∀ a b : α, ¬ a < b := fun a b h => vec0_not_lt _ _ (hf a b h)
    exact ⟨fun _ => vector_not_lt_of_empty hr ys xs, fun _ => vec0_not_lt _ _⟩

theorem foldrM_fold_congr {m : Type v → Type w} [Monad m] {α : Type u} {γ : Type x} {β : Type v}
    (f : α → β → m β) (g : γ → β → m β) (as : Array α) (bs : Array γ) (stop : Nat)
    (hfg : ∀ i (h1 : i < as.size) (h2 : i < bs.size), f as[i] = g bs[i]) :
    ∀ (i j : Nat) (hij : i = j) (h1 : i ≤ as.size) (h2 : j ≤ bs.size) (b : β),
      Array.foldrM.fold f as stop i h1 b = Array.foldrM.fold g bs stop j h2 b := by
  intro i j hij
  subst hij
  induction i with
  | zero => intro h1 h2 b; simp [Array.foldrM.fold]
  | succ i ih =>
    intro h1 h2 b
    rw [Array.foldrM.fold, Array.foldrM.fold]
    split
    · rfl
    · simp only
      rw [hfg i (by omega) (by omega)]
      congr
      funext b'
      exact ih _ _ b'

/-- `Array.foldrM` with pointwise equal step functions on arrays of equal size, in any monad. -/
theorem foldrM_congr {m : Type v → Type w} [Monad m] {α : Type u} {γ : Type x} {β : Type v}
    (f : α → β → m β) (g : γ → β → m β) (as : Array α) (bs : Array γ) (hs : as.size = bs.size)
    (hfg : ∀ i (h1 : i < as.size) (h2 : i < bs.size), f as[i] = g bs[i]) (init : β) :
    as.foldrM f init = bs.foldrM g init := by
  unfold Array.foldrM
  simp only [Nat.le_refl, dite_true]
  split <;> split
  · exact foldrM_fold_congr f g as bs 0 hfg _ _ hs _ _ init
  · omega
  · omega
  · rfl

-- `Vector.foldrM_map` (`[LawfulMonad m]`): removable. Both folds run the same loop with pointwise
-- equal steps (`foldrM_congr`).
theorem foldrM_map {m : Type u → Type v} {β₁ : Type w} {β₂ : Type x} {α : Type u} {n : Nat}
    [inst : Monad m] {f : β₁ → β₂} {g : β₂ → α → m α} {xs : Vector β₁ n} {init : α} :
    Vector.foldrM g init (Vector.map f xs) =
      Vector.foldrM (fun (x : β₁) (y : α) => g (f x) y) init xs :=
  foldrM_congr _ _ _ _ (by simp) (fun i h1 h2 => by simp) init

-- `Vector.foldrM_attachWith` (`[LawfulMonad m]`): removable. Both folds run the same loop with
-- pointwise equal steps (`foldrM_congr`).
theorem foldrM_attachWith {m : Type u → Type v} {α : Type w} {n : Nat} {β : Type u}
    [inst : Monad m] {xs : Vector α n} {q : α → Prop} (H : ∀ (a : α), a ∈ xs → q a)
    {f : { x : α // q x } → β → m β} {b : β} :
    Vector.foldrM f b (xs.attachWith q H) =
      Vector.foldrM (fun (a : { x : α // x ∈ xs }) (acc : β) => f ⟨a.val, H a.val a.property⟩ acc)
        b xs.attach :=
  foldrM_congr _ _ _ _ (by simp) (fun i h1 h2 => by simp) b

open Lean Elab Term Meta in
/-- The private `Vector.mapM.go` of `Init.Data.Vector.Basic`. -/
elab "vecMapMGo%" : term =>
  mkConstWithFreshMVarLevels
    (.str (.str (.str (.num `_private.Init.Data.Vector.Basic 0) "Vector") "mapM") "go")

open Lean Elab Term Meta in
/-- The unfolding equation of the private `Vector.mapM.go`. -/
elab "vecMapMGoEq%" : term =>
  mkConstWithFreshMVarLevels
    (.str (.str (.str (.str (.num `_private.Init.Data.Vector.Basic 0) "Vector") "mapM") "go")
      "eq_def")

theorem mapM_go_map {m : Type u → Type v} {α : Type w} {β : Type x} {γ : Type u} {n : Nat}
    [inst : Monad m] (f : α → β) (g : β → m γ) (xs : Vector α n) (k : Nat) (hk : k ≤ n)
    (acc : Vector γ k) :
    (vecMapMGo%) g (Vector.map f xs) k hk acc = (vecMapMGo%) (g ∘ f) xs k hk acc := by
  rw [vecMapMGoEq%, vecMapMGoEq%]
  split
  · simp only [Vector.getElem_map, Function.comp]
    congr
    funext y
    exact mapM_go_map f g xs (k + 1) _ _
  · rfl
termination_by n - k

-- `Vector.mapM_map` (`[LawfulMonad m]`): removable. `mapM` is a loop calling
-- `g (xs.map f)[k] = g (f xs[k])` (`mapM_go_map`).
theorem mapM_map {m : Type u → Type v} {α : Type w} {β : Type x} {γ : Type u} {n : Nat}
    [inst : Monad m] {f : α → β} {g : β → m γ} {xs : Vector α n} :
    Vector.mapM g (Vector.map f xs) = Vector.mapM (g ∘ f) xs :=
  mapM_go_map f g xs 0 _ _

end RestVectorHand

open RestVectorHand

/-! ## Necessary: monads -/

-- `Vector.foldlM_push` (`[LawfulMonad m]`): `WM`, `xs = #v[]`, step `(1, b)`: 3 vs 2.
example : ¬ ∀ {m : Type → Type} {α : Type} {n : Nat} {β : Type} [inst : Monad m]
    {xs : Vector α n} {a : α} {f : β → α → m β} {b : β},
    Vector.foldlM f b (xs.push a) = (do let b ← Vector.foldlM f b xs; f b a) := by
  intro H
  have := @H WM Nat 0 Nat _ #v[] 0 (fun b _ => wm 1 b) 0
  revert this; decide +kernel

-- `Vector.toArray_mapFinIdxM` (`[LawfulMonad m]`): `WM`, `xs = #v[]`: the extra `map` adds a bind.
example : ¬ ∀ {m : Type → Type} {α : Type} {n : Nat} {β : Type} [inst : Monad m]
    {xs : Vector α n} {f : (i : Nat) → α → i < n → m β},
    Vector.toArray <$> xs.mapFinIdxM f =
      xs.toArray.mapFinIdxM fun (i : Nat) (x : α) (h : i < xs.toArray.size) =>
        f i x (xs.size_toArray ▸ h) := by
  intro H
  have := @H WM Nat 0 Nat _ #v[] (fun _ a _ => wm 0 a)
  revert this; decide +kernel

-- `Vector.forIn'_yield_eq_foldlM` (`[LawfulMonad m]`): `TM tag`, `xs = #v[()]`, `β = γ = Unit`:
-- the left side maps into `ForInStep Unit`, the right side into `Unit`.
example : ¬ ∀ {m : Type → Type} {α : Type} {n : Nat} {β γ : Type} [inst : Monad m]
    {xs : Vector α n} (f : (a : α) → a ∈ xs → β → m γ) (g : (a : α) → a ∈ xs → β → γ → β)
    (init : β),
    (forIn' xs init fun (a : α) (m_1 : a ∈ xs) (b : β) =>
        (fun (c : γ) => ForInStep.yield (g a m_1 b c)) <$> f a m_1 b) =
      Vector.foldlM
        (fun (b : β) (x : { x : α // x ∈ xs }) =>
          match x with
          | ⟨a, m_1⟩ => g a m_1 b <$> f a m_1 b)
        init xs.attach := by
  intro H
  have h1 := @H (TM tag) Unit 1 Unit Unit _ #v[()] (fun _ _ _ => ((0 : Nat), ()))
    (fun _ _ _ _ => ()) ()
  have h2 : (tag (ForInStep Unit) + 0 + 0, ()) = (tag Unit + 0 + 0, ()) := h1
  simp [tag_unit, tag_fis] at h2

-- `Vector.forIn_yield_eq_foldlM` (`[LawfulMonad m]`): as for `forIn'_yield_eq_foldlM`.
example : ¬ ∀ {m : Type → Type} {α : Type} {n : Nat} {β γ : Type} [inst : Monad m]
    {xs : Vector α n} (f : α → β → m γ) (g : α → β → γ → β) (init : β),
    (forIn xs init fun (a : α) (b : β) => (fun (c : γ) => ForInStep.yield (g a b c)) <$> f a b) =
      Vector.foldlM (fun (b : β) (a : α) => g a b <$> f a b) init xs := by
  intro H
  have h1 := @H (TM tag) Unit 1 Unit Unit _ #v[()] (fun _ _ => ((0 : Nat), ())) (fun _ _ _ => ()) ()
  have h2 : (tag (ForInStep Unit) + 0 + 0, ()) = (tag Unit + 0 + 0, ()) := h1
  simp [tag_unit, tag_fis] at h2

-- `Vector.forIn'_pure_yield_eq_foldl` (`[LawfulMonad m]`): `WM`, `xs = #v[0]`: one bind vs none.
example : ¬ ∀ {m : Type → Type} {α : Type} {n : Nat} {β : Type}
    [inst : Monad m] {xs : Vector α n} (f : (a : α) → a ∈ xs → β → β) (init : β),
    (forIn' xs init fun (a : α) (m_1 : a ∈ xs) (b : β) => pure (ForInStep.yield (f a m_1 b))) =
      pure (f := m)
        (Vector.foldl
          (fun (b : β) (x : { x : α // x ∈ xs }) =>
            match x with
            | ⟨a, h⟩ => f a h b)
          init xs.attach) := by
  intro H
  have := @H WM Nat 1 Nat _ #v[0] (fun _ _ b => b) 0
  revert this; decide +kernel

-- `Vector.forIn'_eq_foldlM` (`[LawfulMonad m]`): `WM`, `xs = #v[]`: the outer `map` adds a bind.
example : ¬ ∀ {m : Type → Type} {α : Type} {n : Nat} {β : Type} [inst : Monad m]
    {xs : Vector α n} (f : (a : α) → a ∈ xs → β → m (ForInStep β)) (init : β),
    forIn' xs init f =
      ForInStep.value <$>
        Vector.foldlM
          (fun (b : ForInStep β) (x : { x : α // x ∈ xs }) =>
            match x with
            | ⟨a, m_1⟩ =>
              match b with
              | ForInStep.yield b => f a m_1 b
              | ForInStep.done b => pure (ForInStep.done b))
          (ForInStep.yield init) xs.attach := by
  intro H
  have := @H WM Nat 0 Nat _ #v[] (fun _ _ b => wm 0 (.yield b)) 0
  revert this; decide +kernel

-- `Vector.forM_congr` (`w : as = bs`): `Option`, `#v[0]` vs `#v[1]`, `f a = if a = 0 then none`.
example : ¬ ∀ {m : Type → Type} {α : Type} {n : Nat} [inst : Monad m] {as bs : Vector α n}
    {f : α → m PUnit}, forM as f = forM bs f := by
  intro H
  have := @H Option Nat 1 _ #v[0] #v[1] (fun a => if a = 0 then none else some ⟨⟩)
  revert this; decide +kernel

-- `Vector.forIn'_congr` (`w : xs = ys`, dependent): `#v[0] ≠ #v[1]`.
example : ¬ ∀ {α : Type} {n : Nat} {xs ys : Vector α n}, xs = ys :=
  fun H => absurd (@H Nat 1 #v[0] #v[1]) (by decide)

-- `Vector.forIn'_congr` (`hb : b = b'`): `Option`, `xs = ys = #v[]`, `b = 0`, `b' = 1`.
example : ¬ ∀ {m : Type → Type} {α : Type} {n : Nat} {β : Type} [inst : Monad m]
    {xs ys : Vector α n} (w : xs = ys) {b b' : β}
    {f : (a' : α) → a' ∈ xs → β → m (ForInStep β)} {g : (a' : α) → a' ∈ ys → β → m (ForInStep β)},
    (∀ (a : α) (m_1 : a ∈ ys) (b : β), f a (by subst w; exact m_1) b = g a m_1 b) →
      forIn' xs b f = forIn' ys b' g := by
  intro H
  have := @H Option Nat 0 Nat _ #v[] #v[] rfl 0 1 (fun _ _ b => some (.yield b))
    (fun _ _ b => some (.yield b)) (fun _ _ _ => rfl)
  revert this; decide +kernel

-- `Vector.forIn'_congr` (`h`): `Option`, `xs = ys = #v[0]`, `f` stops with `0`, `g` with `1`.
example : ¬ ∀ {m : Type → Type} {α : Type} {n : Nat} {β : Type} [inst : Monad m]
    {xs ys : Vector α n} (w : xs = ys) {b b' : β}, b = b' →
    ∀ {f : (a' : α) → a' ∈ xs → β → m (ForInStep β)}
      {g : (a' : α) → a' ∈ ys → β → m (ForInStep β)},
      forIn' xs b f = forIn' ys b' g := by
  intro H
  have := @H Option Nat 1 Nat _ #v[0] #v[0] rfl 0 0 rfl (fun _ _ _ => some (.done 0))
    (fun _ _ _ => some (.done 1))
  revert this; decide +kernel

/-! ## Necessary: `Lemmas`, `MapIdx`, `Perm` -/

-- `Vector.all_congr` (`h`): `p = true`, `q = false`, `xs = ys = #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {xs ys : Vector α n}, xs = ys → ∀ {p q : α → Bool},
    xs.all p = ys.all q := by
  intro H
  have := @H Nat 1 #v[0] #v[0] rfl (fun _ => true) (fun _ => false)
  revert this; decide +kernel

-- `Vector.any_congr` (`h`): `p = true`, `q = false`, `xs = ys = #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {xs ys : Vector α n}, xs = ys → ∀ {p q : α → Bool},
    xs.any p = ys.any q := by
  intro H
  have := @H Nat 1 #v[0] #v[0] rfl (fun _ => true) (fun _ => false)
  revert this; decide +kernel

-- `Vector.vector₂_induction` (`of`): `P := False`, `m = 0`.
example : ¬ ∀ {α : Type} {n m : Nat} (P : Vector (Vector α n) m → Prop)
    (xss : Vector (Vector α n) m), P xss :=
  fun H => @H Nat 0 0 (fun _ => False) #v[]

-- `Vector.vector₃_induction` (`of`): `P := False`, `k = 0`.
example : ¬ ∀ {α : Type} {n m k : Nat} (P : Vector (Vector (Vector α n) m) k → Prop)
    (xss : Vector (Vector (Vector α n) m) k), P xss :=
  fun H => @H Nat 0 0 0 (fun _ => False) #v[]

-- `Vector.mapFinIdx_mk` (`h : xs.size = n`, dependent): `xs = #[]`, `n = 1`.
-- `Vector.pmap_mk` (`h : xs.size = n`, dependent): the same.
example : ¬ ∀ {α : Type} {n : Nat} {xs : Array α}, xs.size = n :=
  fun H => absurd (@H Nat 1 #[]) (by decide)

-- `Vector.exists_of_mem_mapFinIdx` (`h : b ∈ xs.mapFinIdx f`): `n = 0`.
example : ¬ ∀ {β : Type} {α : Type} {n : Nat} {b : β} {xs : Vector α n}
    {f : (i : Nat) → α → i < n → β}, ∃ (i : Nat), ∃ (h : i < n), f i xs[i] h = b := by
  intro H
  obtain ⟨i, h, _⟩ := @H Nat Nat 0 0 #v[] (fun _ _ _ => 0)
  omega

-- `Vector.mapFinIdx_eq_mapIdx` (`h`): `f = 0`, `g = 1`, `xs = #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {β : Type} {xs : Vector α n}
    {f : (i : Nat) → α → i < n → β} {g : Nat → α → β}, xs.mapFinIdx f = Vector.mapIdx g xs := by
  intro H
  have := @H Nat 1 Nat #v[0] (fun _ _ _ => 0) (fun _ _ => 1)
  revert this; decide +kernel

-- `Vector.getElem_mapFinIdx` (`h : i < n`, dependent): `n = i = 0`.
-- `Vector.getElem_pmap` (`hn : i < n`, dependent): the same.
example : ¬ ∀ {n i : Nat}, i < n :=
  fun H => absurd (@H 0 0) (by decide)

-- `Vector.mapFinIdx_congr` (`w : xs = ys`): `f = fun _ a _ => a`, `#v[0]` vs `#v[1]`.
example : ¬ ∀ {α : Type} {n : Nat} {β : Type} {xs ys : Vector α n}
    (f : (i : Nat) → α → i < n → β), xs.mapFinIdx f = ys.mapFinIdx f := by
  intro H
  have := @H Nat 1 Nat #v[0] #v[1] (fun _ a _ => a)
  revert this; decide +kernel

-- `Vector.Perm.extract` (`wlo`): `#v[0, 1] ~ #v[1, 0]`, `lo = 1`, `hi = 2`.
example : ¬ ∀ {α : Type} {n : Nat} {xs ys : Vector α n}, xs.Perm ys → ∀ {lo hi : Nat},
    (∀ (i : Nat), hi ≤ i → xs[i]? = ys[i]?) → (xs.extract lo hi).Perm (ys.extract lo hi) := by
  intro H
  have := @H Nat 2 #v[0, 1] #v[1, 0] (Vector.perm_iff_toList_perm.mpr (List.Perm.swap 1 0 []))
    1 2 (fun i hi => by rw [Vector.getElem?_eq_none hi, Vector.getElem?_eq_none hi])
  have := Vector.perm_iff_toList_perm.mp this
  simp at this

-- `Vector.Perm.extract` (`whi`): `#v[0, 1] ~ #v[1, 0]`, `lo = 0`, `hi = 1`.
example : ¬ ∀ {α : Type} {n : Nat} {xs ys : Vector α n}, xs.Perm ys → ∀ {lo hi : Nat},
    (∀ (i : Nat), i < lo → xs[i]? = ys[i]?) → (xs.extract lo hi).Perm (ys.extract lo hi) := by
  intro H
  have := @H Nat 2 #v[0, 1] #v[1, 0] (Vector.perm_iff_toList_perm.mpr (List.Perm.swap 1 0 []))
    0 1 (fun i hi => by omega)
  have := Vector.perm_iff_toList_perm.mp this
  simp at this

/-! ## Necessary: `Lex` -/

-- `Vector.map_lt_map_iff_of_injective` (`hfinj`): `f = half : NH → Nat`, `#v[0, 0]`, `#v[1, 2]`.
example : ¬ ∀ {α : Type} {β : Type} {n : Nat} [inst : LT α] [inst_1 : LT β] (f : α → β),
    (∀ (a b : α), f a < f b ↔ a < b) →
      ∀ {xs ys : Vector α n}, Vector.map f xs < Vector.map f ys ↔ xs < ys := by
  intro H
  have := @H NH Nat 2 _ _ (fun a => half a) (fun _ _ => Iff.rfl) #v[0, 0] #v[1, 2]
  revert this; decide +kernel

-- `Vector.map_le_map_iff_of_injective` (`hfinj`): `f = half : NH → Nat`, `#v[1, 2]`, `#v[0, 0]`.
example : ¬ ∀ {α : Type} {β : Type} {n : Nat} [inst : LT α] [inst_1 : LT β] (f : α → β),
    (∀ (a b : α), f a < f b ↔ a < b) →
      ∀ {xs ys : Vector α n}, Vector.map f xs ≤ Vector.map f ys ↔ xs ≤ ys := by
  intro H
  have := @H NH Nat 2 _ _ (fun a => half a) (fun _ _ => Iff.rfl) #v[1, 2] #v[0, 0]
  revert this; decide +kernel

-- `Vector.map_lt_map_iff_of_injective` (`hf`): `f = id : Nat → NF`, `#v[0]`, `#v[1]`.
example : ¬ ∀ {α : Type} {β : Type} {n : Nat} [inst : LT α] [inst_1 : LT β] (f : α → β),
    Function.Injective f →
      ∀ {xs ys : Vector α n}, Vector.map f xs < Vector.map f ys ↔ xs < ys := by
  intro H
  have := @H Nat NF 1 _ _ (fun a => (a : NF)) (fun _ _ h => h) #v[0] #v[1]
  revert this; decide +kernel

-- `Vector.map_le_map_iff_of_injective` (`hf`): `f = id : Nat → NF`, `#v[1]`, `#v[0]`.
example : ¬ ∀ {α : Type} {β : Type} {n : Nat} [inst : LT α] [inst_1 : LT β] (f : α → β),
    Function.Injective f →
      ∀ {xs ys : Vector α n}, Vector.map f xs ≤ Vector.map f ys ↔ xs ≤ ys := by
  intro H
  have := @H Nat NF 1 _ _ (fun a => (a : NF)) (fun _ _ h => h) #v[1] #v[0]
  revert this; decide +kernel

/-! ## Necessary: `Algebra` (all with `n = 1`) -/

-- `Vector.add_zero` (`add_zero`): `addS`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Zero α] [inst_1 : Add α] (xs : Vector α n),
    xs + 0 = xs := by
  intro H
  have := @H Nat 1 _ addS #v[0]
  revert this; decide +kernel

-- `Vector.zero_add` (`zero_add`): `addS`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Zero α] [inst_1 : Add α] (xs : Vector α n),
    0 + xs = xs := by
  intro H
  have := @H Nat 1 _ addS #v[0]
  revert this; decide +kernel

-- `Vector.add_comm` (`add_comm`): `addL`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Add α] (xs ys : Vector α n), xs + ys = ys + xs := by
  intro H
  have := @H Nat 1 addL #v[0] #v[1]
  revert this; decide +kernel

-- `Vector.add_assoc` (`add_assoc`): `add2`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Add α] (xs ys zs : Vector α n),
    xs + ys + zs = xs + (ys + zs) := by
  intro H
  have := @H Nat 1 add2 #v[1] #v[0] #v[0]
  revert this; decide +kernel

-- `Vector.neg_zero` (`neg_zero`): `negS`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Zero α] [inst_1 : Neg α], -(0 : Vector α n) = 0 := by
  intro H
  have := @H Nat 1 _ negS
  revert this; decide +kernel

-- `Vector.neg_add_cancel` (`neg_add_cancel`): `negId`, `xs = #v[1]`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Zero α] [inst_1 : Add α] [inst_2 : Neg α]
    (xs : Vector α n), -xs + xs = 0 := by
  intro H
  have := @H Nat 1 _ _ negId #v[1]
  revert this; decide +kernel

-- `Vector.sub_eq_add_neg` (`sub_eq_add_neg`): `negId`, `xs = ys = #v[1]`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Sub α] [inst_1 : Add α] [inst_2 : Neg α]
    (xs ys : Vector α n), xs - ys = xs + -ys := by
  intro H
  have := @H Nat 1 _ _ negId #v[1] #v[1]
  revert this; decide +kernel

-- `Vector.getElem_neg` (`h : i < n`, dependent): `n = i = 0`.
example : ¬ ∀ {n : Nat} (i : Nat), i < n :=
  fun H => absurd (@H 0 0) (by decide)

section
attribute [local instance] Vector.instMul

-- `Vector.mul_zero` (`mul_zero`): `mulA`, `xs = #v[1]`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Zero α] [inst_1 : Mul α] (xs : Vector α n),
    xs * 0 = 0 := by
  intro H
  have := @H Nat 1 _ mulA #v[1]
  revert this; decide +kernel

-- `Vector.zero_mul` (`zero_mul`): `mulA`, `xs = #v[1]`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Zero α] [inst_1 : Mul α] (xs : Vector α n),
    0 * xs = 0 := by
  intro H
  have := @H Nat 1 _ mulA #v[1]
  revert this; decide +kernel

-- `Vector.mul_comm` (`mul_comm`): `mulL`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Mul α] (xs ys : Vector α n), xs * ys = ys * xs := by
  intro H
  have := @H Nat 1 mulL #v[0] #v[1]
  revert this; decide +kernel

-- `Vector.mul_assoc` (`mul_assoc`): `mul2`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Mul α] (xs ys zs : Vector α n),
    xs * ys * zs = xs * (ys * zs) := by
  intro H
  have := @H Nat 1 mul2 #v[1] #v[0] #v[0]
  revert this; decide +kernel

-- `Vector.left_distrib` (`left_distrib`): `mulA`, `xs = #v[1]`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Add α] [inst_1 : Mul α] (xs ys zs : Vector α n),
    xs * (ys + zs) = xs * ys + xs * zs := by
  intro H
  have := @H Nat 1 _ mulA #v[1] #v[0] #v[0]
  revert this; decide +kernel

-- `Vector.right_distrib` (`right_distrib`): `mulA`, `zs = #v[1]`.
example : ¬ ∀ {α : Type} {n : Nat} [inst : Add α] [inst_1 : Mul α] (xs ys zs : Vector α n),
    (xs + ys) * zs = xs * zs + ys * zs := by
  intro H
  have := @H Nat 1 _ mulA #v[0] #v[0] #v[1]
  revert this; decide +kernel

end

-- `Vector.zero_hmul` (`zero_hmul`): `hmulA`, `c = #v[1]`.
example : ¬ ∀ {α : Type} {β : Type} {γ : Type} {n : Nat} [inst : Zero α] [inst_1 : Zero β]
    [inst_2 : Zero γ] [inst_3 : HMul α β γ] (c : Vector β n), (0 : α) * c = 0 := by
  intro H
  have := @H Nat Nat Nat 1 _ _ _ hmulA #v[1]
  revert this; decide +kernel

-- `Vector.hmul_zero` (`hmul_zero`): `hmulA`, `c = 1`.
example : ¬ ∀ {β : Type} {γ : Type} {α : Type} {n : Nat} [inst : Zero β] [inst_1 : Zero γ]
    [inst_2 : HMul α β γ] (c : α), c * (0 : Vector β n) = 0 := by
  intro H
  have := @H Nat Nat Nat 1 _ _ hmulA 1
  revert this; decide +kernel

-- `Vector.hmul_add` (`hmul_add`): `hmulA`, `c = 1`.
example : ¬ ∀ {β : Type} {γ : Type} {α : Type} {n : Nat} [inst : Add β] [inst_1 : Add γ]
    [inst_2 : HMul α β γ] (c : α) (xs ys : Vector β n), c * (xs + ys) = c * xs + c * ys := by
  intro H
  have := @H Nat Nat Nat 1 _ _ hmulA 1 #v[0] #v[0]
  revert this; decide +kernel

-- `Vector.add_hmul` (`add_hmul`): `hmulA`, `xs = #v[1]`.
example : ¬ ∀ {α : Type} {β : Type} {γ : Type} {n : Nat} [inst : Add α] [inst_1 : Add β]
    [inst_2 : Add γ] [inst_3 : HMul α β γ] (c d : α) (xs : Vector β n),
    (c + d) * xs = c * xs + d * xs := by
  intro H
  have := @H Nat Nat Nat 1 _ _ _ hmulA 0 0 #v[1]
  revert this; decide +kernel

-- `Vector.zero_smul` (`zero_smul`): `smulA`, `c = #v[1]`.
example : ¬ ∀ {α : Type} {β : Type} {n : Nat} [inst : Zero α] [inst_1 : Zero β]
    [inst_2 : SMul α β] (c : Vector β n), (0 : α) • c = 0 := by
  intro H
  have := @H Nat Nat 1 _ _ smulA #v[1]
  revert this; decide +kernel

-- `Vector.smul_zero` (`smul_zero`): `smulA`, `c = 1`.
example : ¬ ∀ {β : Type} {α : Type} {n : Nat} [inst : Zero β] [inst_1 : SMul α β] (c : α),
    c • (0 : Vector β n) = 0 := by
  intro H
  have := @H Nat Nat 1 _ smulA 1
  revert this; decide +kernel

-- `Vector.smul_add` (`smul_add`): `smulA`, `c = 1`.
example : ¬ ∀ {β : Type} {α : Type} {n : Nat} [inst : Add β] [inst_1 : SMul α β] (c : α)
    (xs ys : Vector β n), c • (xs + ys) = c • xs + c • ys := by
  intro H
  have := @H Nat Nat 1 _ smulA 1 #v[0] #v[0]
  revert this; decide +kernel

-- `Vector.add_smul` (`add_smul`): `smulA`, `xs = #v[1]`.
example : ¬ ∀ {α : Type} {β : Type} {n : Nat} [inst : Add α] [inst_1 : Add β]
    [inst_2 : SMul α β] (c d : α) (xs : Vector β n), (c + d) • xs = c • xs + d • xs := by
  intro H
  have := @H Nat Nat 1 _ _ smulA 0 0 #v[1]
  revert this; decide +kernel

-- `Vector.mul_smul` (`mul_smul`): `smulA`, `c = d = 1`.
example : ¬ ∀ {α : Type} {β : Type} {n : Nat} {d : α} [inst : Mul α] [inst_1 : SMul α β]
    (c : α) (xs : Vector β n), (c * d) • xs = c • d • xs := by
  intro H
  have := @H Nat Nat 1 1 _ smulA 1 #v[0]
  revert this; decide +kernel

/-! ## Necessary: `Attach` (dependent side conditions unless noted) -/

-- `Vector.pmap_congr_left` (`h`, not dependent): `f = 0`, `g = 1`, `p = q = True`, `xs = #v[0]`.
example : ¬ ∀ {α : Type} {β : Type} {n : Nat} {p q : α → Prop} {f : (a : α) → p a → β}
    {g : (a : α) → q a → β} (xs : Vector α n) {H₁ : ∀ (a : α), a ∈ xs → p a}
    {H₂ : ∀ (a : α), a ∈ xs → q a}, Vector.pmap f xs H₁ = Vector.pmap g xs H₂ := by
  intro H
  have := @H Nat Nat 1 (fun _ => True) (fun _ => True) (fun _ _ => 0) (fun _ _ => 1) #v[0]
    (fun _ _ => trivial) (fun _ _ => trivial)
  revert this; decide +kernel

-- `Vector.getElem_pmap` (`h`): `p := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Vector α n}, ∀ a, a ∈ xs → p a :=
  fun H => H (p := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.getElem?_pmap` (`h`): `p := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Vector α n}, ∀ a, a ∈ xs → p a :=
  fun H => H (p := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.mem_pmap` (`H`): `p := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Vector α n}, ∀ a, a ∈ xs → p a :=
  fun H => H (p := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.mem_pmap_of_mem` (`H`): `p := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Vector α n}, ∀ a, a ∈ xs → p a :=
  fun H => H (p := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.mem_pmap_of_mem` (`h : a ∈ xs`): `xs = #v[]`.
example : ¬ ∀ {α : Type} {n : Nat} {xs : Vector α n} {a : α}, a ∈ xs :=
  fun H => absurd (@H Nat 0 #v[] 0) (by simp)

-- `Vector.map_pmap` (`H`): `p := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Vector α n}, ∀ a, a ∈ xs → p a :=
  fun H => H (p := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.pmap_eq_map_attach` (`H`): `p := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Vector α n}, ∀ a, a ∈ xs → p a :=
  fun H => H (p := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.pmap_append'` (`h₁`): `p := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Vector α n}, ∀ a, a ∈ xs → p a :=
  fun H => H (p := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.pmap_append'` (`h₂`): `p := False`, `ys := #v[0]`.
example : ¬ ∀ {α : Type} {m : Nat} {p : α → Prop} {ys : Vector α m}, ∀ a, a ∈ ys → p a :=
  fun H => H (p := fun _ => False) (ys := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.pmap_congr_left` (`H₁`): `p := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Vector α n}, ∀ a, a ∈ xs → p a :=
  fun H => H (p := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.pmap_congr_left` (`H₂`): `q := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {q : α → Prop} {xs : Vector α n}, ∀ a, a ∈ xs → q a :=
  fun H => H (q := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.pmap_pmap` (`H₁`): `p := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Vector α n}, ∀ a, a ∈ xs → p a :=
  fun H => H (p := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.countP_pmap` (`H₁`): `p := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Vector α n}, ∀ a, a ∈ xs → p a :=
  fun H => H (p := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.reverse_pmap` (`H`): `P := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {P : α → Prop} {xs : Vector α n}, ∀ a, a ∈ xs → P a :=
  fun H => H (P := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.back?_pmap` (`H`): `P := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {P : α → Prop} {xs : Vector α n}, ∀ a, a ∈ xs → P a :=
  fun H => H (P := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.find?_pmap` (`H`): `P := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {P : α → Prop} {xs : Vector α n}, ∀ a, a ∈ xs → P a :=
  fun H => H (P := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.pmap_attachWith` (`H₁`): `q := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {q : α → Prop} {xs : Vector α n}, ∀ a, a ∈ xs → q a :=
  fun H => H (q := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.pmap_eq_self` (`hp`): `p := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {xs : Vector α n} {p : α → Prop}, ∀ a, a ∈ xs → p a :=
  fun H => H (p := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.foldl_pmap` (`H`): `P := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {xs : Vector α n} {P : α → Prop}, ∀ a, a ∈ xs → P a :=
  fun H => H (P := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.foldr_pmap` (`H`): `P := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {xs : Vector α n} {P : α → Prop}, ∀ a, a ∈ xs → P a :=
  fun H => H (P := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.toList_pmap` (`H`): `P := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {xs : Vector α n} {P : α → Prop}, ∀ a, a ∈ xs → P a :=
  fun H => H (P := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.toArray_pmap` (`H`): `P := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {xs : Vector α n} {P : α → Prop}, ∀ a, a ∈ xs → P a :=
  fun H => H (P := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.pmap_append` (`h`): `p := False`, `xs := #v[0]`, `ys := #v[]`.
example : ¬ ∀ {ι : Type} {n m : Nat} {p : ι → Prop} {xs : Vector ι n} {ys : Vector ι m},
    ∀ a, a ∈ xs ++ ys → p a :=
  fun H => H (p := fun _ => False) (xs := #v[(0 : Nat)]) (ys := #v[]) 0 (by simp)

-- `Vector.pmap_reverse` (`H`): `P := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {P : α → Prop} {xs : Vector α n},
    ∀ a, a ∈ xs.reverse → P a :=
  fun H => H (P := fun _ => False) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.pmap_map` (`H`): `p := False`, `f := id`, `xs := #v[0]`.
example : ¬ ∀ {β : Type} {α : Type} {n : Nat} {p : β → Prop} {f : α → β} {xs : Vector α n},
    ∀ a, a ∈ Vector.map f xs → p a :=
  fun H => H (p := fun _ => False) (f := fun (a : Nat) => a) (xs := #v[(0 : Nat)]) 0 (by simp)

-- `Vector.pmap_push` (`h`): `P := False`, `a := 0`, `xs := #v[]`.
example : ¬ ∀ {α : Type} {n : Nat} {P : α → Prop} {a : α} {xs : Vector α n},
    ∀ b, b ∈ xs.push a → P b :=
  fun H => H (P := fun _ => False) (a := (0 : Nat)) (xs := #v[]) 0 (by simp)

-- `Vector.pmap_attach` (`H`): `p := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {xs : Vector α n} {p : { x : α // x ∈ xs } → Prop},
    ∀ a, a ∈ xs.attach → p a :=
  fun H => H (xs := #v[(0 : Nat)]) (p := fun _ => False) ⟨0, by simp⟩ (by simp)

-- `Vector.pmap_attachWith` (`H₂`): `q := True`, `p := False`, `xs := #v[0]`.
example : ¬ ∀ {α : Type} {n : Nat} {q : α → Prop} {xs : Vector α n}
    {p : { x : α // q x } → Prop} (H₁ : ∀ (x : α), x ∈ xs → q x),
    ∀ a, a ∈ xs.attachWith q H₁ → p a :=
  fun H => H (q := fun _ => True) (xs := #v[(0 : Nat)]) (p := fun _ => False)
    (fun _ _ => trivial) ⟨0, trivial⟩ (by simp)

-- `Vector.pmap_pmap` (`H₂`): `p := True`, `q := False`, `g := fun a _ => a`, `xs := #v[0]`.
example : ¬ ∀ {α β : Type} {n : Nat} {p : α → Prop} {q : β → Prop} {g : (a : α) → p a → β}
    {xs : Vector α n} (H₁ : ∀ (a : α), a ∈ xs → p a), ∀ a, a ∈ Vector.pmap g xs H₁ → q a :=
  fun H => H (p := fun _ => True) (q := fun _ => False) (g := fun (a : Nat) _ => a)
    (xs := #v[(0 : Nat)]) (fun _ _ => trivial) 0 (by simp)

-- `Vector.pmap_mk` (`H`): `xs := #[0]`, `P := False`.
example : ¬ ∀ {α : Type} {n : Nat} {xs : Array α} {h : xs.size = n} {P : α → Prop},
    ∀ a, a ∈ Vector.mk xs h → P a :=
  fun H => H (xs := #[(0 : Nat)]) (h := rfl) (P := fun _ => False) 0 (by simp)
