/-!
Hand resolution of the remaining unresolved hypotheses in `Init.Data.Array.*` (cluster `Array`,
`runs/hand5/todo_Array.jsonl`, 113 hypotheses). For each hypothesis `hᵢ` of theorem `T`, this file
proves `T'` (removable), `¬T'` (necessary), or, for a dependent hypothesis, `∀ indep, Hᵢ` resp.
`¬∀ indep, Hᵢ`. Universe-polymorphic theorems are refuted at `Type`.

Removable (19):
* `[LawfulMonad m]` in `foldrM_map`, `foldrM_subtype`, `foldrM_attachWith`, `foldrM_unattach`,
  `flatMapM_subtype`, `flatMapM_unattach`, `filterMapM_subtype`, `filterMapM_unattach`, `mapM_map`,
  `mapM_subtype`, `mapM_unattach` and `zipWithM_eq_mapM_id_zipWith`: the two sides run the same loop
  over arrays of the same size whose elements correspond (`unattach` and `attachWith` are `map`s), so
  they perform the same binds in any monad. Helpers: `foldlM_map_gen`/`foldrM_map_gen` (via
  `foldlM_start_stop`/`foldrM_start_stop`, `map_extract` and the `Monad`-only `List` folds),
  `mapM_map_loop`, `zip_loop` (induction over the well-founded loops).
* `w : start/stop = xs.size` in `foldrM_map`, `foldlM_map`, `foldlM_subtype`, `foldrM_subtype`: the
  same helpers hold for every `start`/`stop`.
* `w` in `filter_replicate_of_neg`: every element fails `p`, so the result is empty for every `stop`.
* `h : start + size ≤ xs.size` in `extract_loop_eq`: both sides copy `min size (xs.size - start)`
  elements (`extract_loop_min`).
* `h` in `getElem_extract_loop_lt` (dependent, derivable): it is the default value
  `getElem_extract_loop_lt_aux hlt`.

Necessary (93, 36 of them dependent): models below.
* `NatM α := Nat` with `natMonad` (`pure = 0`, `bind x _ = x + 1`, `map _ x = x + 10`): counts outer
  binds, violates every monad law; refutes `[LawfulMonad m]` in `foldlM_push`, `foldlM_push'`,
  `forIn'_pure_yield_eq_foldl`, `mapM_eq_foldlM_push`, `mapM_eq_foldlM`, `forIn'_eq_foldlM`,
  `List.mapFinIdxM_toArray`, `toList_mapFinIdxM`.
* `tyMonad` on `NatM`: like `natMonad`, but `map` adds `1` iff the result type is a subsingleton
  (classical, not parametric). It satisfies `bind (f <$> x) k = bind x (k ∘ f)` up to this type
  test, so it separates the `ForInStep β`-valued `<$>` of a `forIn'` body from the `β`-valued one of
  the fold: `forIn'_yield_eq_foldlM`, `forIn_yield_eq_foldlM` (`β := Unit`).
* `pmap`/`attach` side conditions (dependent): `∀ a ∈ xs, p a` fails for `p := False`, `xs := #[0]`.
* Orders: `NE` (`Nat` with the empty `<`), `U1` (one element, empty `<`, trichotomous), `Fin 2` with
  `f 0 = #[0]`, `f 1 = #[0, 0]` (strictly monotone, not prefix-free); `rps` (rock-paper-scissors on
  `Fin 3`: total, not transitive), `le01` (`a = b ∨ (a, b) = (0, 1)` on `Fin 3`: transitive, not
  total), constant `false`; `mergeSort` is evaluated with `ms2`/`ms3` and `simp`.
* The rest are small `Nat` arrays evaluated with `decide +kernel`.

Left unresolved (1): `[LawfulMonad m]` in `Array.toList_ofFnM`: both sides are the same `Fin.foldlM`
loop with `<$>` steps (`push` vs. `cons` + `reverse`), differing only between the isomorphic result
types `Array α` and `List α`. A monad whose `map` tests `β = List Nat` (classically) would refute it,
but `Array Nat ≠ List Nat` is not provable, so this looks independent of the axioms.

Run with the lean4 repo's stage1 binary: `lean checks/RestArrayHand.lean`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option warn.classDefReducibility false

universe u v w x

namespace RestArrayHand
open Array

/-! # Helpers for the removable verdicts -/

theorem foldlM_map_gen {m : Type u → Type v} [Monad m] {f : β₁ → β₂} {g : α → β₂ → m α} {xs : Array β₁}
    {init : α} {start stop : Nat} :
    (xs.map f).foldlM g init start stop = xs.foldlM (fun x y => g x (f y)) init start stop := by
  rw [foldlM_start_stop, foldlM_start_stop (xs := xs), ← map_extract]
  rw [size_map]
  exact foldlM_map (m := m) (w := rfl)

theorem foldrM_map_gen {m : Type u → Type v} [Monad m] {f : β₁ → β₂} {g : β₂ → α → m α} {xs : Array β₁}
    {init : α} {start stop : Nat} :
    (xs.map f).foldrM g init start stop = xs.foldrM (fun x y => g (f x) y) init start stop := by
  rw [foldrM_start_stop, foldrM_start_stop (xs := xs), ← map_extract]
  rw [foldrM_eq_reverse_foldlM_toList, foldrM_eq_reverse_foldlM_toList, toList_map, ← List.map_reverse,
    List.foldlM_map]

theorem mapM_map_loop {m : Type u → Type v} [Monad m] {f : α → β} {g : β → m γ} (xs : Array α) :
    ∀ (n i : Nat) (bs : Array γ), xs.size - i = n →
      mapM.map g (xs.map f) i bs = mapM.map (g ∘ f) xs i bs := by
  intro n
  induction n with
  | zero =>
    intro i bs h
    rw [mapM.map, mapM.map]
    simp only [size_map]
    rw [dif_neg (by omega), dif_neg (by omega)]
  | succ n ih =>
    intro i bs h
    rw [mapM.map, mapM.map]
    simp only [size_map]
    rw [dif_pos (by omega), dif_pos (by omega)]
    simp only [getElem_map, Function.comp]
    congr 1; funext b
    exact ih _ _ (by omega)

theorem mapM_map_gen {m : Type u → Type v} [Monad m] {f : α → β} {g : β → m γ} {xs : Array α} :
    (xs.map f).mapM g = xs.mapM (g ∘ f) := by
  unfold mapM
  simp only [size_map]
  exact mapM_map_loop xs _ 0 _ rfl

theorem zip_loop {m : Type u → Type v} [Monad m] {f : α → β → m γ} (as : Array α) (bs : Array β) :
    ∀ (n i : Nat) (cs : Array γ), min as.size bs.size - i = n →
      zipWithMAux as bs f i cs = mapM.map id (zipWith f as bs) i cs := by
  intro n
  induction n with
  | zero =>
    intro i cs h
    rw [zipWithMAux, mapM.map]
    simp only [size_zipWith]
    have hn : ¬ i < min as.size bs.size := by omega
    rw [dif_neg hn]
    by_cases h1 : i < as.size
    · have h2 : ¬ i < bs.size := by omega
      rw [dif_pos h1, dif_neg h2]
    · rw [dif_neg h1]
  | succ n ih =>
    intro i cs h
    rw [zipWithMAux, mapM.map]
    simp only [size_zipWith]
    have h1 : i < as.size := by omega
    have h2 : i < bs.size := by omega
    have h3 : i < min as.size bs.size := by omega
    rw [dif_pos h1, dif_pos h3, dif_pos h2]
    simp only [getElem_zipWith, id]
    congr 1; funext c
    exact ih _ _ (by omega)

theorem filter_start_zero {α : Type u} (p : α → Bool) (xs : Array α) (stop : Nat) :
    xs.filter p 0 stop = (xs.extract 0 stop).filter p := by
  simp only [filter, foldl_eq_foldlM]
  rw [foldlM_start_stop]

theorem extract_loop_min {α : Type u} (xs : Array α) : ∀ (size start : Nat) (ys : Array α),
    extract.loop xs size start ys = extract.loop xs (min size (xs.size - start)) start ys := by
  intro size
  induction size with
  | zero => intro start ys; simp
  | succ size ih =>
    intro start ys
    by_cases h : start < xs.size
    · have e : min (size + 1) (xs.size - start) = min size (xs.size - (start + 1)) + 1 := by omega
      rw [e, extract_loop_succ h, extract_loop_succ h, ih]
    · rw [extract_loop_of_ge (by omega), show xs.size - start = 0 by omega, Nat.min_zero, extract_loop_zero]

/-! # Removable -/

-- `Array.foldrM_map` (`[LawfulMonad m]`): mapping the array and composing the step function give the
-- same loop for every monad (`foldrM_start_stop`, then the `List` fold).
theorem foldrM_map_inst {m : Type u → Type v} {β₁ : Type w} {β₂ : Type x} {α : Type u} {start : Nat}
    [Monad m] {f : β₁ → β₂} {g : β₂ → α → m α} {xs : Array β₁} {init : α} {w : start = xs.size} :
    (xs.map f).foldrM g init start 0 = xs.foldrM (fun x y => g (f x) y) init start 0 :=
  foldrM_map_gen

-- `Array.foldrM_map` (`w`): holds for every `start` (`foldrM_start_stop` and `map_extract`).
theorem foldrM_map_w {m : Type u → Type v} {β₁ : Type w} {β₂ : Type x} {α : Type u} {start : Nat}
    [Monad m] [LawfulMonad m] {f : β₁ → β₂} {g : β₂ → α → m α} {xs : Array β₁} {init : α} :
    (xs.map f).foldrM g init start 0 = xs.foldrM (fun x y => g (f x) y) init start 0 :=
  foldrM_map_gen

-- `Array.foldlM_map` (`w`): holds for every `stop` (`foldlM_start_stop` and `map_extract`).
theorem foldlM_map_w {m : Type u → Type v} {β₁ : Type w} {β₂ : Type x} {α : Type u} {stop : Nat}
    [Monad m] {f : β₁ → β₂} {g : α → β₂ → m α} {xs : Array β₁} {init : α} :
    (xs.map f).foldlM g init 0 stop = xs.foldlM (fun x y => g x (f y)) init 0 stop :=
  foldlM_map_gen

-- `Array.foldlM_subtype` (`w`): `unattach` is `map (·.val)`, so this is `foldlM_map` for every `stop`.
theorem foldlM_subtype_w {m : Type u → Type v} {α : Type w} {β : Type u} {stop : Nat} [Monad m]
    {p : α → Prop} {xs : Array { x // p x }} {f : β → { x // p x } → m β} {g : β → α → m β} {x : β}
    (hf : ∀ b x h, f b ⟨x, h⟩ = g b x) :
    xs.foldlM f x 0 stop = xs.unattach.foldlM g x 0 stop := by
  have e : f = fun b y => g b y.1 := by funext b y; exact hf b y.1 y.2
  subst e
  rw [unattach, foldlM_map_gen]

-- `Array.foldrM_subtype` (`[LawfulMonad m]`): `unattach` is `map (·.val)`; `foldrM` over a `map` needs
-- no monad laws.
theorem foldrM_subtype_inst {m : Type u → Type v} {α : Type w} {β : Type u} {start : Nat} [Monad m]
    {p : α → Prop} {xs : Array { x // p x }} {f : { x // p x } → β → m β} {g : α → β → m β} {x : β}
    (hf : ∀ x h b, f ⟨x, h⟩ b = g x b) (w : start = xs.size) :
    xs.foldrM f x start 0 = xs.unattach.foldrM g x start 0 := by
  have e : f = fun y b => g y.1 b := by funext y b; exact hf y.1 y.2 b
  subst e
  rw [unattach, foldrM_map_gen]

-- `Array.foldrM_subtype` (`w`): as above, for every `start`.
theorem foldrM_subtype_w {m : Type u → Type v} {α : Type w} {β : Type u} {start : Nat} [Monad m]
    [LawfulMonad m] {p : α → Prop} {xs : Array { x // p x }} {f : { x // p x } → β → m β}
    {g : α → β → m β} {x : β} (hf : ∀ x h b, f ⟨x, h⟩ b = g x b) :
    xs.foldrM f x start 0 = xs.unattach.foldrM g x start 0 := by
  have e : f = fun y b => g y.1 b := by funext y b; exact hf y.1 y.2 b
  subst e
  rw [unattach, foldrM_map_gen]

-- `Array.foldrM_attachWith` (`[LawfulMonad m]`): `attachWith` is a `map` of `attach`.
theorem foldrM_attachWith_inst {m : Type u → Type v} {α : Type w} {β : Type u} {start : Nat} [Monad m]
    {xs : Array α} {q : α → Prop} (H : ∀ a, a ∈ xs → q a) {f : { x // q x } → β → m β} {b : β}
    {w : start = xs.size} :
    (xs.attachWith q H).foldrM f b start 0 =
      xs.attach.foldrM (fun a acc => f ⟨a.1, H _ a.2⟩ acc) b := by
  subst w
  rw [attachWith_eq_map_attach, foldrM_map_gen, size_attach]

-- `Array.foldrM_unattach` (`[LawfulMonad m]`): `unattach` is `map (·.val)`; `foldrM` over a `map`
-- needs no monad laws.
theorem foldrM_unattach_inst {m : Type u → Type v} {α : Type w} {β : Type u} [Monad m]
    {P : α → Prop} {xs : Array (Subtype P)} {f : α → β → m β} {init : β} :
    xs.unattach.foldrM f init = xs.foldrM (init := init) fun ⟨x, h⟩ b =>
      binderNameHint x f <| binderNameHint h () <| binderNameHint b (f x) <|
      f (wfParam x) b := by
  simp only [unattach, foldrM_map_gen, size_map]
  rfl

-- `Array.flatMapM_subtype` (`[LawfulMonad m]`): `flatMapM` is a `foldlM`, and `unattach` a `map`.
theorem flatMapM_subtype_inst {m : Type u → Type v} {α : Type w} {β : Type u} [Monad m]
    {p : α → Prop} {xs : Array { x // p x }} {f : { x // p x } → m (Array β)} {g : α → m (Array β)}
    (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    xs.flatMapM f = xs.unattach.flatMapM g := by
  have e : f = fun y => g y.1 := by funext y; exact hf y.1 y.2
  subst e
  simp only [flatMapM, unattach, foldlM_map_gen, size_map]

-- `Array.flatMapM_unattach` (`[LawfulMonad m]`): as for `flatMapM_subtype`.
theorem flatMapM_unattach_inst {m : Type u → Type v} {α : Type w} {β : Type u} [Monad m]
    {P : α → Prop} {xs : Array (Subtype P)} {f : α → m (Array β)} :
    xs.unattach.flatMapM f = xs.flatMapM fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp only [flatMapM, unattach, foldlM_map_gen, size_map]
  rfl

-- `Array.filterMapM_subtype` (`[LawfulMonad m]`): `filterMapM` is a `foldlM`, and `unattach` a `map`.
theorem filterMapM_subtype_inst {m : Type u → Type v} {α : Type w} {β : Type u} {stop : Nat} [Monad m]
    {p : α → Prop} {xs : Array { x // p x }} {f : { x // p x } → m (Option β)} {g : α → m (Option β)}
    (hf : ∀ x h, f ⟨x, h⟩ = g x) (w : stop = xs.size) :
    xs.filterMapM f 0 stop = xs.unattach.filterMapM g := by
  have e : f = fun y => g y.1 := by funext y; exact hf y.1 y.2
  subst e w
  simp only [filterMapM, unattach, foldlM_map_gen, size_map]

-- `Array.filterMapM_unattach` (`[LawfulMonad m]`): as for `filterMapM_subtype`.
theorem filterMapM_unattach_inst {m : Type u → Type v} {α : Type w} {β : Type u} [Monad m]
    {P : α → Prop} {xs : Array (Subtype P)} {f : α → m (Option β)} :
    xs.unattach.filterMapM f = xs.filterMapM fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  simp only [filterMapM, unattach, foldlM_map_gen, size_map]
  rfl

-- `Array.mapM_map` (`[LawfulMonad m]`): the `mapM` loops agree step by step for every monad.
theorem mapM_map_inst {m : Type u → Type v} {α : Type w} {β : Type x} {γ : Type u} [Monad m]
    {f : α → β} {g : β → m γ} {xs : Array α} :
    (xs.map f).mapM g = xs.mapM (g ∘ f) :=
  mapM_map_gen

-- `Array.mapM_subtype` (`[LawfulMonad m]`): `unattach` is a `map`, then as for `mapM_map`.
theorem mapM_subtype_inst {m : Type u → Type v} {α : Type w} {β : Type u} [Monad m]
    {p : α → Prop} {xs : Array { x // p x }} {f : { x // p x } → m β} {g : α → m β}
    (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    xs.mapM f = xs.unattach.mapM g := by
  have e : f = fun y => g y.1 := by funext y; exact hf y.1 y.2
  subst e
  rw [unattach, mapM_map_gen]
  rfl

-- `Array.mapM_unattach` (`[LawfulMonad m]`): as for `mapM_subtype`.
theorem mapM_unattach_inst {m : Type u → Type v} {α : Type w} {β : Type u} [Monad m]
    {P : α → Prop} {xs : Array (Subtype P)} {f : α → m β} :
    xs.unattach.mapM f = xs.mapM fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x) := by
  rw [unattach, mapM_map_gen]
  rfl

-- `Array.zipWithM_eq_mapM_id_zipWith` (`[LawfulMonad m]`): `zipWithMAux` and the `mapM` loop over
-- `zipWith f as bs` perform the same binds for every monad.
theorem zipWithM_eq_mapM_id_zipWith_inst {α : Type w} {β : Type x} {γ : Type u} {m : Type u → Type v}
    [Monad m] {f : α → β → m γ} {as : Array α} {bs : Array β} :
    zipWithM f as bs = mapM id (zipWith f as bs) := by
  unfold zipWithM mapM
  exact zip_loop as bs _ 0 #[] rfl

-- `Array.filter_replicate_of_neg` (`w`): every element is `a` and fails `p`, so the result is empty
-- for every `stop`.
theorem filter_replicate_of_neg_w {stop n : Nat} {α : Type u} {p : α → Bool} {a : α} (h : ¬ p a) :
    (replicate n a).filter p 0 stop = #[] := by
  rw [filter_start_zero, extract_replicate]
  exact filter_replicate_of_neg size_replicate h

-- `Array.extract_loop_eq` (`h`): both sides copy `min size (xs.size - start)` elements from `start`.
theorem extract_loop_eq_h {α : Type u} {xs ys : Array α} {size start : Nat} :
    extract.loop xs size start ys = ys ++ xs.extract start (start + size) := by
  rw [extract_loop_eq_aux]
  simp only [extract, Nat.sub_eq, emptyWithCapacity_eq]
  rw [extract_loop_min xs size, extract_loop_min xs (min (start + size) xs.size - start)]
  congr 2
  omega

-- `Array.getElem_extract_loop_lt` (`h`, dependent): it is the default value
-- `getElem_extract_loop_lt_aux hlt`, so it follows from `hlt`.
theorem getElem_extract_loop_lt_h {α : Type u} {i : Nat} {xs ys : Array α} {size start : Nat}
    (hlt : i < ys.size) : i < (extract.loop xs size start ys).size :=
  getElem_extract_loop_lt_aux hlt

/-! # Necessary -/

/-! ## `[LawfulMonad m]`: non-lawful monads on `NatM` -/

def NatM (_ : Type) : Type := Nat

instance (α : Type) : DecidableEq (NatM α) := inferInstanceAs (DecidableEq Nat)

instance natMonad : Monad NatM where
  pure _ := (0 : Nat)
  bind x _ := (show Nat from x) + 1
  map _ x := (show Nat from x) + 10

open Classical in
/-- `1` if `β` is a subsingleton, else `0` (classical). -/
noncomputable def ssInd (β : Type) : Nat := if Subsingleton β then 1 else 0

theorem ssInd_unit : ssInd Unit = 1 := by
  unfold ssInd; exact if_pos ⟨fun _ _ => rfl⟩

theorem ssInd_forInStep : ssInd (ForInStep Unit) = 0 := by
  unfold ssInd
  exact if_neg fun h => by cases h.allEq (.done ()) (.yield ())

/-- Like `natMonad`, but `map` adds `1` when the result type is a subsingleton: not parametric, so
`map` with `ForInStep β` and with `β` results differ. -/
noncomputable instance tyMonad : Monad NatM where
  pure _ := (0 : Nat)
  bind x _ := (show Nat from x) + 1
  map {_ β} _ x := (show Nat from x) + ssInd β

-- `Array.foldlM_push'` (`[LawfulMonad m]`): `NatM`, `xs := #[0]`, `f := pure`: the left side has
-- one outer bind (1), the right side `foldlM … >>= _` two (2).
theorem neg1 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [inst : Monad m]
    {xs : Array α} {a : α} {f : β → α → m β} {b : β} {stop : Nat},
    stop = xs.size + 1 → (xs.push a).foldlM f b 0 stop = (xs.foldlM f b >>= fun b => f b a) := by
  intro H
  have h := @H NatM Nat Nat natMonad #[0] 0 (fun _ _ => (0 : Nat)) 0 2 rfl
  revert h; decide +kernel

-- `Array.foldlM_push` (`[LawfulMonad m]`): as for `foldlM_push'`.
theorem neg2 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [inst : Monad m]
    {xs : Array α} {a : α} {f : β → α → m β} {b : β},
    (xs.push a).foldlM f b = (xs.foldlM f b >>= fun b => f b a) := by
  intro H
  have h := @H NatM Nat Nat natMonad #[0] 0 (fun _ _ => (0 : Nat)) 0
  revert h; decide +kernel

-- `Array.forIn'_pure_yield_eq_foldl` (`[LawfulMonad m]`): `NatM`, `xs := #[0]`: the loop binds once
-- (1), the right side is `pure` (0).
theorem neg3 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [inst : Monad m]
    {xs : Array α} (f : (a : α) → a ∈ xs → β → β) (init : β),
    forIn' xs init (fun a m b => pure (.yield (f a m b))) =
      pure (f := m) (xs.attach.foldl (fun b ⟨a, h⟩ => f a h b) init) := by
  intro H
  have h := @H NatM Nat Nat natMonad #[0] (fun _ _ b => b) 0
  revert h; decide +kernel

-- `Array.mapM_eq_foldlM_push` (`[LawfulMonad m]`): `NatM`, `xs := #[0]`: `mapM` binds once (1), the
-- fold binds around the `do` block (2).
theorem neg4 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [inst : Monad m]
    {f : α → m β} {xs : Array α},
    mapM f xs = xs.foldlM (fun acc a => return (acc.push (← f a))) #[] := by
  intro H
  have h := @H NatM Nat Nat natMonad (fun _ => (0 : Nat)) #[0]
  revert h; decide +kernel

-- `Array.mapM_eq_foldlM` (`[LawfulMonad m]`): `NatM`, `xs := #[0]`: `mapM` binds once (1), the fold
-- binds a `<$>` (10 + 1).
theorem neg5 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [inst : Monad m]
    {f : α → m β} {xs : Array α},
    xs.mapM f = xs.foldlM (fun bs a => bs.push <$> f a) #[] := by
  intro H
  have h := @H NatM Nat Nat natMonad (fun _ => (0 : Nat)) #[0]
  revert h; decide +kernel

-- `Array.forIn'_eq_foldlM` (`[LawfulMonad m]`): `NatM`, `xs := #[]`: `pure` (0) vs. `value <$> pure _`
-- (10).
theorem neg6 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [inst : Monad m]
    {xs : Array α} (f : (a : α) → a ∈ xs → β → m (ForInStep β)) (init : β),
    forIn' xs init f = ForInStep.value <$>
      xs.attach.foldlM (fun b ⟨a, m⟩ => match b with
        | .yield b => f a m b
        | .done b => pure (.done b)) (ForInStep.yield init) := by
  intro H
  have h := @H NatM Nat Nat natMonad #[] (fun _ _ _ => (0 : Nat)) 0
  revert h; decide +kernel

-- `List.mapFinIdxM_toArray` (`[LawfulMonad m]`): `NatM`, `l := []`: `pure` (0) vs. `toArray <$> pure _`
-- (10).
theorem neg7 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [inst : Monad m]
    {l : List α} {f : (i : Nat) → α → i < l.length → m β},
    l.toArray.mapFinIdxM f = List.toArray <$> l.mapFinIdxM f := by
  intro H
  have h := @H NatM Nat Nat natMonad [] (fun _ _ _ => (0 : Nat))
  revert h; decide +kernel

-- `Array.toList_mapFinIdxM` (`[LawfulMonad m]`): `NatM`, `xs := #[]`: `toList <$> pure _` (10) vs.
-- `pure` (0).
theorem neg8 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [inst : Monad m]
    {xs : Array α} {f : (i : Nat) → α → i < xs.size → m β},
    toList <$> xs.mapFinIdxM f = xs.toList.mapFinIdxM f := by
  intro H
  have h := @H NatM Nat Nat natMonad #[] (fun _ _ _ => (0 : Nat))
  revert h; decide +kernel

-- `Array.forIn'_yield_eq_foldlM` (`[LawfulMonad m]`): `tyMonad`, `β := γ := Unit`, `xs := #[0]`: the
-- loop maps into `ForInStep Unit` (not a subsingleton, 0 + 1), the fold into `Unit` (1 + 1).
theorem neg9 : ¬ ∀ {m : Type → Type} {α : Type} {β γ : Type} [inst : Monad m]
    {xs : Array α} (f : (a : α) → a ∈ xs → β → m γ) (g : (a : α) → a ∈ xs → β → γ → β) (init : β),
    forIn' xs init (fun a m b => (fun c => .yield (g a m b c)) <$> f a m b) =
      xs.attach.foldlM (fun b ⟨a, m⟩ => g a m b <$> f a m b) init := by
  intro H
  have h := @H NatM Nat Unit Unit tyMonad #[0] (fun _ _ _ => (0 : Nat)) (fun _ _ _ _ => ()) ()
  change (0 + ssInd (ForInStep Unit)) + 1 = (0 + ssInd Unit) + 1 at h
  rw [ssInd_forInStep, ssInd_unit] at h
  exact absurd h (by decide)

-- `Array.forIn_yield_eq_foldlM` (`[LawfulMonad m]`): as for `forIn'_yield_eq_foldlM`.
theorem neg10 : ¬ ∀ {m : Type → Type} {α : Type} {β γ : Type} [inst : Monad m]
    {xs : Array α} (f : α → β → m γ) (g : α → β → γ → β) (init : β),
    forIn xs init (fun a b => (fun c => .yield (g a b c)) <$> f a b) =
      xs.foldlM (fun b a => g a b <$> f a b) init := by
  intro H
  have h := @H NatM Nat Unit Unit tyMonad #[0] (fun _ _ => (0 : Nat)) (fun _ _ _ => ()) ()
  change (0 + ssInd (ForInStep Unit)) + 1 = (0 + ssInd Unit) + 1 at h
  rw [ssInd_forInStep, ssInd_unit] at h
  exact absurd h (by decide)

/-- For `decide` on `Id` results. -/
instance idDecEq {α : Type} [DecidableEq α] : DecidableEq (Id α) := inferInstanceAs (DecidableEq α)

/-! ## pmap side conditions (all dependent) -/

-- `Array.pmap_congr_left` (`H₁`): `∀ a ∈ xs, p a` fails for `p := False`, `xs := #[0]`.
theorem neg11 : ¬ ∀ {α : Type} {p : α → Prop} (xs : Array α), ∀ a ∈ xs, p a :=
  fun H => H (α := Nat) (p := fun _ => False) #[0] 0 (by simp)

-- `Array.pmap_congr_left` (`H₂`): as for `H₁`.
theorem neg12 : ¬ ∀ {α : Type} {q : α → Prop} (xs : Array α), ∀ a ∈ xs, q a :=
  fun H => H (α := Nat) (q := fun _ => False) #[0] 0 (by simp)

-- `Array.pmap_congr_left` (`h`): `f := 0`, `g := 1` on `#[0]`.
theorem neg13 : ¬ ∀ {α : Type} {β : Type} {p q : α → Prop} {f : (a : α) → p a → β}
    {g : (a : α) → q a → β} (xs : Array α) {H₁ : ∀ (a : α), a ∈ xs → p a} {H₂ : ∀ (a : α), a ∈ xs → q a},
    pmap f xs H₁ = pmap g xs H₂ := by
  intro H
  have h := @H Nat Nat (fun _ => True) (fun _ => True) (fun _ _ => 0) (fun _ _ => 1) #[0]
    (fun _ _ => trivial) (fun _ _ => trivial)
  revert h; decide +kernel

-- `Array.mem_pmap_of_mem` (`H`), `Array.getElem_pmap` (`h`), `Array.pmap_pmap` (`H₁`),
-- `Array.pmap_append'` (`h₁`), `Array.pmap_eq_empty_iff` (`H`), `Array.pmap_eq_map_attach` (`H`),
-- `Array.size_pmap` (`H`), `Array.getElem?_pmap` (`h`), `Array.map_pmap` (`H`), `Array.mem_pmap` (`H`),
-- `Array.countP_pmap` (`H₁`): `∀ a ∈ xs, p a` fails for `p := False`, `xs := #[0]`.
theorem neg14 : ¬ ∀ {α : Type} {p : α → Prop} {xs : Array α}, ∀ a ∈ xs, p a :=
  fun H => H (α := Nat) (p := fun _ => False) (xs := #[0]) 0 (by simp)

-- `Array.pmap_ne_empty_iff` (`H`), `Array.reverse_pmap` (`H`), `Array.back?_pmap` (`H`),
-- `Array.find?_pmap` (`H`): as above.
theorem neg15 : ¬ ∀ {α : Type} {P : α → Prop} {xs : Array α}, ∀ a ∈ xs, P a :=
  fun H => H (α := Nat) (P := fun _ => False) (xs := #[0]) 0 (by simp)

-- `Array.foldr_pmap` (`H`), `Array.foldl_pmap` (`H`), `Array.toList_pmap` (`H`): as above.
theorem neg16 : ¬ ∀ {α : Type} {xs : Array α} {P : α → Prop}, ∀ a ∈ xs, P a :=
  fun H => H (α := Nat) (P := fun _ => False) (xs := #[0]) 0 (by simp)

-- `Array.pmap_eq_self` (`hp`): as above.
theorem neg17 : ¬ ∀ {α : Type} {xs : Array α} {p : α → Prop}, ∀ a ∈ xs, p a :=
  fun H => H (α := Nat) (p := fun _ => False) (xs := #[0]) 0 (by simp)

-- `Array.pmap_append'` (`h₂`): as above, for `ys`.
theorem neg18 : ¬ ∀ {α : Type} {p : α → Prop} {ys : Array α}, ∀ a ∈ ys, p a :=
  fun H => H (α := Nat) (p := fun _ => False) (ys := #[0]) 0 (by simp)

-- `Array.pmap_attachWith` (`H₁`): `q := False`, `xs := #[0]`.
theorem neg19 : ¬ ∀ {α : Type} {q : α → Prop} {xs : Array α}, ∀ a ∈ xs, q a :=
  fun H => H (α := Nat) (q := fun _ => False) (xs := #[0]) 0 (by simp)

-- `Array.pmap_attachWith` (`H₂`): `q := True`, `p := False`, `xs := #[0]`.
theorem neg20 : ¬ ∀ {α : Type} {q : α → Prop} {xs : Array α} {p : { x // q x } → Prop}
    (H₁ : ∀ (x : α), x ∈ xs → q x), ∀ a ∈ xs.attachWith q H₁, p a :=
  fun H => H (α := Nat) (q := fun _ => True) (xs := #[0]) (p := fun _ => False) (fun _ _ => trivial)
    ⟨0, trivial⟩ (by simp)

-- `Array.pmap_attach` (`H`): `p := False`, `xs := #[0]`.
theorem neg21 : ¬ ∀ {α : Type} {xs : Array α} {p : { x // x ∈ xs } → Prop}, ∀ a ∈ xs.attach, p a :=
  fun H => H (α := Nat) (xs := #[0]) (p := fun _ => False) ⟨0, by simp⟩ (by simp)

-- `Array.pmap_pmap` (`H₂`): `p := True`, `q := False`, `g := fun a _ => a`, `xs := #[0]`.
theorem neg22 : ¬ ∀ {α β : Type} {p : α → Prop} {q : β → Prop} {g : (a : α) → p a → β} {xs : Array α}
    (H₁ : ∀ (a : α), a ∈ xs → p a), ∀ a ∈ pmap g xs H₁, q a :=
  fun H => H (α := Nat) (β := Nat) (p := fun _ => True) (q := fun _ => False) (g := fun a _ => a)
    (xs := #[0]) (fun _ _ => trivial) 0 (by simp)

-- `Array.pmap_map` (`H`): `p := False`, `f := id`, `xs := #[0]`.
theorem neg23 : ¬ ∀ {β α : Type} {p : β → Prop} {f : α → β} {xs : Array α}, ∀ a ∈ map f xs, p a :=
  fun H => H (β := Nat) (α := Nat) (p := fun _ => False) (f := id) (xs := #[0]) 0 (by simp)

-- `Array.pmap_append` (`h`): `p := False`, `xs := #[0]`, `ys := #[]`.
theorem neg24 : ¬ ∀ {ι : Type} {p : ι → Prop} {xs ys : Array ι}, ∀ a ∈ xs ++ ys, p a :=
  fun H => H (ι := Nat) (p := fun _ => False) (xs := #[0]) (ys := #[]) 0 (by simp)

-- `Array.pmap_push` (`h`): `P := False`, `a := 0`, `xs := #[]`.
theorem neg25 : ¬ ∀ {α : Type} {P : α → Prop} (a : α) (xs : Array α), ∀ b ∈ xs.push a, P b :=
  fun H => H (α := Nat) (P := fun _ => False) 0 #[] 0 (by simp)

-- `List.pmap_toArray` (`H`): `P := False`, `l := [0]`.
theorem neg26 : ¬ ∀ {α : Type} {l : List α} {P : α → Prop}, ∀ a ∈ l.toArray, P a :=
  fun H => H (α := Nat) (l := [0]) (P := fun _ => False) 0 (by simp)

-- `Array.pmap_reverse` (`H`): `P := False`, `xs := #[0]`.
theorem neg27 : ¬ ∀ {α : Type} {P : α → Prop} {xs : Array α}, ∀ a ∈ xs.reverse, P a :=
  fun H => H (α := Nat) (P := fun _ => False) (xs := #[0]) 0 (by simp)

-- `Array.mem_pmap_of_mem` (`h`): `a := 0`, `xs := #[]`.
theorem neg28 : ¬ ∀ {α : Type} {xs : Array α} {a : α}, a ∈ xs :=
  fun H => by simpa using H (α := Nat) (xs := #[]) (a := 0)

-- `Array.getElem_pmap` (`hi`): `xs := #[]`, `i := 0`.
theorem neg29 : ¬ ∀ {α : Type} {β : Type} {p : α → Prop} (f : (a : α) → p a → β) {xs : Array α}
    (h : ∀ (a : α), a ∈ xs → p a) {i : Nat}, i < (pmap f xs h).size := by
  intro H
  have := H (α := Nat) (β := Nat) (p := fun _ => True) (fun a _ => a) (xs := #[]) (fun _ _ => trivial)
    (i := 0)
  simp at this

/-! ## MapIdx -/

-- `Array.mapFinIdx_induction` (`h0`): `motive := False`, `xs := #[]`.
theorem neg30 : ¬ ∀ {α : Type} {β : Type} (xs : Array α) (f : (i : Nat) → α → i < xs.size → β)
    (motive : Nat → Prop) (p : (i : Nat) → β → i < xs.size → Prop),
    (∀ (i : Nat) (h : i < xs.size), motive i → p i (f i xs[i] h) h ∧ motive (i + 1)) →
      motive xs.size ∧ ∃ (eq : (xs.mapFinIdx f).size = xs.size),
        ∀ (i : Nat) (h : i < xs.size), p i (xs.mapFinIdx f)[i] h := by
  intro H
  exact (H (α := Nat) (β := Nat) #[] (fun i _ _ => i) (fun _ => False) (fun _ _ _ => True)
    (fun _ h => by simp at h)).1

-- `Array.mapFinIdx_induction` (`hs`): `motive := (· = 0)`, `xs := #[0]`.
theorem neg31 : ¬ ∀ {α : Type} {β : Type} (xs : Array α) (f : (i : Nat) → α → i < xs.size → β)
    (motive : Nat → Prop), motive 0 → ∀ (p : (i : Nat) → β → i < xs.size → Prop),
      motive xs.size ∧ ∃ (eq : (xs.mapFinIdx f).size = xs.size),
        ∀ (i : Nat) (h : i < xs.size), p i (xs.mapFinIdx f)[i] h := by
  intro H
  have := (H (α := Nat) (β := Nat) #[0] (fun i _ _ => i) (fun n => n = 0) rfl (fun _ _ _ => True)).1
  simp at this

-- `Array.mapIdx_induction` (`h0`): `motive := False`, `xs := #[]`.
theorem neg32 : ¬ ∀ {α : Type} {β : Type} {f : Nat → α → β} {xs : Array α} {motive : Nat → Prop}
    {p : (i : Nat) → β → i < xs.size → Prop},
    (∀ (i : Nat) (h : i < xs.size), motive i → p i (f i xs[i]) h ∧ motive (i + 1)) →
      motive xs.size ∧ ∃ (eq : (xs.mapIdx f).size = xs.size),
        ∀ (i : Nat) (h : i < xs.size), p i (xs.mapIdx f)[i] h := by
  intro H
  exact (H (α := Nat) (β := Nat) (f := fun i _ => i) (xs := #[]) (motive := fun _ => False)
    (p := fun _ _ _ => True) (fun _ h => by simp at h)).1

-- `Array.mapIdx_induction` (`hs`): `motive := (· = 0)`, `xs := #[0]`.
theorem neg33 : ¬ ∀ {α : Type} {β : Type} {f : Nat → α → β} {xs : Array α} {motive : Nat → Prop},
    motive 0 → ∀ {p : (i : Nat) → β → i < xs.size → Prop},
      motive xs.size ∧ ∃ (eq : (xs.mapIdx f).size = xs.size),
        ∀ (i : Nat) (h : i < xs.size), p i (xs.mapIdx f)[i] h := by
  intro H
  have := (H (α := Nat) (β := Nat) (f := fun i _ => i) (xs := #[0]) (motive := fun n => n = 0) rfl
    (p := fun _ _ _ => True)).1
  simp at this

-- `Array.mapFinIdx_spec` (`hs`): `p := False`, `xs := #[0]`.
theorem neg34 : ¬ ∀ {α : Type} {β : Type} {xs : Array α} {f : (i : Nat) → α → i < xs.size → β}
    {p : (i : Nat) → β → i < xs.size → Prop},
    ∃ (eq : (xs.mapFinIdx f).size = xs.size), ∀ (i : Nat) (h : i < xs.size), p i (xs.mapFinIdx f)[i] h := by
  intro H
  obtain ⟨_, h⟩ := H (α := Nat) (β := Nat) (xs := #[0]) (f := fun i _ _ => i) (p := fun _ _ _ => False)
  exact h 0 (by decide)

-- `Array.mapIdx_spec` (`hs`): `p := False`, `xs := #[0]`.
theorem neg35 : ¬ ∀ {α : Type} {β : Type} {f : Nat → α → β} {xs : Array α}
    {p : (i : Nat) → β → i < xs.size → Prop},
    ∃ (eq : (xs.mapIdx f).size = xs.size), ∀ (i : Nat) (h : i < xs.size), p i (xs.mapIdx f)[i] h := by
  intro H
  obtain ⟨_, h⟩ := H (α := Nat) (β := Nat) (f := fun i _ => i) (xs := #[0]) (p := fun _ _ _ => False)
  exact h 0 (by decide)

-- `Array.exists_of_mem_mapFinIdx` (`h`): `xs := #[]`.
theorem neg36 : ¬ ∀ {β : Type} {α : Type} {b : β} {xs : Array α} {f : (i : Nat) → α → i < xs.size → β},
    ∃ (i : Nat), ∃ (h : i < xs.size), f i xs[i] h = b := by
  intro H
  obtain ⟨i, h, _⟩ := H (β := Nat) (α := Nat) (b := 0) (xs := #[]) (f := fun i _ _ => i)
  simp at h

-- `Array.mapFinIdx_eq_mapIdx` (`h`): `f := 0`, `g := 1`, `xs := #[0]`.
theorem neg37 : ¬ ∀ {α : Type} {β : Type} {xs : Array α} {f : (i : Nat) → α → i < xs.size → β}
    {g : Nat → α → β}, xs.mapFinIdx f = xs.mapIdx g := by
  intro H
  have h := H (α := Nat) (β := Nat) (xs := #[0]) (f := fun _ _ _ => 0) (g := fun _ _ => 1)
  revert h; decide +kernel

-- `Array.getElem_mapFinIdx` (`h`, dependent): `i < (xs.mapFinIdx f).size` fails for `xs := #[]`.
theorem neg38 : ¬ ∀ {α : Type} {β : Type} {xs : Array α} {f : (i : Nat) → α → i < xs.size → β} {i : Nat},
    i < (xs.mapFinIdx f).size := by
  intro H
  have := H (α := Nat) (β := Nat) (xs := #[]) (f := fun i _ _ => i) (i := 0)
  simp at this

-- `Array.mapFinIdx_congr` (`w`, dependent): `xs = ys` fails.
theorem neg39 : ¬ ∀ {α : Type} {xs ys : Array α}, xs = ys := by
  intro H
  have := H (α := Nat) (xs := #[]) (ys := #[0])
  simp at this

/-! ## Congruence lemmas -/

-- `Array.forIn'_congr` (`w`, dependent): `as = bs` fails.
theorem neg40 : ¬ ∀ {α : Type} {as bs : Array α}, as = bs := by
  intro H
  have := H (α := Nat) (as := #[]) (bs := #[0])
  simp at this

-- `Array.forIn'_congr` (`hb`): `m := Id`, empty arrays, `b := 0`, `b' := 1`.
theorem neg41 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [inst : Monad m] {as bs : Array α}
    (w : as = bs) {b b' : β}
    {f : (a' : α) → a' ∈ as → β → m (ForInStep β)}
    {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)},
    (∀ a m b, f a (by simpa [w] using m) b = g a m b) →
    forIn' as b f = forIn' bs b' g := by
  intro H
  have h := @H Id Nat Nat _ #[] #[] rfl 0 1 (fun _ _ b => pure (.yield b)) (fun _ _ b => pure (.yield b))
    (fun _ _ _ => rfl)
  revert h; decide +kernel

-- `Array.forIn'_congr` (`h`): `m := Id`, `as := #[0]`, `f` yields `0`, `g` yields `1`.
theorem neg42 : ¬ ∀ {m : Type → Type} {α : Type} {β : Type} [inst : Monad m] {as bs : Array α}
    (w : as = bs) {b b' : β}, b = b' →
    ∀ {f : (a' : α) → a' ∈ as → β → m (ForInStep β)}
    {g : (a' : α) → a' ∈ bs → β → m (ForInStep β)},
    forIn' as b f = forIn' bs b' g := by
  intro H
  have h := @H Id Nat Nat _ #[0] #[0] rfl 0 0 rfl (fun _ _ _ => pure (.yield 0)) (fun _ _ _ => pure (.yield 1))
  revert h; decide +kernel

-- `Array.any_congr` (`h`): `p := true`, `q := false` on `#[0]`.
theorem neg43 : ¬ ∀ {α : Type} {start₁ start₂ stop₁ stop₂ : Nat} {xs ys : Array α},
    xs = ys → ∀ {p q : α → Bool}, start₁ = start₂ → stop₁ = stop₂ →
      xs.any p start₁ stop₁ = ys.any q start₂ stop₂ := by
  intro H
  have h := H (α := Nat) (start₁ := 0) (start₂ := 0) (stop₁ := 1) (stop₂ := 1) (xs := #[0]) (ys := #[0]) rfl
    (p := fun _ => true) (q := fun _ => false) rfl rfl
  revert h; decide +kernel

-- `Array.any_congr` (`wstart`): `p := true` on `#[0]`, starts `0` and `1`, stop `1`.
theorem neg44 : ¬ ∀ {α : Type} {start₁ start₂ stop₁ stop₂ : Nat} {xs ys : Array α},
    xs = ys → ∀ {p q : α → Bool}, (∀ a, p a = q a) → stop₁ = stop₂ →
      xs.any p start₁ stop₁ = ys.any q start₂ stop₂ := by
  intro H
  have h := H (α := Nat) (start₁ := 0) (start₂ := 1) (stop₁ := 1) (stop₂ := 1) (xs := #[0]) (ys := #[0]) rfl
    (p := fun _ => true) (q := fun _ => true) (fun _ => rfl) rfl
  revert h; decide +kernel

-- `Array.all_congr` (`h`): `p := true`, `q := false` on `#[0]`.
theorem neg45 : ¬ ∀ {α : Type} {start₁ start₂ stop₁ stop₂ : Nat} {xs ys : Array α},
    xs = ys → ∀ {p q : α → Bool}, start₁ = start₂ → stop₁ = stop₂ →
      xs.all p start₁ stop₁ = ys.all q start₂ stop₂ := by
  intro H
  have h := H (α := Nat) (start₁ := 0) (start₂ := 0) (stop₁ := 1) (stop₂ := 1) (xs := #[0]) (ys := #[0]) rfl
    (p := fun _ => true) (q := fun _ => false) rfl rfl
  revert h; decide +kernel

-- `Array.all_congr` (`wstart`): `p := false` on `#[0]`, starts `0` and `1`, stop `1`.
theorem neg46 : ¬ ∀ {α : Type} {start₁ start₂ stop₁ stop₂ : Nat} {xs ys : Array α},
    xs = ys → ∀ {p q : α → Bool}, (∀ a, p a = q a) → stop₁ = stop₂ →
      xs.all p start₁ stop₁ = ys.all q start₂ stop₂ := by
  intro H
  have h := H (α := Nat) (start₁ := 0) (start₂ := 1) (stop₁ := 1) (stop₂ := 1) (xs := #[0]) (ys := #[0]) rfl
    (p := fun _ => false) (q := fun _ => false) (fun _ => rfl) rfl
  revert h; decide +kernel

-- `Array.anyM_congr` (`h`): `m := Id`, `p := true`, `q := false` on `#[0]`.
theorem neg47 : ¬ ∀ {m : Type → Type} {α : Type} {start₁ start₂ stop₁ stop₂ : Nat} [inst : Monad m]
    {xs ys : Array α}, xs = ys → ∀ {p q : α → m Bool}, start₁ = start₂ → stop₁ = stop₂ →
      xs.anyM p start₁ stop₁ = ys.anyM q start₂ stop₂ := by
  intro H
  have h := @H Id Nat 0 0 1 1 _ #[0] #[0] rfl (fun _ => pure true) (fun _ => pure false) rfl rfl
  revert h; decide +kernel

-- `Array.anyM_congr` (`wstart`): `m := Id`, `p := true` on `#[0]`, starts `0` and `1`.
theorem neg48 : ¬ ∀ {m : Type → Type} {α : Type} {start₁ start₂ stop₁ stop₂ : Nat} [inst : Monad m]
    {xs ys : Array α}, xs = ys → ∀ {p q : α → m Bool}, (∀ a, p a = q a) → stop₁ = stop₂ →
      xs.anyM p start₁ stop₁ = ys.anyM q start₂ stop₂ := by
  intro H
  have h := @H Id Nat 0 1 1 1 _ #[0] #[0] rfl (fun _ => pure true) (fun _ => pure true) (fun _ => rfl) rfl
  revert h; decide +kernel

-- `Array.allM_congr` (`wstart`): `m := Id`, `p := false` on `#[0]`, starts `0` and `1`.
theorem neg49 : ¬ ∀ {m : Type → Type} {α : Type} {start₁ start₂ stop₁ stop₂ : Nat} [inst : Monad m]
    {xs ys : Array α}, xs = ys → ∀ {p q : α → m Bool}, (∀ a, p a = q a) → stop₁ = stop₂ →
      xs.allM p start₁ stop₁ = ys.allM q start₂ stop₂ := by
  intro H
  have h := @H Id Nat 0 1 1 1 _ #[0] #[0] rfl (fun _ => pure false) (fun _ => pure false) (fun _ => rfl) rfl
  revert h; decide +kernel

/-! ## Other `Init.Data.Array` lemmas -/

-- `Array.foldl_subtype'` (`h`): `stop := 0`, `xs := #[⟨0, _⟩]`, `f, g := (· + 1)`.
theorem neg50 : ¬ ∀ {α : Type} {β : Type} {stop : Nat} {p : α → Prop} {xs : Array { x // p x }}
    {f : β → { x // p x } → β} {g : β → α → β} {x : β},
    (∀ b x h, f b ⟨x, h⟩ = g b x) → xs.foldl f x 0 stop = xs.unattach.foldl g x := by
  intro H
  have h := H (α := Nat) (β := Nat) (stop := 0) (p := fun _ => True) (xs := #[⟨0, trivial⟩])
    (f := fun b _ => b + 1) (g := fun b _ => b + 1) (x := 0) (fun _ _ _ => rfl)
  revert h; decide +kernel

-- `Array.foldl_map_hom'` (`w`): `stop := 0`, `g := id`, `f, f' := (· + ·)`, `xs := #[1]`.
theorem neg51 : ¬ ∀ {α : Type} {β : Type} {g : α → β} {f : α → α → α} {f' : β → β → β} {a : α}
    {xs : Array α} {stop : Nat}, (∀ x y, f' (g x) (g y) = g (f x y)) →
    (xs.map g).foldl f' (g a) 0 stop = g (xs.foldl f a) := by
  intro H
  have h := H (α := Nat) (β := Nat) (g := id) (f := (· + ·)) (f' := (· + ·)) (a := 0) (xs := #[1])
    (stop := 0) (fun _ _ => rfl)
  revert h; decide +kernel

-- `Array.all_filter'` (`w`): `stop := 0`, `xs := #[0]`, `p := true`, `q := false`.
theorem neg52 : ¬ ∀ {α : Type} {stop : Nat} {xs : Array α} {p q : α → Bool},
    (xs.filter p).all q 0 stop = xs.all fun a => !(p a) || q a := by
  intro H
  have h := H (α := Nat) (stop := 0) (xs := #[0]) (p := fun _ => true) (q := fun _ => false)
  revert h; decide +kernel

-- `Array.all_flatten'` (`w`): `stop := 0`, `xss := #[#[0]]`, `f := false`.
theorem neg53 : ¬ ∀ {α : Type} {stop : Nat} {f : α → Bool} {xss : Array (Array α)},
    xss.flatten.all f 0 stop = xss.all (all · f) := by
  intro H
  have h := H (α := Nat) (stop := 0) (f := fun _ => false) (xss := #[#[0]])
  revert h; decide +kernel

-- `Array.map_inj_right` (`w`): constant `f`, `#[0]` and `#[1]`.
theorem neg54 : ¬ ∀ {α : Type} {β : Type} {xs ys : Array α} {f : α → β}, (map f xs = map f ys ↔ xs = ys) := by
  intro H
  have h := H (α := Nat) (β := Nat) (xs := #[0]) (ys := #[1]) (f := fun _ => 0)
  revert h; decide +kernel

-- `Array.array₂_induction` (`of`): `P := False`.
theorem neg55 : ¬ ∀ {α : Type} (P : Array (Array α) → Prop) (xss : Array (Array α)), P xss :=
  fun H => H (α := Nat) (fun _ => False) #[]

-- `Array.array₃_induction` (`of`): `P := False`.
theorem neg56 : ¬ ∀ {α : Type} (P : Array (Array (Array α)) → Prop) (xss : Array (Array (Array α))), P xss :=
  fun H => H (α := Nat) (fun _ => False) #[]

-- `Array.findIdx?_eq_some_le_of_findIdx?_eq_some` (`w`): `xs := #[0]`, `p := true`, `q := false`.
theorem neg57 : ¬ ∀ {α : Type} {xs : Array α} {p q : α → Bool} {i : Nat},
    xs.findIdx? p = some i → ∃ j, j ≤ i ∧ xs.findIdx? q = some j := by
  intro H
  obtain ⟨j, _, h⟩ := H (α := Nat) (xs := #[0]) (p := fun _ => true) (q := fun _ => false) (i := 0)
    (by decide +kernel)
  rw [show (#[0] : Array Nat).findIdx? (fun _ => false) = none by decide +kernel] at h
  cases h

-- `Array.eraseP_append_left` (`pa`): `p := (· == 1)`, `a := 0`, `xs := #[0]`, `ys := #[1]`.
theorem neg58 : ¬ ∀ {α : Type} {p : α → Bool} {a : α} {xs ys : Array α},
    a ∈ xs → (xs ++ ys).eraseP p = xs.eraseP p ++ ys := by
  intro H
  have h := H (α := Nat) (p := (· == 1)) (a := 0) (xs := #[0]) (ys := #[1]) (by simp)
  revert h; decide +kernel

-- `Array.eraseP_comm` (`h`): `p := true`, `q := (· == 0)`, `xs := #[0, 1]`.
theorem neg59 : ¬ ∀ {α : Type} {p q : α → Bool} {xs : Array α},
    (xs.eraseP p).eraseP q = (xs.eraseP q).eraseP p := by
  intro H
  have h := H (α := Nat) (p := fun _ => true) (q := (· == 0)) (xs := #[0, 1])
  revert h; decide +kernel

-- `Array.reverse_zipWith` (`h`): `f := (· + ·)`, `as := #[0]`, `bs := #[1, 2]`.
theorem neg60 : ¬ ∀ {α : Type} {α_1 : Type} {α_2 : Type} {f : α → α_1 → α_2} {as : Array α} {bs : Array α_1},
    (zipWith f as bs).reverse = zipWith f as.reverse bs.reverse := by
  intro H
  have h := H (α := Nat) (α_1 := Nat) (α_2 := Nat) (f := (· + ·)) (as := #[0]) (bs := #[1, 2])
  revert h; decide +kernel

/-! ## mergeSort -/

/-- Rock-paper-scissors on `Fin 3`: total, not transitive. -/
def rps (a b : Fin 3) : Bool := a == b || b == a + 1

/-- `a = b` or `a = 0, b = 1` on `Fin 3`: transitive, not total. -/
def le01 (a b : Fin 3) : Bool := a == b || (a == 0 && b == 1)

theorem ms2 {α : Type} (a b : α) (le : α → α → Bool) : [a, b].mergeSort le = List.merge [a] [b] le := by
  rw [List.mergeSort]; simp

theorem ms3 {α : Type} (a b c : α) (le : α → α → Bool) :
    [a, b, c].mergeSort le = List.merge (List.merge [a] [b] le) [c] le := by
  rw [List.mergeSort]; simp [List.cons_merge_cons]

-- `Array.pairwise_mergeSort` (`trans`): `rps` on `#[0, 1, 2]` sorts to `#[2, 0, 1]`.
theorem neg61 : ¬ ∀ {α : Type} {le : α → α → Bool},
    (∀ (a b : α), (le a b || le b a) = true) →
      ∀ {xs : Array α}, (xs.mergeSort le).toList.Pairwise (le · ·) := by
  intro H
  have h := H (le := rps) (by decide) (xs := #[0, 1, 2])
  rw [toList_mergeSort] at h
  simp +decide [ms3, rps] at h

-- `Array.pairwise_mergeSort` (`total`): `le := false` on `#[0, 1]`.
theorem neg62 : ¬ ∀ {α : Type} {le : α → α → Bool},
    (∀ (a b c : α), le a b = true → le b c = true → le a c = true) →
      ∀ {xs : Array α}, (xs.mergeSort le).toList.Pairwise (le · ·) := by
  intro H
  have h := H (α := Nat) (le := fun _ _ => false) (by simp) (xs := #[0, 1])
  rw [toList_mergeSort] at h
  simp at h

-- `Array.sublist_mergeSort` (`trans`): `rps`, `xs := #[0, 1, 2]` sorts to `#[2, 0, 1]`, `ys := [1, 2]`.
theorem neg63 : ¬ ∀ {α : Type} {xs : Array α} {le : α → α → Bool},
    (∀ (a b : α), (le a b || le b a) = true) →
      ∀ {ys : List α}, ys.Pairwise (le · ·) → ys.Sublist xs.toList → ys.Sublist (xs.mergeSort le).toList := by
  intro H
  have h := H (xs := #[0, 1, 2]) (le := rps) (by decide) (ys := [1, 2]) (by decide) (by decide)
  rw [toList_mergeSort] at h
  simp +decide [ms3, rps] at h

-- `Array.sublist_mergeSort` (`total`): `le01`, `xs := #[0, 2, 1]` sorts to `#[1, 2, 0]`, `ys := [0, 1]`.
theorem neg64 : ¬ ∀ {α : Type} {xs : Array α} {le : α → α → Bool},
    (∀ (a b c : α), le a b = true → le b c = true → le a c = true) →
      ∀ {ys : List α}, ys.Pairwise (le · ·) → ys.Sublist xs.toList → ys.Sublist (xs.mergeSort le).toList := by
  intro H
  have h := H (xs := #[0, 2, 1]) (le := le01) (by decide) (ys := [0, 1]) (by decide) (by decide)
  rw [toList_mergeSort] at h
  simp +decide [ms3, le01] at h

-- `Array.sublist_mergeSort` (the `Pairwise` hypothesis): `(· ≤ ·)`, `xs := #[1, 0]`, `ys := [1, 0]`.
theorem neg65 : ¬ ∀ {α : Type} {xs : Array α} {le : α → α → Bool},
    (∀ (a b c : α), le a b = true → le b c = true → le a c = true) →
    (∀ (a b : α), (le a b || le b a) = true) →
      ∀ {ys : List α}, ys.Sublist xs.toList → ys.Sublist (xs.mergeSort le).toList := by
  intro H
  have h := H (xs := #[1, 0]) (le := fun a b => decide (a ≤ b)) (by simp; omega) (by simp; omega)
    (ys := [1, 0]) (by decide)
  rw [toList_mergeSort] at h
  simp at h
  revert h; decide

-- `Array.pair_sublist_mergeSort` (`trans`): `rps`, `a, b := 1, 2`, `xs := #[0, 1, 2]`.
theorem neg66 : ¬ ∀ {α : Type} {le : α → α → Bool} {a b : α} {xs : Array α},
    (∀ (a b : α), (le a b || le b a) = true) →
      le a b = true → [a, b].Sublist xs.toList → [a, b].Sublist (xs.mergeSort le).toList := by
  intro H
  have h := H (le := rps) (a := 1) (b := 2) (xs := #[0, 1, 2]) (by decide) (by decide) (by decide)
  rw [toList_mergeSort] at h
  simp +decide [ms3, rps] at h

-- `Array.pair_sublist_mergeSort` (`total`): `le01`, `a, b := 0, 1`, `xs := #[0, 2, 1]`.
theorem neg67 : ¬ ∀ {α : Type} {le : α → α → Bool} {a b : α} {xs : Array α},
    (∀ (a b c : α), le a b = true → le b c = true → le a c = true) →
      le a b = true → [a, b].Sublist xs.toList → [a, b].Sublist (xs.mergeSort le).toList := by
  intro H
  have h := H (le := le01) (a := 0) (b := 1) (xs := #[0, 2, 1]) (by decide) (by decide) (by decide)
  rw [toList_mergeSort] at h
  simp +decide [ms3, le01] at h

-- `Array.pair_sublist_mergeSort` (`hab`): `(· ≤ ·)`, `a, b := 1, 0`, `xs := #[1, 0]`.
theorem neg68 : ¬ ∀ {α : Type} {le : α → α → Bool} {a b : α} {xs : Array α},
    (∀ (a b c : α), le a b = true → le b c = true → le a c = true) →
    (∀ (a b : α), (le a b || le b a) = true) →
      [a, b].Sublist xs.toList → [a, b].Sublist (xs.mergeSort le).toList := by
  intro H
  have h := H (le := fun a b => decide (a ≤ b)) (a := 1) (b := 0) (xs := #[1, 0]) (by simp; omega)
    (by simp; omega) (by decide)
  rw [toList_mergeSort] at h
  simp at h
  revert h; decide

-- `Array.mergeSort_of_pairwise` (the `Pairwise` hypothesis): `(· ≤ ·)`, `xs := #[1, 0]`.
theorem neg69 : ¬ ∀ {α : Type} {le : α → α → Bool} {xs : Array α}, xs.mergeSort le = xs := by
  intro H
  have h := H (le := fun a b => decide (a ≤ b)) (xs := #[1, 0])
  rw [mergeSort_eq_toArray_mergeSort_toList] at h
  simp at h

-- `Array.map_mergeSort` (`hxs`): `r := (· ≤ ·)`, `s := (· ≥ ·)`, `f := id`, `xs := #[0, 1]`.
theorem neg70 : ¬ ∀ {α : Type} {β : Type} {r : α → α → Bool} {s : β → β → Bool} {f : α → β} {xs : Array α},
    (xs.mergeSort r).map f = (xs.map f).mergeSort s := by
  intro H
  have h := H (r := fun a b => decide (a ≤ b)) (s := fun a b => decide (b ≤ a)) (f := id) (xs := #[0, 1])
  rw [mergeSort_eq_toArray_mergeSort_toList, mergeSort_eq_toArray_mergeSort_toList] at h
  simp at h

/-! ## Lexicographic order -/

/-- `Nat` with the empty `<`. -/
def NE := Nat
instance : LT NE := ⟨fun _ _ => False⟩
instance : DecidableEq NE := inferInstanceAs (DecidableEq Nat)
instance neDecLT : DecidableRel (α := NE) (· < ·) := fun _ _ => isFalse id
instance : OfNat NE n := ⟨(n : Nat)⟩

/-- A one-element type with the empty `<` (trichotomous). -/
def U1 := Unit
instance : LT U1 := ⟨fun _ _ => False⟩
instance : DecidableEq U1 := inferInstanceAs (DecidableEq Unit)
instance : DecidableRel (α := U1) (· < ·) := fun _ _ => isFalse id
instance : Std.Trichotomous (· < · : U1 → U1 → Prop) := ⟨fun _ _ _ _ => rfl⟩

-- `Array.map_lt_map_iff_of_injective` (`hf`): `f := id : Nat → NE` (injective), `#[0]`, `#[1]`.
theorem neg71 : ¬ ∀ {α : Type} {β : Type} [inst : LT α] [inst_1 : LT β] (f : α → β),
    Function.Injective f → ∀ {xs ys : Array α}, xs.map f < ys.map f ↔ xs < ys := by
  intro H
  have h := H (α := Nat) (β := NE) (fun n => n) (fun _ _ h => h) (xs := #[0]) (ys := #[1])
  revert h; decide +kernel

-- `Array.map_lt_map_iff_of_injective` (`hfinj`): `f := 0 : NE → Nat`, `#[0]`, `#[1, 1]`.
theorem neg72 : ¬ ∀ {α : Type} {β : Type} [inst : LT α] [inst_1 : LT β] (f : α → β),
    (∀ a b, f a < f b ↔ a < b) → ∀ {xs ys : Array α}, xs.map f < ys.map f ↔ xs < ys := by
  intro H
  have h := H (α := NE) (β := Nat) (fun _ => 0) (fun _ _ => ⟨fun h => absurd h (Nat.lt_irrefl 0), False.elim⟩)
    (xs := #[0]) (ys := #[1, 1])
  revert h; decide +kernel

-- `Array.map_le_map_iff_of_injective` (`hf`): as for `<`, with `#[1]`, `#[0]`.
theorem neg73 : ¬ ∀ {α : Type} {β : Type} [inst : LT α] [inst_1 : LT β] (f : α → β),
    Function.Injective f → ∀ {xs ys : Array α}, xs.map f ≤ ys.map f ↔ xs ≤ ys := by
  intro H
  have h := H (α := Nat) (β := NE) (fun n => n) (fun _ _ h => h) (xs := #[1]) (ys := #[0])
  revert h; decide +kernel

-- `Array.map_le_map_iff_of_injective` (`hfinj`): as for `<`, with `#[1, 1]`, `#[0]`.
theorem neg74 : ¬ ∀ {α : Type} {β : Type} [inst : LT α] [inst_1 : LT β] (f : α → β),
    (∀ a b, f a < f b ↔ a < b) → ∀ {xs ys : Array α}, xs.map f ≤ ys.map f ↔ xs ≤ ys := by
  intro H
  have h := H (α := NE) (β := Nat) (fun _ => 0) (fun _ _ => ⟨fun h => absurd h (Nat.lt_irrefl 0), False.elim⟩)
    (xs := #[1, 1]) (ys := #[0])
  revert h; decide +kernel

/-- `f 0 = #[0]`, `f 1 = #[0, 0]`: strictly monotone, never empty, but `f 0` is a prefix of `f 1`. -/
def zeros (n : Fin 2) : Array Nat := Array.replicate (n + 1) 0

-- `Array.flatMap_lt_flatMap_iff` (`hp`): `α := Fin 2`, `zeros`; `#[0, 1]` ↦ 3 zeros, `#[1]` ↦ 2 zeros.
theorem neg75 : ¬ ∀ {α : Type} {β : Type} [inst : LT α] [Std.Trichotomous (· < · : α → α → Prop)] [inst_2 : LT β]
    [Std.Asymm (· < · : β → β → Prop)] (f : α → Array β),
    (∀ a b, a < b → f a < f b) → (∀ a, f a ≠ #[]) →
    ∀ {xs ys : Array α}, xs.flatMap f < ys.flatMap f ↔ xs < ys := by
  intro H
  have h := H (α := Fin 2) (β := Nat) zeros (by decide) (by decide) (xs := #[0, 1]) (ys := #[1])
  revert h; decide +kernel

-- `Array.flatMap_lt_flatMap_iff` (`hx`): `α := U1`, `f := #[]`, `#[]` and `#[()]`.
theorem neg76 : ¬ ∀ {α : Type} {β : Type} [inst : LT α] [Std.Trichotomous (· < · : α → α → Prop)] [inst_2 : LT β]
    [Std.Asymm (· < · : β → β → Prop)] (f : α → Array β),
    (∀ a b, a < b → f a < f b) → (∀ a b zs, f a ++ zs = f b → a = b) →
    ∀ {xs ys : Array α}, xs.flatMap f < ys.flatMap f ↔ xs < ys := by
  intro H
  have h := H (α := U1) (β := Nat) (fun _ => #[]) (fun _ _ h => False.elim h) (fun _ _ _ _ => rfl)
    (xs := #[]) (ys := #[()])
  revert h; decide +kernel

-- `Array.flatMap_le_flatMap_iff` (`hp`): as for `<`, with `#[1]`, `#[0, 1]`.
theorem neg77 : ¬ ∀ {α : Type} {β : Type} [inst : LT α] [Std.Trichotomous (· < · : α → α → Prop)] [inst_2 : LT β]
    [Std.Asymm (· < · : β → β → Prop)] (f : α → Array β),
    (∀ a b, a < b → f a < f b) → (∀ a, f a ≠ #[]) →
    ∀ {xs ys : Array α}, xs.flatMap f ≤ ys.flatMap f ↔ xs ≤ ys := by
  intro H
  have h := H (α := Fin 2) (β := Nat) zeros (by decide) (by decide) (xs := #[1]) (ys := #[0, 1])
  revert h; decide +kernel

-- `Array.flatMap_le_flatMap_iff` (`hx`): as for `<`, with `#[()]`, `#[]`.
theorem neg78 : ¬ ∀ {α : Type} {β : Type} [inst : LT α] [Std.Trichotomous (· < · : α → α → Prop)] [inst_2 : LT β]
    [Std.Asymm (· < · : β → β → Prop)] (f : α → Array β),
    (∀ a b, a < b → f a < f b) → (∀ a b zs, f a ++ zs = f b → a = b) →
    ∀ {xs ys : Array α}, xs.flatMap f ≤ ys.flatMap f ↔ xs ≤ ys := by
  intro H
  have h := H (α := U1) (β := Nat) (fun _ => #[]) (fun _ _ h => False.elim h) (fun _ _ _ _ => rfl)
    (xs := #[()]) (ys := #[])
  revert h; decide +kernel

end RestArrayHand
