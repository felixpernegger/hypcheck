/-!
Hand resolution of the 33 hypotheses in `Init.Data.Slice.*` (generic `Std.Slice` lemmas and
`Subarray`) that `HypCheck.lean` left unresolved. For each hypothesis `hᵢ` of theorem `T`, this file
proves either `T'` (the theorem without `hᵢ`: removable) or `¬T'` (necessary). None of them is
dependent. 30 are decided here (29 necessary, 1 removable); 3 `[Finite α Id]` hypotheses stay
unresolved (see the end of the file).

Models used:
* `S0 = #[0].toSubarray` with the library's `Subarray` iterator (finite, default `IteratorLoop`,
  lawful `SliceSize`), combined with a broken `IteratorLoop` (`bogusLoop`: every loop returns `init`)
  or a broken `SliceSize` (`bogusSize`: always 5).
* `NatM`, a non-lawful monad whose values are `Nat`s counting the outer binds (`bind x _ = x + 1`,
  `pure _ = 0`, `map` free). A list loop over `[0]` has one bind at the top, the iterator loop two
  (the `IteratorLoop.finiteForIn'` wrapper adds one).
* `CI`, a non-finite iterator that always yields `0`. For non-finite iterators `LawfulIteratorLoop`
  says nothing about the `fun _ _ _ => True` loops used by `fold`/`foldM`/`forIn`/`length` (it only
  constrains well-founded loops), so a lawful `IteratorLoop` can run those loops on one element
  more than `toList` (or than the default loop) has: `ciLoopL`, `ciLoopD`.

Run with the lean4 repo's stage1 binary: `lean checks/SliceHand.lean`.
-/

open Std Std.Iterators

universe u v

namespace SliceHand

/-! ## Models -/

abbrev S0 : Subarray Nat := #[0].toSubarray

theorem S0_toList : Slice.toList S0 = [0] := by simp [Subarray.toList_eq]

theorem S0_toArray : Slice.toArray S0 = #[0] := by
  rw [← Subarray.toArray_toList, S0_toList]

theorem S0_size : Std.Slice.size S0 = 1 := rfl

/-- Every loop returns its initial value. -/
def bogusLoop {n : Type → Type} [Monad n] : IteratorLoop (SubarrayIterator Nat) Id n :=
  ⟨fun _ _ _ _ init _ => pure init⟩

def bogusSize : Std.Slice.SliceSize (Std.Slice.Internal.SubarrayData Nat) := ⟨fun _ => 5⟩

theorem foldl_succ {β : Type} (l : List β) (n : Nat) :
    l.foldl (fun c _ => c + 1) n = n + l.length := by
  induction l generalizing n <;> simp_all [Nat.add_assoc, Nat.add_comm 1]

/-- Non-lawful monad counting the outer binds. -/
def NatM (_ : Type) : Type := Nat

instance : Monad NatM where
  pure _ := (0 : Nat)
  bind x _ := (show Nat from x) + 1
  map _ x := (show Nat from x)

/-- One unfolding of the default loop in `NatM`, for an iterator whose first step yields. -/
theorem natM_forIn {α β : Type} [Iterator α Id β] {γ : Type} (Pl : β → γ → ForInStep γ → Prop)
    (it : IterM (α := α) Id β) (init : γ)
    (f : (b : β) → it.IsPlausibleIndirectOutput b → (c : γ) → NatM (Subtype (Pl b c)))
    (wf : IteratorLoop.WellFounded α Id Pl) (it' : IterM (α := α) Id β) (out : β) (h)
    (hs : it.step.run.inflate = ⟨.yield it' out, h⟩) :
    (IteratorLoop.defaultImplementation : IteratorLoop α Id NatM).forIn
        (fun _ _ g c => g c.run) γ Pl it init f
      = (show Nat from (f out (.direct ⟨_, h⟩) init)) + 1 := by
  haveI : Nonempty γ := ⟨init⟩
  show IterM.DefaultConsumers.forIn' _ _ _ _ _ _ _ _ = _
  rw [IterM.DefaultConsumers.forIn', WellFounded.extrinsicFix₃_eq_apply (InvImage.wf _ wf)]
  dsimp only
  split
  · rename_i heq; rw [hs] at heq; cases heq; rfl
  · rename_i heq; rw [hs] at heq; cases heq
  · rename_i heq; rw [hs] at heq; cases heq

theorem S0_step : (Slice.Internal.iter S0).toIterM.step.run.inflate =
    ⟨.yield ⟨⟨#[0].toSubarray 1 1⟩⟩ 0, rfl⟩ := by
  simp only [IterM.step, Iterator.step, Id.run_pure, Shrink.inflate_deflate]
  rfl

/-- The `S0` iterator loop in `NatM` with a body returning `pure`: two binds. -/
theorem S0_natM {γ : Type} (Pl : Nat → γ → ForInStep γ → Prop) (init : γ) (f) :
    (IteratorLoop.defaultImplementation : IteratorLoop (SubarrayIterator Nat) Id NatM).forIn
        (fun _ _ g c => g c.run) γ Pl (Slice.Internal.iter S0).toIterM init f
      = (show Nat from (f 0 (.direct ⟨_, rfl⟩) init)) + 1 :=
  natM_forIn _ _ _ _ IteratorLoop.wellFounded_of_finite _ _ _ S0_step

/-- Non-finite iterator: always yields `0`. -/
structure CI where
  u : Unit

instance ciIter : Iterator CI Id Nat where
  IsPlausibleStep _ _ := True
  step it := pure (.deflate ⟨.yield it 0, trivial⟩)

instance ciToIter : ToIterator (Slice Unit) Id CI Nat := ToIterator.of CI (fun _ => ⟨⟨()⟩⟩)

abbrev s0 : Slice Unit := ⟨()⟩

theorem ci_out (it : IterM (α := CI) Id Nat) (b : Nat) : it.IsPlausibleIndirectOutput b :=
  .direct ⟨it, trivial⟩

theorem not_wf_of_refl {α : Sort _} {r : α → α → Prop} (x : α) (h : r x x) : ¬ WellFounded r := by
  intro wf
  have : ∀ y, Acc r y → ¬ r y y := by
    intro y hy
    induction hy with
    | intro y _ ih => exact fun hyy => ih y hyy hyy
  exact this x (wf.apply x) h

theorem ci_not_wf {γ : Type} (Pl : Nat → γ → ForInStep γ → Prop) (c : γ)
    (hc : Pl 0 c (.yield c)) : ¬ IteratorLoop.WellFounded CI Id Pl :=
  not_wf_of_refl (⟨⟨()⟩⟩, c) (Or.inl ⟨0, trivial, hc⟩)

/-- Lawful; on non-well-founded loops it runs the body over `toList ++ [0]`. -/
noncomputable def ciLoopL : IteratorLoop CI Id Id where
  forIn lift γ Pl it init f :=
    open Classical in
    if IteratorLoop.WellFounded CI Id Pl then
      IteratorLoop.defaultImplementation.forIn lift γ Pl it init f
    else
      ((IterM.toList it).run ++ [0]).foldl (fun c b => (f b (ci_out it b) c).run.1.value) init

theorem ciLoopL_lawful : @LawfulIteratorLoop Nat CI Id Id _ _ _ ciLoopL :=
  @LawfulIteratorLoop.mk Nat CI Id Id _ _ _ ciLoopL
    (fun _ _ _ _ _ _ wf _ => ite_eq_left_of_eq_true _ _ (eq_true wf))

theorem ciL_neg {γ : Type} (lift : (γ' : Type) → (δ : Type) → (γ' → Id δ) → Id γ' → Id δ)
    (Pl : Nat → γ → ForInStep γ → Prop) (it : IterM (α := CI) Id Nat) (init : γ)
    (f : (b : Nat) → it.IsPlausibleIndirectOutput b → (c : γ) → Id (Subtype (Pl b c)))
    (h : ¬ IteratorLoop.WellFounded CI Id Pl) :
    ciLoopL.forIn lift γ Pl it init f =
      ((IterM.toList it).run ++ [0]).foldl (fun c b => (f b (ci_out it b) c).run.1.value) init :=
  ite_eq_right_of_eq_false _ _ (eq_false h)

/-- Lawful; on non-well-founded loops it applies the body to `0` once more after the default loop. -/
noncomputable def ciLoopD : IteratorLoop CI Id Id where
  forIn lift γ Pl it init f :=
    open Classical in
    if IteratorLoop.WellFounded CI Id Pl then
      IteratorLoop.defaultImplementation.forIn lift γ Pl it init f
    else
      (f 0 (ci_out it 0) (IteratorLoop.defaultImplementation.forIn lift γ Pl it init f)).run.1.value

theorem ciLoopD_lawful : @LawfulIteratorLoop Nat CI Id Id _ _ _ ciLoopD :=
  @LawfulIteratorLoop.mk Nat CI Id Id _ _ _ ciLoopD
    (fun _ _ _ _ _ _ wf _ => ite_eq_left_of_eq_true _ _ (eq_true wf))

theorem ciD_neg {γ : Type} (lift : (γ' : Type) → (δ : Type) → (γ' → Id δ) → Id γ' → Id δ)
    (Pl : Nat → γ → ForInStep γ → Prop) (it : IterM (α := CI) Id Nat) (init : γ)
    (f : (b : Nat) → it.IsPlausibleIndirectOutput b → (c : γ) → Id (Subtype (Pl b c)))
    (h : ¬ IteratorLoop.WellFounded CI Id Pl) :
    ciLoopD.forIn lift γ Pl it init f =
      (f 0 (ci_out it 0) (IteratorLoop.defaultImplementation.forIn lift γ Pl it init f)).run.1.value :=
  ite_eq_right_of_eq_false _ _ (eq_false h)

/-- Lawful `SliceSize` for `CI`: the default loop's length. -/
def ciSize : Std.Slice.SliceSize Unit :=
  ⟨fun s => letI : IteratorLoop CI Id Id := .defaultImplementation; (ToIterator.iter s).length⟩

theorem ciSize_lawful : @Std.Slice.LawfulSliceSize CI Nat Unit ciSize _ _ :=
  @Std.Slice.LawfulSliceSize.mk CI Nat Unit ciSize _ _ (fun _ => rfl)

end SliceHand

open SliceHand

/-! ## `[LawfulIteratorLoop ..]`: `S0` with `bogusLoop` (all necessary) -/

-- `Std.Slice.foldl_toArray` (`[LawfulIteratorLoop α Id Id]`): `S0`, `bogusLoop`, `f = (· + 1)`,
-- `init = 0`: `#[0].foldl f 0 = 1`, but the loop returns `0`.
example : ¬ ∀ {γ : Type} {α β : Type} {δ : Type} [inst : ToIterator (Slice γ) Id α β]
    [inst_1 : Iterator α Id β] [inst_2 : IteratorLoop α Id Id] [Finite α Id] {s : Slice γ}
    {init : δ} {f : δ → β → δ}, Array.foldl f init s.toArray = Slice.foldl f init s := by
  intro H
  have h1 := @H _ _ _ Nat _ _ bogusLoop _ S0 0 (fun a _ => a + 1)
  rw [S0_toArray] at h1
  exact absurd h1 (by decide)

-- `Std.Slice.foldl_toList` (`[LawfulIteratorLoop α Id Id]`): as for `foldl_toArray`.
example : ¬ ∀ {γ : Type} {α β : Type} {δ : Type} [inst : ToIterator (Slice γ) Id α β]
    [inst_1 : Iterator α Id β] [inst_2 : IteratorLoop α Id Id] [Finite α Id] {s : Slice γ}
    {init : δ} {f : δ → β → δ}, List.foldl f init s.toList = Slice.foldl f init s := by
  intro H
  have h1 := @H _ _ _ Nat _ _ bogusLoop _ S0 0 (fun a _ => a + 1)
  rw [S0_toList] at h1
  exact absurd h1 (by decide)

-- `Std.Slice.foldlM_toList` (`[LawfulIteratorLoop α Id m]`): `m = Id`, otherwise as for
-- `foldl_toArray`.
example : ¬ ∀ {γ : Type} {α β : Type} {m : Type → Type} {δ : Type} [inst : Monad m]
    [inst_1 : ToIterator (Slice γ) Id α β] [inst_2 : Iterator α Id β] [inst_3 : IteratorLoop α Id m]
    [Finite α Id] [LawfulMonad m] {s : Slice γ} {init : δ} {f : δ → β → m δ},
    List.foldlM f init s.toList = Slice.foldlM f init s := by
  intro H
  have h1 := @H _ _ _ Id Nat _ _ _ bogusLoop _ _ S0 0 (fun a _ => pure (a + 1))
  rw [S0_toList] at h1
  have : (1 : Nat) = 0 := h1
  omega

-- `Std.Slice.foldlM_toArray` (`[LawfulIteratorLoop α Id m]`): as for `foldlM_toList`.
example : ¬ ∀ {γ : Type} {α β : Type} {m : Type → Type} {δ : Type} [inst : Monad m]
    [inst_1 : ToIterator (Slice γ) Id α β] [inst_2 : Iterator α Id β] [inst_3 : IteratorLoop α Id m]
    [Finite α Id] [LawfulMonad m] {s : Slice γ} {init : δ} {f : δ → β → m δ},
    Array.foldlM f init s.toArray = Slice.foldlM f init s := by
  intro H
  have h1 := @H _ _ _ Id Nat _ _ _ bogusLoop _ _ S0 0 (fun a _ => pure (a + 1))
  rw [S0_toArray] at h1
  have : (1 : Nat) = 0 := h1
  omega

-- `Std.Slice.forIn_toList` (`[LawfulIteratorLoop α Id m]`): `m = Id`, `S0`, `bogusLoop`,
-- `f _ acc = yield (acc + 1)`, `init = 0`: the list loop gives 1, the slice loop 0.
example : ¬ ∀ {α : Type} {γ : Type} {β : Type} {m : Type → Type} [inst : Monad m]
    [LawfulMonad m] {δ : Type} [inst_2 : ToIterator (Slice γ) Id α β] [inst_3 : Iterator α Id β]
    [inst_4 : IteratorLoop α Id m] [Finite α Id] {s : Slice γ} {init : δ}
    {f : β → δ → m (ForInStep δ)}, forIn s.toList init f = forIn s init f := by
  intro H
  have h1 := @H _ _ _ Id _ _ Nat _ _ bogusLoop _ S0 0 (fun _ acc => pure (.yield (acc + 1)))
  rw [S0_toList] at h1
  have : (1 : Nat) = 0 := h1
  omega

-- `Std.Slice.forIn_toArray` (`[LawfulIteratorLoop α Id m]`): as for `forIn_toList`.
example : ¬ ∀ {α : Type} {γ : Type} {β : Type} {m : Type → Type} [inst : Monad m]
    [LawfulMonad m] {δ : Type} [inst_2 : ToIterator (Slice γ) Id α β] [inst_3 : Iterator α Id β]
    [inst_4 : IteratorLoop α Id m] [Finite α Id] {s : Slice γ} {init : δ}
    {f : β → δ → m (ForInStep δ)}, forIn s.toArray init f = forIn s init f := by
  intro H
  have h1 := @H _ _ _ Id _ _ Nat _ _ bogusLoop _ S0 0 (fun _ acc => pure (.yield (acc + 1)))
  rw [S0_toArray] at h1
  have : (1 : Nat) = 0 := h1
  omega

-- `Std.Slice.Internal.size_eq_length_iter` (`[LawfulIteratorLoop α Id Id]`): `S0` (size 1) with
-- `bogusLoop`, whose `length` is 0.
example : ¬ ∀ {γ : Type} {α β : Type} [inst : ToIterator (Slice γ) Id α β]
    [inst_1 : Iterator α Id β] [Finite α Id] [inst_3 : IteratorLoop α Id Id] {s : Slice γ}
    [inst_5 : Std.Slice.SliceSize γ] [Std.Slice.LawfulSliceSize γ],
    s.size = (Std.Slice.Internal.iter s).length := by
  intro H
  have h1 := @H _ _ _ _ _ _ bogusLoop S0 _ _
  exact absurd h1 (by decide)

/-! ## `[LawfulSliceSize γ]` and its projection: `S0` with `bogusSize` (all necessary) -/

-- `Std.Slice.size_toArray_eq_size` (`[LawfulSliceSize γ]`): `S0` with `bogusSize` (5); the array
-- has size 1 (by the theorem itself with the lawful `Subarray` size).
example : ¬ ∀ {γ : Type} {α β : Type} [inst : ToIterator (Slice γ) Id α β]
    [inst_1 : Iterator α Id β] [inst_2 : Std.Slice.SliceSize γ] [Finite α Id] {s : Slice γ},
    s.toArray.size = s.size := by
  intro H
  have h1 := @H _ _ _ _ _ bogusSize _ S0
  rw [Std.Slice.size_toArray_eq_size] at h1
  exact absurd h1 (by decide)

-- `Std.Slice.length_toList_eq_size` (`[LawfulSliceSize γ]`): as for `size_toArray_eq_size`.
example : ¬ ∀ {γ : Type} {α β : Type} [inst : ToIterator (Slice γ) Id α β]
    [inst_1 : Iterator α Id β] {s : Slice γ} [inst_2 : Std.Slice.SliceSize γ] [Finite α Id],
    s.toList.length = s.size := by
  intro H
  have h1 := @H _ _ _ _ _ S0 bogusSize _
  rw [Std.Slice.length_toList_eq_size] at h1
  exact absurd h1 (by decide)

-- `Std.Slice.length_toListRev_eq_size` (`[LawfulSliceSize γ]`): as for `size_toArray_eq_size`.
example : ¬ ∀ {γ : Type} {α β : Type} [inst : ToIterator (Slice γ) Id α β]
    [inst_1 : Iterator α Id β] {s : Slice γ} [inst_2 : IteratorLoop α Id Id]
    [inst_3 : Std.Slice.SliceSize γ] [Finite α Id] [LawfulIteratorLoop α Id Id],
    s.toListRev.length = s.size := by
  intro H
  have h1 := @H _ _ _ _ _ S0 _ bogusSize _ _
  rw [Std.Slice.length_toListRev_eq_size] at h1
  exact absurd h1 (by decide)

-- `Std.Slice.Internal.size_eq_length_iter` (`[LawfulSliceSize γ]`): as for `size_toArray_eq_size`.
example : ¬ ∀ {γ : Type} {α β : Type} [inst : ToIterator (Slice γ) Id α β]
    [inst_1 : Iterator α Id β] [Finite α Id] [inst_3 : IteratorLoop α Id Id]
    [LawfulIteratorLoop α Id Id] {s : Slice γ} [inst_5 : Std.Slice.SliceSize γ],
    s.size = (Std.Slice.Internal.iter s).length := by
  intro H
  have h1 := @H _ _ _ _ _ _ _ _ S0 bogusSize
  rw [← Std.Slice.Internal.size_eq_length_iter] at h1
  exact absurd h1 (by decide)

-- `Std.Slice.LawfulSliceSize.lawful` (`self`): `S0` with `bogusSize`; the default `length` of the
-- `S0` iterator is 1 by the lawful `Subarray` instance.
example : ¬ ∀ {α β : Type} {γ : Type} {inst : Std.Slice.SliceSize γ}
    {inst_1 : ToIterator (Slice γ) Id α β} {inst_2 : Iterator α Id β} (s : Slice γ),
    Std.Slice.SliceSize.size s =
      (letI : IteratorLoop α Id Id := .defaultImplementation; (ToIterator.iter s).length) := by
  intro H
  have h1 := @H (SubarrayIterator Nat) Nat _ bogusSize inferInstance inferInstance S0
  rw [← Std.Slice.LawfulSliceSize.lawful] at h1
  exact absurd h1 (by decide)

/-! ## `[LawfulMonad m]`: `NatM` on `S0` (all necessary) -/

-- `Std.Slice.foldlM_toList` (`[LawfulMonad m]`): `m = NatM`, `S0` with its (default, lawful) loop,
-- `f _ _ = pure 0`: the list fold over `[0]` is 1, the iterator fold 2.
example : ¬ ∀ {γ : Type} {α β : Type} {m : Type → Type} {δ : Type} [inst : Monad m]
    [inst_1 : ToIterator (Slice γ) Id α β] [inst_2 : Iterator α Id β] [inst_3 : IteratorLoop α Id m]
    [LawfulIteratorLoop α Id m] [Finite α Id] {s : Slice γ} {init : δ} {f : δ → β → m δ},
    List.foldlM f init s.toList = Slice.foldlM f init s := by
  intro H
  have h1 := @H _ _ _ NatM Nat _ _ _ _ _ _ S0 0 (fun _ _ => (0 : Nat))
  rw [S0_toList] at h1
  have e : Slice.foldlM (m := NatM) (fun _ _ => (0 : Nat)) 0 S0 = _ := S0_natM _ _ _
  rw [e] at h1
  have : (1 : Nat) = 2 := h1
  omega

-- `Std.Slice.foldlM_toArray` (`[LawfulMonad m]`): as for `foldlM_toList`.
example : ¬ ∀ {γ : Type} {α β : Type} {m : Type → Type} {δ : Type} [inst : Monad m]
    [inst_1 : ToIterator (Slice γ) Id α β] [inst_2 : Iterator α Id β] [inst_3 : IteratorLoop α Id m]
    [LawfulIteratorLoop α Id m] [Finite α Id] {s : Slice γ} {init : δ} {f : δ → β → m δ},
    Array.foldlM f init s.toArray = Slice.foldlM f init s := by
  intro H
  have h1 := @H _ _ _ NatM Nat _ _ _ _ _ _ S0 0 (fun _ _ => (0 : Nat))
  rw [S0_toArray] at h1
  have e : Slice.foldlM (m := NatM) (fun _ _ => (0 : Nat)) 0 S0 = _ := S0_natM _ _ _
  rw [e] at h1
  have : (1 : Nat) = 2 := h1
  omega

-- `Std.Slice.forIn_toList` (`[LawfulMonad m]`): `m = NatM`, `S0`, `f _ _ = pure 0`: the list loop
-- over `[0]` is 1, the iterator loop 2.
example : ¬ ∀ {α : Type} {γ : Type} {β : Type} {m : Type → Type} [inst : Monad m] {δ : Type}
    [inst_2 : ToIterator (Slice γ) Id α β] [inst_3 : Iterator α Id β]
    [inst_4 : IteratorLoop α Id m] [LawfulIteratorLoop α Id m] [Finite α Id] {s : Slice γ}
    {init : δ} {f : β → δ → m (ForInStep δ)}, forIn s.toList init f = forIn s init f := by
  intro H
  have h1 := @H _ _ _ NatM _ Nat _ _ _ _ _ S0 0 (fun _ _ => (0 : Nat))
  rw [S0_toList] at h1
  have e : forIn (m := NatM) S0 0 (fun _ _ => (0 : Nat)) = _ := S0_natM _ _ _
  rw [e] at h1
  have : (1 : Nat) = 2 := h1
  omega

-- `Std.Slice.forIn_toArray` (`[LawfulMonad m]`): as for `forIn_toList`.
example : ¬ ∀ {α : Type} {γ : Type} {β : Type} {m : Type → Type} [inst : Monad m] {δ : Type}
    [inst_2 : ToIterator (Slice γ) Id α β] [inst_3 : Iterator α Id β]
    [inst_4 : IteratorLoop α Id m] [LawfulIteratorLoop α Id m] [Finite α Id] {s : Slice γ}
    {init : δ} {f : β → δ → m (ForInStep δ)}, forIn s.toArray init f = forIn s init f := by
  intro H
  have h1 := @H _ _ _ NatM _ Nat _ _ _ _ _ S0 0 (fun _ _ => (0 : Nat))
  rw [S0_toArray] at h1
  have e : forIn (m := NatM) S0 0 (fun _ _ => (0 : Nat)) = _ := S0_natM _ _ _
  rw [e] at h1
  have : (1 : Nat) = 2 := h1
  omega

-- `Subarray.foldlM_toList` (`[LawfulMonad m]`): `m = NatM`, `S0`, `f _ _ = pure 0`: 1 vs 2.
example : ¬ ∀ {a : Type} {init : a} {m : Type → Type} [inst : Monad m] {α : Type}
    {s : Subarray α} {f : a → α → m a}, List.foldlM f init (Slice.toList s) = Slice.foldlM f init s := by
  intro H
  have h1 := @H Nat 0 NatM _ Nat S0 (fun _ _ => (0 : Nat))
  rw [S0_toList] at h1
  have e : Slice.foldlM (m := NatM) (fun _ _ => (0 : Nat)) 0 S0 = _ := S0_natM _ _ _
  rw [e] at h1
  have : (1 : Nat) = 2 := h1
  omega

-- `Subarray.forIn_toList` (`[LawfulMonad m]`): `m = NatM`, `S0`, `f _ _ = pure 0`: 1 vs 2.
example : ¬ ∀ {α : Type} {s : Subarray α} {m : Type → Type} [inst : Monad m] {γ : Type}
    {init : γ} {f : α → γ → m (ForInStep γ)}, forIn (Slice.toList s) init f = forIn s init f := by
  intro H
  have h1 := @H Nat S0 NatM _ Nat 0 (fun _ _ => (0 : Nat))
  rw [S0_toList] at h1
  have e : forIn (m := NatM) S0 0 (fun _ _ => (0 : Nat)) = _ := S0_natM _ _ _
  rw [e] at h1
  have : (1 : Nat) = 2 := h1
  omega

-- `Subarray.forIn_toArray` (`[LawfulMonad m]`): `m = NatM`, `S0`, `f _ _ = pure 0`: 1 vs 2.
example : ¬ ∀ {α : Type} {s : Subarray α} {m : Type → Type} [inst : Monad m] {γ : Type}
    {init : γ} {f : α → γ → m (ForInStep γ)}, forIn (Slice.toArray s) init f = forIn s init f := by
  intro H
  have h1 := @H Nat S0 NatM _ Nat 0 (fun _ _ => (0 : Nat))
  rw [S0_toArray] at h1
  have e : forIn (m := NatM) S0 0 (fun _ _ => (0 : Nat)) = _ := S0_natM _ _ _
  rw [e] at h1
  have : (1 : Nat) = 2 := h1
  omega

-- `Subarray.forIn_eq_forIn_toList` (`[LawfulMonad m]`): `m = NatM`, `S0`, `f _ _ = pure 0`: 2 vs 1.
example : ¬ ∀ {α : Type} {s : Subarray α} {m : Type → Type} [inst : Monad m] {γ : Type}
    {init : γ} {f : α → γ → m (ForInStep γ)}, forIn s init f = forIn (Slice.toList s) init f := by
  intro H
  have h1 := @H Nat S0 NatM _ Nat 0 (fun _ _ => (0 : Nat))
  rw [S0_toList] at h1
  have e : forIn (m := NatM) S0 0 (fun _ _ => (0 : Nat)) = _ := S0_natM _ _ _
  rw [e] at h1
  have : (2 : Nat) = 1 := h1
  omega

/-! ## `[Finite α Id]` with a free lawful `IteratorLoop`: `CI` (all necessary) -/

-- `Std.Slice.foldl_toArray` (`[Finite α Id]`): `CI` with `ciLoopL`, `f = (· + 1)`, `init = 0`:
-- the array fold is `n` (the opaque `toArray` size), the loop `n + 1`.
example : ¬ ∀ {γ : Type} {α β : Type} {δ : Type} [inst : ToIterator (Slice γ) Id α β]
    [inst_1 : Iterator α Id β] [inst_2 : IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    {s : Slice γ} {init : δ} {f : δ → β → δ}, Array.foldl f init s.toArray = Slice.foldl f init s := by
  intro H
  letI : IteratorLoop CI Id Id := ciLoopL
  have h1 := @H Unit CI Nat Nat ciToIter ciIter ciLoopL ciLoopL_lawful s0 0 (fun a _ => a + 1)
  have e : Slice.foldl (fun a _ => a + 1) 0 s0 =
      ((Slice.toArray s0).toList ++ [0]).foldl (fun c _ => c + 1) 0 :=
    ciL_neg _ _ _ _ _ (ci_not_wf _ 0 trivial)
  rw [e, ← Array.foldl_toList, foldl_succ, foldl_succ] at h1
  simp at h1

-- `Std.Slice.foldl_toList` (`[Finite α Id]`): as for `foldl_toArray`.
example : ¬ ∀ {γ : Type} {α β : Type} {δ : Type} [inst : ToIterator (Slice γ) Id α β]
    [inst_1 : Iterator α Id β] [inst_2 : IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    {s : Slice γ} {init : δ} {f : δ → β → δ}, List.foldl f init s.toList = Slice.foldl f init s := by
  intro H
  letI : IteratorLoop CI Id Id := ciLoopL
  have h1 := @H Unit CI Nat Nat ciToIter ciIter ciLoopL ciLoopL_lawful s0 0 (fun a _ => a + 1)
  have e : Slice.foldl (fun a _ => a + 1) 0 s0 =
      ((Slice.toList s0) ++ [0]).foldl (fun c _ => c + 1) 0 :=
    ciL_neg _ _ _ _ _ (ci_not_wf _ 0 trivial)
  rw [e, foldl_succ, foldl_succ] at h1
  simp at h1

-- `Std.Slice.foldlM_toList` (`[Finite α Id]`): `m = Id`, otherwise as for `foldl_toArray`.
example : ¬ ∀ {γ : Type} {α β : Type} {m : Type → Type} {δ : Type} [inst : Monad m]
    [inst_1 : ToIterator (Slice γ) Id α β] [inst_2 : Iterator α Id β] [inst_3 : IteratorLoop α Id m]
    [LawfulIteratorLoop α Id m] [LawfulMonad m] {s : Slice γ} {init : δ} {f : δ → β → m δ},
    List.foldlM f init s.toList = Slice.foldlM f init s := by
  intro H
  letI : IteratorLoop CI Id Id := ciLoopL
  have h1 := @H Unit CI Nat Id Nat _ ciToIter ciIter ciLoopL ciLoopL_lawful _ s0 0
    (fun a _ => pure (a + 1))
  have e : Slice.foldlM (m := Id) (fun a _ => pure (a + 1)) 0 s0 =
      (pure (((Slice.toList s0) ++ [0]).foldl (fun (c : Nat) _ => c + 1) 0) : Id Nat) :=
    ciL_neg _ _ _ _ _ (ci_not_wf _ 0 trivial)
  have e2 : List.foldlM (m := Id) (fun a _ => pure (a + 1)) 0 (Slice.toList s0) =
      (pure ((Slice.toList s0).foldl (fun (c : Nat) _ => c + 1) 0) : Id Nat) := by simp
  rw [e, e2] at h1
  have h2 : (Slice.toList s0).foldl (fun (c : Nat) _ => c + 1) 0 =
      ((Slice.toList s0) ++ [0]).foldl (fun (c : Nat) _ => c + 1) 0 := h1
  rw [foldl_succ, foldl_succ] at h2
  simp at h2

-- `Std.Slice.foldlM_toArray` (`[Finite α Id]`): as for `foldlM_toList`.
example : ¬ ∀ {γ : Type} {α β : Type} {m : Type → Type} {δ : Type} [inst : Monad m]
    [inst_1 : ToIterator (Slice γ) Id α β] [inst_2 : Iterator α Id β] [inst_3 : IteratorLoop α Id m]
    [LawfulIteratorLoop α Id m] [LawfulMonad m] {s : Slice γ} {init : δ} {f : δ → β → m δ},
    Array.foldlM f init s.toArray = Slice.foldlM f init s := by
  intro H
  letI : IteratorLoop CI Id Id := ciLoopL
  have h1 := @H Unit CI Nat Id Nat _ ciToIter ciIter ciLoopL ciLoopL_lawful _ s0 0
    (fun a _ => pure (a + 1))
  have e : Slice.foldlM (m := Id) (fun a _ => pure (a + 1)) 0 s0 =
      (pure (((Slice.toArray s0).toList ++ [0]).foldl (fun (c : Nat) _ => c + 1) 0) : Id Nat) :=
    ciL_neg _ _ _ _ _ (ci_not_wf _ 0 trivial)
  have e2 : Array.foldlM (m := Id) (fun a _ => pure (a + 1)) 0 (Slice.toArray s0) =
      (pure ((Slice.toArray s0).toList.foldl (fun (c : Nat) _ => c + 1) 0) : Id Nat) := by
    rw [← Array.foldlM_toList]; simp
  rw [e, e2] at h1
  have h2 : (Slice.toArray s0).toList.foldl (fun (c : Nat) _ => c + 1) 0 =
      ((Slice.toArray s0).toList ++ [0]).foldl (fun (c : Nat) _ => c + 1) 0 := h1
  rw [foldl_succ, foldl_succ] at h2
  simp at h2

-- `Std.Slice.forIn_toList` (`[Finite α Id]`): `m = Id`, `CI` with `ciLoopL`,
-- `f _ acc = yield (acc + 1)`, `init = 0`: `n` vs `n + 1`.
example : ¬ ∀ {α : Type} {γ : Type} {β : Type} {m : Type → Type} [inst : Monad m]
    [LawfulMonad m] {δ : Type} [inst_2 : ToIterator (Slice γ) Id α β] [inst_3 : Iterator α Id β]
    [inst_4 : IteratorLoop α Id m] [LawfulIteratorLoop α Id m] {s : Slice γ} {init : δ}
    {f : β → δ → m (ForInStep δ)}, forIn s.toList init f = forIn s init f := by
  intro H
  letI : IteratorLoop CI Id Id := ciLoopL
  have h1 := @H CI Unit Nat Id _ _ Nat ciToIter ciIter ciLoopL ciLoopL_lawful s0 0
    (fun _ acc => pure (.yield (acc + 1)))
  have e : forIn (m := Id) s0 0 (fun _ acc => pure (.yield (acc + 1))) =
      (pure (((Slice.toList s0) ++ [0]).foldl (fun (c : Nat) _ => c + 1) 0) : Id Nat) :=
    ciL_neg _ _ _ _ _ (ci_not_wf _ 0 trivial)
  have e2 : forIn (m := Id) (Slice.toList s0) 0 (fun _ acc => pure (.yield (acc + 1))) =
      (pure ((Slice.toList s0).foldl (fun (c : Nat) _ => c + 1) 0) : Id Nat) := by simp
  rw [e, e2] at h1
  have h2 : (Slice.toList s0).foldl (fun (c : Nat) _ => c + 1) 0 =
      ((Slice.toList s0) ++ [0]).foldl (fun (c : Nat) _ => c + 1) 0 := h1
  rw [foldl_succ, foldl_succ] at h2
  simp at h2

-- `Std.Slice.forIn_toArray` (`[Finite α Id]`): as for `forIn_toList`.
example : ¬ ∀ {α : Type} {γ : Type} {β : Type} {m : Type → Type} [inst : Monad m]
    [LawfulMonad m] {δ : Type} [inst_2 : ToIterator (Slice γ) Id α β] [inst_3 : Iterator α Id β]
    [inst_4 : IteratorLoop α Id m] [LawfulIteratorLoop α Id m] {s : Slice γ} {init : δ}
    {f : β → δ → m (ForInStep δ)}, forIn s.toArray init f = forIn s init f := by
  intro H
  letI : IteratorLoop CI Id Id := ciLoopL
  have h1 := @H CI Unit Nat Id _ _ Nat ciToIter ciIter ciLoopL ciLoopL_lawful s0 0
    (fun _ acc => pure (.yield (acc + 1)))
  have e : forIn (m := Id) s0 0 (fun _ acc => pure (.yield (acc + 1))) =
      (pure (((Slice.toArray s0).toList ++ [0]).foldl (fun (c : Nat) _ => c + 1) 0) : Id Nat) :=
    ciL_neg _ _ _ _ _ (ci_not_wf _ 0 trivial)
  have e2 : forIn (m := Id) (Slice.toArray s0) 0 (fun _ acc => pure (.yield (acc + 1))) =
      (pure ((Slice.toArray s0).foldl (fun (c : Nat) _ => c + 1) 0) : Id Nat) := by simp
  rw [e, e2] at h1
  have h2 : (Slice.toArray s0).foldl (fun (c : Nat) _ => c + 1) 0 =
      ((Slice.toArray s0).toList ++ [0]).foldl (fun (c : Nat) _ => c + 1) 0 := h1
  rw [← Array.foldl_toList, foldl_succ, foldl_succ] at h2
  simp at h2

-- `Std.Slice.Internal.size_eq_length_iter` (`[Finite α Id]`): `CI` with `ciLoopD` and the lawful
-- `ciSize` (the default loop's `length`, `n`); `ciLoopD`'s `length` is `n + 1`.
example : ¬ ∀ {γ : Type} {α β : Type} [inst : ToIterator (Slice γ) Id α β]
    [inst_1 : Iterator α Id β] [inst_3 : IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    {s : Slice γ} [inst_5 : Std.Slice.SliceSize γ] [Std.Slice.LawfulSliceSize γ],
    s.size = (Std.Slice.Internal.iter s).length := by
  intro H
  have h1 := @H Unit CI Nat ciToIter ciIter ciLoopD ciLoopD_lawful s0 ciSize ciSize_lawful
  have e : @Iter.length CI Nat ciIter ciLoopD (Std.Slice.Internal.iter s0) =
      @Iter.length CI Nat ciIter IteratorLoop.defaultImplementation (ToIterator.iter s0) + 1 :=
    congrArg ULift.down (ciD_neg _ _ _ _ _ (ci_not_wf _ (ULift.up 0) trivial))
  rw [e] at h1
  exact absurd h1 (Nat.ne_of_lt (Nat.lt_succ_self _))

/-! ## Other necessary ones -/

-- `Array.toSubarray_eq_toSubarray_of_min_eq_min` (`h`): `xs = #[0]`, `start = 0`, `stop = 0`,
-- `stop' = 1`: the subarrays end at 0 and 1.
example : ¬ ∀ {α : Type} {xs : Array α} {start stop stop' : Nat},
    xs.toSubarray start stop = xs.toSubarray start stop' := fun H =>
  absurd (congrArg Subarray.stop (@H Nat #[0] 0 0 1)) (by decide)

-- `Std.Slice.Self.eq` (`self`): `Unit ≠ Empty`.
example : ¬ ∀ {α : Type} {β : Type}, α = β := fun H =>
  nomatch (cast (@H Unit Empty) ())

/-! ## Removable -/

-- `Std.Slice.length_toListRev_eq_size` (`[LawfulIteratorLoop α Id Id]`): the statement does not
-- mention the `IteratorLoop` instance, so apply the theorem with the default one, which is lawful
-- for finite iterators.
example : ∀ {γ : Type u} {α β : Type v} [inst : ToIterator (Slice γ) Id α β]
    [inst_1 : Iterator α Id β] {s : Slice γ} [inst_2 : IteratorLoop α Id Id.{v}]
    [inst_3 : Std.Slice.SliceSize γ] [Std.Slice.LawfulSliceSize γ] [Finite α Id],
    s.toListRev.length = s.size := fun {γ α β} _ _ {s} _ _ _ _ =>
  @Std.Slice.length_toListRev_eq_size γ α β _ _ s IteratorLoop.defaultImplementation _ _ _
    (instLawfulIteratorLoopDefaultImplementation α Id Id)

/-!
## Unresolved (3)

`Std.Slice.size_toArray_eq_size`, `Std.Slice.length_toList_eq_size` and
`Std.Slice.length_toListRev_eq_size`, hypothesis `[Finite α Id]`: both sides are computed with
`WellFounded.extrinsicFix₂`/`₃`, which for a non-finite iterator type (the relation of plausible
successors is not well-founded) is the `partial def` `opaqueFix₂`/`opaqueFix₃`, an opaque constant.
`toArray`/`toList`/`toListRev` use `opaqueFix₂` and the size (pinned by `LawfulSliceSize` to the
default loop's `length`) uses `opaqueFix₃`; no instance in these statements can be chosen freely to
relate them (unlike the free `IteratorLoop` above). So `T'` restricted to finite types is `T`, and
on non-finite types it equates values of two unrelated opaque constants: neither `T'` nor `¬T'`
appears provable.
-/
