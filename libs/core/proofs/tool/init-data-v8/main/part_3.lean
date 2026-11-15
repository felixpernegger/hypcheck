import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Array.foldrM_congr, hypothesis 14: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldrM_congr.h14 : ¬∀ {α β : Type} {start start' stop stop' : Nat} {m : Type → Type} [inst : Monad m] {f g : α → β → m β} {b : β}
        {xs xs' : Array α},
        xs = xs' → start = start' → stop = stop' → Array.foldrM f b xs start stop = Array.foldrM g b xs' start' stop' := fun hc_h => absurd (@hc_h (Nat) (Nat) (1) (1) (0) (0) (Option : Type → Type) (instMonadOption) (fun (a x : Nat) => Option.none) (fun (a : Nat) => Option.some) (0) (#[0]) (#[0]) rfl rfl rfl) (by
  decide)

-- Array.foldrM_congr, hypothesis 16: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldrM_congr.h16 : ¬∀ {α β : Type} {start start' stop stop' : Nat} {m : Type → Type} [inst : Monad m] {f g : α → β → m β} {b : β}
        {xs xs' : Array α},
        xs = xs' →
          (∀ (x : α) (y : β), f x y = g x y) →
            start = start' → Array.foldrM f b xs start stop = Array.foldrM g b xs' start' stop' := fun hc_h => absurd (@hc_h (Nat) (Nat) (1) (1) (0) (1) (Option : Type → Type) (instMonadOption) (fun (a x : Nat) => Option.none) (fun (a x : Nat) => Option.none) (0) (#[0]) (#[0]) rfl (by
  simp) rfl) (by
  decide)

-- List.le_minIdxOn_of_apply_getElem_lt_apply_getElem, hypothesis 6: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.List.le_minIdxOn_of_apply_getElem_lt_apply_getElem.h6.inst : ¬∀ (h : [0, 1] ≠ []) (hi : 1 < [0, 1].length),
        (∀ (j : Nat) (x : j < 1), (fun (x : Nat) => 0) [0, 1][1] ≤ (fun (x : Nat) => 0) [0, 1][j]) →
          1 ≤ List.minIdxOn (fun (x : Nat) => 0) [0, 1] h := by
  decide
theorem HypCheckProof.List.le_minIdxOn_of_apply_getElem_lt_apply_getElem.h6 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : LT β] [inst_3 : Std.IsLinearPreorder β] {f : α → β}
        {xs : List α} (h : xs ≠ []) {i : Nat} (hi : i < xs.length),
        (∀ (j : Nat) (x : j < i), f xs[i] < f xs[j]) → i ≤ List.minIdxOn f xs h := fun hc_h => HypCheckProof.List.le_minIdxOn_of_apply_getElem_lt_apply_getElem.h6.inst (fun hc_k0 hc_k1 hc_k2 => @hc_h (Nat) (Nat) (instLENat) (Nat.decLe) ({ lt := fun (a b : Nat) => a ≤ b : LT Nat }) _ (fun (x : Nat) => 0) ([0, 1]) hc_k0 (1) hc_k1 hc_k2)

-- Array.filterMapM_subtype, hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.filterMapM_subtype.h10 : ¬∀ {m : Type → Type} {α β : Type} {stop : Nat} [inst : Monad m] [inst_1 : LawfulMonad m] {p : α → Prop}
        {xs : Array { x : α // p x }} {f : { x : α // p x } → m (Option β)} {g : α → m (Option β)},
        stop = xs.size → Array.filterMapM f xs 0 stop = Array.filterMapM g xs.unattach := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })].size) (instMonadOption) _ (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Option.none) (fun (a : Nat) => Option.some Option.none) rfl) (by
  decide +kernel)

-- Array.filterMapM_subtype, hypothesis 11: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.filterMapM_subtype.h11 : ¬∀ {m : Type → Type} {α β : Type} {stop : Nat} [inst : Monad m] [inst_1 : LawfulMonad m] {p : α → Prop}
        {xs : Array { x : α // p x }} {f : { x : α // p x } → m (Option β)} {g : α → m (Option β)},
        (∀ (x : α) (h : p x), f (⟨x, h⟩ : { x : α // p x }) = g x) →
          Array.filterMapM f xs 0 stop = Array.filterMapM g xs.unattach := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (0) (instMonadOption) _ (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Option.none) (fun (a : Nat) => Option.none) (by
  simp)) (by
  decide +kernel)

-- Vector.map_lt_map_iff, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.map_lt_map_iff.h6 : ¬∀ {α β : Type} {n : Nat} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
        (f : α → β), (∀ (a b : α), a < b → f a < f b) → ∀ {xs ys : Vector α n}, Vector.map f xs < Vector.map f ys ↔ xs < ys := fun hc_h => absurd (@hc_h (Nat) (Nat) (1) (instLTNat) _ (⟨fun a b => a ≤ b⟩ : LT Nat) (fun n => n + 1 : Nat → Nat) (by
  grind) (#v[0]) (#v[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    simp <;> decide))

-- List.map_le_map_iff, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.map_le_map_iff.h5 : ¬∀ {α β : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β] (f : α → β),
        (∀ (a b : α), a < b → f a < f b) → ∀ {l₁ l₂ : List α}, List.map f l₁ ≤ List.map f l₂ ↔ l₁ ≤ l₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLTNat) _ (⟨fun a b => a ≤ b⟩ : LT Nat) (fun n => n + 1 : Nat → Nat) (by
  grind) ([0]) ([0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.apply_maxOn_le_apply_maxOn_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.apply_maxOn_le_apply_maxOn_of_subset.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs ys : List α} {f : α → β} (hxs : ys ⊆ xs) (hys : ys ≠ []),
        f (List.maxOn f ys hys) ≤
          f
            (List.maxOn f xs
              ((fun {α : Type} {xs ys : List α} (hxs : ys ⊆ xs) (hys : ys ≠ []) (h : xs = []) =>
                  False.elim
                    (Eq.mp (Eq.trans List.subset_nil._simp_1 (eq_false hys))
                      (Eq.mp (congrArg (fun (_a : List α) => ys ⊆ _a) h) hxs)))
                hxs hys)) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) ([0]) ([0]) (fun n => n % 2 == 0 : Nat → Bool) hc_k0 hc_k1) (by
  decide)

-- Array.map_lt_map_iff, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.map_lt_map_iff.h5 : ¬∀ {α β : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β] (f : α → β),
        (∀ (a b : α), a < b → f a < f b) → ∀ {xs ys : Array α}, Array.map f xs < Array.map f ys ↔ xs < ys := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLTNat) _ (⟨fun a b => a ≤ b⟩ : LT Nat) (fun n => n + 1 : Nat → Nat) (by
  grind) (#[0]) (#[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    simp <;> decide))

-- Array.map_lt_map_iff, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.map_lt_map_iff.h7 : ¬∀ {α β : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
        [inst_3 : Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → β) {xs ys : Array α},
        Array.map f xs < Array.map f ys ↔ xs < ys := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (instLTNat) _ (fun n => n + 1 : Nat → Nat) (#[0]) (#[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    simp <;> decide))

-- Array.le_max_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.le_max_of_mem.h3 : ¬∀ {α : Type} [inst : Max α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderMax α] {xs : Array α} {a : α} (ha : a ∈ xs),
        a ≤ xs.max (Array.ne_empty_of_mem ha) := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Bool.instMax) (⟨fun _ _ => False⟩ : LE Bool) (@Std.LawfulOrderMax.mk (Bool) (Bool.instMax) (@LE.mk Bool fun (x x_1 : Bool) => False) (@Std.MaxEqOr.mk (Bool) (Bool.instMax) (by (try dsimp only);   decide)) (@Std.LawfulOrderSup.mk (Bool) (Bool.instMax) (@LE.mk Bool fun (x x_1 : Bool) => False) (by (try dsimp only);   decide))) (#[Bool.false]) (Bool.false) hc_k0) (by
  decide +kernel)

-- Array.le_max_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.le_max_of_mem.h4 : ¬∀ {α : Type} [inst : Max α] [inst_1 : LE α] [inst_2 : Std.IsLinearOrder α] {xs : Array α} {a : α} (ha : a ∈ xs),
        a ≤ xs.max (Array.ne_empty_of_mem ha) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (⟨fun a b => a - b⟩ : Max Nat) (instLENat) _ (#[0, 1]) (1) hc_k0) (by
  decide +kernel)

-- List.apply_minOn_le_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.apply_minOn_le_of_mem.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs : List α} {f : α → β} {y : α} (hx : y ∈ xs),
        f (List.minOn f xs (List.ne_nil_of_mem hx)) ≤ f y := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) ([0]) (fun n => n % 2 == 0 : Nat → Bool) (0) hc_k0) (by
  decide)

-- Array.le_iff_lt_or_eq, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.le_iff_lt_or_eq.h4 : ¬∀ {α : Type} [inst : LT α] [inst_1 : Std.Irrefl fun (x1 x2 : α) => x1 < x2]
        [inst_2 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {xs ys : Array α}, xs ≤ ys ↔ xs < ys ∨ xs = ys := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≠ b⟩ : LT Nat) (@Std.Irrefl.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @Ne Nat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @Ne Nat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (#[0]) (#[1])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @Ne Nat a b)) := fun (a b : Nat) =>
      @instDecidableNot (@Eq Nat a b) (instDecidableEqNat a b);
    decide))

-- Std.Rxo.LawfulHasSize.size_eq_zero_of_not_le, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.Rxo.LawfulHasSize.size_eq_zero_of_not_le.h7 : ¬∀ {α : Type} {inst : LT α} {inst_1 : Std.PRange.UpwardEnumerable α} {inst_2 : Std.Rxo.HasSize α}
        [self : Std.Rxo.LawfulHasSize α] (lo hi : α), Std.Rxo.HasSize.size lo hi = 0 := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) ({ succ? := fun n => some (n + 1), succMany? := fun k n => some (n + k + 1) } : Std.PRange.UpwardEnumerable Nat) (⟨fun lo hi => hi + 1 - lo⟩ : Std.Rxo.HasSize Nat) (@Std.Rxo.LawfulHasSize.mk (Nat) (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) (@Std.PRange.UpwardEnumerable.mk Nat
      (fun (n : Nat) =>
        @Option.some Nat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      fun (k n : Nat) =>
      @Option.some Nat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n k)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Std.Rxo.HasSize.mk Nat fun (lo hi : Nat) =>
      @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) hi (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) lo) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all <;> omega))) (0) (0)) (by
  decide)

-- List.append_right_le_iff_of_length_eq, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.append_right_le_iff_of_length_eq.h2 : ¬∀ {α : Type} [inst : LT α] {l₁ l₂ : List α} (l₃ : List α), l₁.length = l₂.length → (l₁ ++ l₃ ≤ l₂ ++ l₃ ↔ l₁ ≤ l₂) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) ([]) ([]) ([0]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.append_right_lt_iff_of_length_eq, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.append_right_lt_iff_of_length_eq.h2 : ¬∀ {α : Type} [inst : LT α] {l₁ l₂ : List α} (l₃ : List α), l₁.length = l₂.length → (l₁ ++ l₃ < l₂ ++ l₃ ↔ l₁ < l₂) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) ([]) ([]) ([0]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.min?_eq_some_iff, hypothesis 5: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Array.min?_eq_some_iff.h5.inst : ¬(#[Bool.false].min? = Option.some Bool.false ↔ Bool.false ∈ #[Bool.false] ∧ ∀ (b : Bool), b ∈ #[Bool.false] → False) := by
  decide +kernel
theorem HypCheckProof.Array.min?_eq_some_iff.h5 : ¬∀ {α : Type} {a : α} [inst : Min α] [inst_1 : LE α] {xs : Array α} [inst_2 : Std.LawfulOrderMin α],
        xs.min? = Option.some a ↔ a ∈ xs ∧ ∀ (b : α), b ∈ xs → a ≤ b := fun hc_h => HypCheckProof.Array.min?_eq_some_iff.h5.inst (@hc_h (Bool) (Bool.false) (Bool.instMin) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (#[Bool.false]) (@Std.LawfulOrderMin.mk (Bool) (Bool.instMin) (@LE.mk Bool fun (x x_1 : Bool) => False) (@Std.MinEqOr.mk (Bool) (Bool.instMin) (by (try dsimp only);   decide)) (@Std.LawfulOrderInf.mk (Bool) (Bool.instMin) (@LE.mk Bool fun (x x_1 : Bool) => False) (by (try dsimp only);   decide))))

-- Array.min?_eq_some_iff, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.min?_eq_some_iff.h6 : ¬∀ {α : Type} {a : α} [inst : Min α] [inst_1 : LE α] {xs : Array α} [inst_2 : Std.IsLinearOrder α],
        xs.min? = Option.some a ↔ a ∈ xs ∧ ∀ (b : α), b ∈ xs → a ≤ b := fun hc_h => absurd (@hc_h (Nat) (0) (⟨fun a b => a - b⟩ : Min Nat) (instLENat) (#[1, 0]) _) (by
  decide +kernel)

-- Vector.foldr_subtype, hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.foldr_subtype.h8 : ¬∀ {α : Type} {n : Nat} {β : Type} {p : α → Prop} {xs : Vector { x : α // p x } n} {f : { x : α // p x } → β → β}
        {g : α → β → β} {x : β}, Vector.foldr f x xs = Vector.foldr g x xs.unattach := fun hc_h => absurd (@hc_h (Nat) (1) (Nat) (fun n => n = 0 : Nat → Prop) (#v[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) (n : Nat) => n + 1) (fun a b => a - b : Nat → Nat → Nat) (0)) (by
  decide +kernel)

-- ISize.lt_of_lt_of_le, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ISize.lt_of_lt_of_le.h3 : ¬∀ {a b c : ISize}, b ≤ c → a < c := fun hc_h => absurd (@hc_h (ISize.ofInt 0) (ISize.ofInt 0) (ISize.ofInt 0) (by
  simp)) (by
  simp)

-- Membership.get_elem_helper, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Membership.get_elem_helper.h3 : ¬∀ {i n : Nat} {r : Std.Legacy.Range}, r.stop = n → i < n := fun hc_h => absurd (@hc_h (0) ([:0].stop) ([:0]) rfl) (by
  decide)

-- Vector.append_left_le_iff, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.append_left_le_iff.h4 : ¬∀ {α : Type} {n m : Nat} [inst : LT α] (xs : Vector α n) {ys ys' : Vector α m}, xs ++ ys ≤ xs ++ ys' ↔ ys ≤ ys' := fun hc_h => absurd (@hc_h (Nat) (1) (0) (⟨fun a b => a ≤ b⟩ : LT Nat) (#v[0]) (#v[]) (#v[])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Option.merge_lt_iff, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.merge_lt_iff.h6 : ¬∀ {α : Type} [inst : LT α] {f : α → α → α} {o₁ o₂ o₃ : Option α}, Option.merge f o₁ o₂ < o₃ ↔ o₁ < o₃ ∧ o₂ < o₃ := fun hc_h => absurd (@hc_h (Nat) (instLTNat) (fun a b => a - b : Nat → Nat → Nat) (Option.some 0) (Option.some 1) (Option.some 1)) (by
  simp)

-- Array.flatMap_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.flatMap_subtype.h6 : ¬∀ {α β : Type} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → Array β} {g : α → Array β},
        Array.flatMap f xs = Array.flatMap g xs.unattach := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => #[]) (fun n => #[n] : Nat → Array Nat)) (by
  decide +kernel)

-- List.flatMap_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.flatMap_subtype.h6 : ¬∀ {α β : Type} {p : α → Prop} {l : List { x : α // p x }} {f : { x : α // p x } → List β} {g : α → List β},
        List.flatMap f l = List.flatMap g l.unattach := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => []) (fun n => [n] : Nat → List Nat)) (by
  decide)

-- List.findSome?_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.findSome?_subtype.h6 : ¬∀ {α β : Type} {p : α → Prop} {l : List { x : α // p x }} {f : { x : α // p x } → Option β} {g : α → Option β},
        List.findSome? f l = List.findSome? g l.unattach := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Option.none) (some : Nat → Option Nat)) (by
  decide)

-- Array.append_left_le_iff, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.append_left_le_iff.h2 : ¬∀ {α : Type} [inst : LT α] (xs : Array α) {ys zs : Array α}, xs ++ ys ≤ xs ++ zs ↔ ys ≤ zs := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (#[0]) (#[]) (#[])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.findIdx_subtype, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.findIdx_subtype.h5 : ¬∀ {α : Type} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        Array.findIdx f xs = Array.findIdx g xs.unattach := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- List.all_subtype, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.all_subtype.h5 : ¬∀ {α : Type} {p : α → Prop} {l : List { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        l.all f = l.unattach.all g := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide)

-- List.findIdx?_subtype, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.findIdx?_subtype.h5 : ¬∀ {α : Type} {p : α → Prop} {l : List { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        List.findIdx? f l = List.findIdx? g l.unattach := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide)

-- List.findIdx_subtype, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.findIdx_subtype.h5 : ¬∀ {α : Type} {p : α → Prop} {l : List { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        List.findIdx f l = List.findIdx g l.unattach := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide)

-- List.findFinIdx?_subtype, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.findFinIdx?_subtype.h5 : ¬∀ {α : Type} {p : α → Prop} {l : List { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        List.findFinIdx? f l =
          Option.map (fun (i : Fin l.unattach.length) => Fin.cast (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) i) (List.findFinIdx? g l.unattach) := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) ([(⟨0, (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide)

-- USize.ofNat_lt_iff_lt, hypothesis 3: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.ofNat_lt_iff_lt.h3.inst : ¬(USize.ofNat 0 < USize.ofNat 18446744073709551616 ↔ 0 < 18446744073709551616) := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.ofNat_lt_iff_lt.h3.prem0 : 0 < USize.size := by
  grind
theorem HypCheckProof.USize.ofNat_lt_iff_lt.h3 : ¬∀ {a b : Nat}, a < USize.size → (USize.ofNat a < USize.ofNat b ↔ a < b) := fun hc_h => HypCheckProof.USize.ofNat_lt_iff_lt.h3.inst (@hc_h (0) (18446744073709551616) HypCheckProof.USize.ofNat_lt_iff_lt.h3.prem0)

-- List.Perm.unattach, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.Perm.unattach.h4 : ¬∀ {α : Type} {p : α → Prop} {l₁ l₂ : List { x : α // p x }}, l₁.unattach.Perm l₂.unattach := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) ([]) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })])) (by
  decide)

-- List.MergeSort.Internal.splitInTwo_fst_pairwise, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.MergeSort.Internal.splitInTwo_fst_pairwise.h4 : ¬∀ {α : Type} {n : Nat} {le : α → α → Prop} (l : { l : List α // l.length = n }),
        List.Pairwise le (List.MergeSort.Internal.splitInTwo l).fst.val := fun hc_h => absurd (@hc_h (Nat) (3) (fun a b => a < b : Nat → Nat → Prop) ((⟨[2, 1, 0], of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { l : List Nat // l.length = 3 }))) (by
  decide)

-- List.le_total_of_asymm, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.le_total_of_asymm.h2 : ¬∀ {α : Type} [inst : LT α] (l₁ l₂ : List α), l₁ ≤ l₂ ∨ l₂ ≤ l₁ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) ([0]) ([0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.mem_attachWith, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.mem_attachWith.h3 : ¬∀ {α : Type} {l : List α} {q : α → Prop} (x : { x : α // q x }) (x : α), x ∈ l → q x := fun hc_h => absurd (@hc_h (Nat) ([1]) (fun n => n = 0 : Nat → Prop) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x }))) (by
  decide)

-- List.le_append_left, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.le_append_left.h2 : ¬∀ {α : Type} [inst : LT α] {l₁ l₂ : List α}, l₁ ≤ l₁ ++ l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) ([0]) ([])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Option.attachWith_eq_some_iff, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.attachWith_eq_some_iff.h3 : ¬∀ {α : Type} {p : α → Prop} {o : Option α} {x : { x : α // p x }} (a : α), o = Option.some a → p a := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (Option.some 1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x }))) (by
  decide)

-- USize.ofNatLT_add, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.ofNatLT_add.h2 : ¬∀ {a b : Nat}, a + b < 2 ^ System.Platform.numBits := fun hc_h => absurd (@hc_h (0) (18446744073709551616)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.toNat_mod_lt, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.toNat_mod_lt.h2 : ¬∀ {m : Nat} (u : USize), (u % USize.ofNat m).toNat < m := fun hc_h => absurd (@hc_h (0) (USize.ofNat 0)) (by
  decide)

