import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Array.foldr_congr, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldr_congr.h7 : ¬∀ {α β : Type} {as bs : Array α},
        as = bs →
          ∀ {f g : α → β → β} {a b : β},
            a = b →
              ∀ {start start' stop stop' : Nat},
                start = start' → stop = stop' → Array.foldr f a as start stop = Array.foldr g b bs start' stop' := fun hc_h => absurd (@hc_h (Nat) (Nat) (#[0]) (#[0]) rfl (fun a b => a - b : Nat → Nat → Nat) (fun a b => a + b : Nat → Nat → Nat) (1) (1) rfl (1) (1) (0) (0) rfl rfl) (by
  decide)

-- Array.foldr_congr, hypothesis 15: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldr_congr.h15 : ¬∀ {α β : Type} {as bs : Array α},
        as = bs →
          ∀ {f g : α → β → β},
            f = g →
              ∀ {a b : β},
                a = b →
                  ∀ {start start' stop stop' : Nat},
                    stop = stop' → Array.foldr f a as start stop = Array.foldr g b bs start' stop' := fun hc_h => absurd (@hc_h (Nat) (Nat) (#[0]) (#[0]) rfl (fun a b => a - b : Nat → Nat → Nat) (fun a b => a - b : Nat → Nat → Nat) rfl (1) (1) rfl (0) (1) (0) (0) rfl) (by
  decide)

-- Array.foldr_congr, hypothesis 16: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldr_congr.h16 : ¬∀ {α β : Type} {as bs : Array α},
        as = bs →
          ∀ {f g : α → β → β},
            f = g →
              ∀ {a b : β},
                a = b →
                  ∀ {start start' stop stop' : Nat},
                    start = start' → Array.foldr f a as start stop = Array.foldr g b bs start' stop' := fun hc_h => absurd (@hc_h (Nat) (Nat) (#[0]) (#[0]) rfl (fun a b => a - b : Nat → Nat → Nat) (fun a b => a - b : Nat → Nat → Nat) rfl (1) (1) rfl (1) (1) (0) (1) rfl) (by
  decide)

-- List.flatMap_lt_flatMap_iff, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.flatMap_lt_flatMap_iff.h7 : ¬∀ {α β : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
        [inst_3 : Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → List β),
        (∀ (a b : α), f a <+: f b → a = b) →
          (∀ (a : α), f a ≠ []) → ∀ {l₁ l₂ : List α}, List.flatMap f l₁ < List.flatMap f l₂ ↔ l₁ < l₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (instLTNat) _ (fun n => [n] : Nat → List Nat) (by
  simp) (by
  simp) ([0]) ([0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.foldrM_subtype, hypothesis 11: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldrM_subtype.h11 : ¬∀ {m : Type → Type} {α β : Type} {start : Nat} [inst : Monad m] [inst_1 : LawfulMonad m] {p : α → Prop}
        {xs : Array { x : α // p x }} {f : { x : α // p x } → β → m β} {g : α → β → m β} {x : β},
        start = xs.size → Array.foldrM f x xs start = Array.foldrM g x xs.unattach start := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })].size) (instMonadOption) _ (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) (x : Nat) => Option.none) (fun (a : Nat) => Option.some) (0) rfl) (by
  decide +kernel)

-- Std.Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none, hypothesis 8: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none.h8.inst : ¬1 + 1 - 0 = 1 := by
  decide
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none.h8.prem0 : 0 ≤ 1 := by
  decide
theorem HypCheckProof.Std.Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none.h8 : ¬∀ {α : Type} {inst : LT α} {inst_1 : Std.PRange.UpwardEnumerable α} {inst_2 : Std.Rxo.HasSize α}
        [self : Std.Rxo.LawfulHasSize α] (lo hi : α), lo < hi → Std.Rxo.HasSize.size lo hi = 1 := fun hc_h => HypCheckProof.Std.Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none.h8.inst (@hc_h (Nat) ({ lt := fun (a b : Nat) => a ≤ b : LT Nat }) ({ succ? := fun (n : Nat) => Option.some (n + 1), succMany? := fun (k n : Nat) => Option.some (n + k + 1) :
      Std.PRange.UpwardEnumerable Nat }) ({ size := fun (lo hi : Nat) => hi + 1 - lo : Std.Rxo.HasSize Nat }) (@Std.Rxo.LawfulHasSize.mk (Nat) (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) (@Std.PRange.UpwardEnumerable.mk Nat
      (fun (n : Nat) =>
        @Option.some Nat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      fun (k n : Nat) =>
      @Option.some Nat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n k)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Std.Rxo.HasSize.mk Nat fun (lo hi : Nat) =>
      @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) hi (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) lo) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all <;> omega))) (0) (1) HypCheckProof.Std.Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none.h8.prem0)

-- List.append_le_append_iff_of_length_eq, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.append_le_append_iff_of_length_eq.h2 : ¬∀ {α : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {l₁ l₂ l₃ l₄ : List α},
        l₁.length = l₂.length → (l₁ ++ l₃ ≤ l₂ ++ l₄ ↔ l₁ < l₂ ∨ l₁ = l₂ ∧ l₃ ≤ l₄) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) ([0]) ([0]) ([]) ([]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.flatMapM_subtype, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.flatMapM_subtype.h9 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] [inst_1 : LawfulMonad m] {p : α → Prop} {xs : Array { x : α // p x }}
        {f : { x : α // p x } → m (Array β)} {g : α → m (Array β)}, Array.flatMapM f xs = Array.flatMapM g xs.unattach := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (instMonadOption) _ (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Option.none) (fun (a : Nat) => Option.some #[])) (by
  decide +kernel)

-- Option.left_lt_of_merge_lt, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.left_lt_of_merge_lt.h3 : ¬∀ {α : Type} [inst : LT α] {f : α → α → α} {o₁ o₂ o₃ : Option α}, Option.merge f o₁ o₂ < o₃ → o₁ < o₃ := fun hc_h => absurd (@hc_h (Nat) (instLTNat) (fun a b => a - b : Nat → Nat → Nat) (Option.some 1) (Option.some 1) (Option.some 1) (by
  simp)) (by
  simp)

-- Option.left_le_max, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.left_le_max.h4 : ¬∀ {α : Type} [inst : LE α] [inst_1 : Max α], (∀ (x : α), x ≤ x) → ∀ {a b : Option α}, a ≤ Max.max a b := fun hc_h => absurd (@hc_h (Nat) (instLENat) (⟨fun a b => a - b⟩ : Max Nat) (by
  simp) (Option.some 1) (Option.some 1)) (by
  simp)

-- Vector.le_iff_lt_or_eq, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.le_iff_lt_or_eq.h3 : ¬∀ {α : Type} {n : Nat} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {xs ys : Vector α n},
        xs ≤ ys ↔ xs < ys ∨ xs = ys := fun hc_h => absurd (@hc_h (Nat) (1) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (#v[0]) (#v[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Vector.le_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.le_of_lt.h3 : ¬∀ {α : Type} {n : Nat} [inst : LT α] {xs ys : Vector α n}, xs < ys → xs ≤ ys := fun hc_h => absurd (@hc_h (Nat) (1) (⟨fun a b => a ≤ b⟩ : LT Nat) (#v[0]) (#v[0]) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.le_iff_exists, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.le_iff_exists.h2 : ¬∀ {α : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {l₁ l₂ : List α},
        l₁ ≤ l₂ ↔
          l₁ = List.take l₁.length l₂ ∨
            ∃ (i : Nat),
              ∃ (h₁ : i < l₁.length), ∃ (h₂ : i < l₂.length), (∀ (j : Nat) (hj : j < i), l₁[j] = l₂[j]) ∧ l₁[i] < l₂[i] := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) ([0]) ([0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Std.PRange.LawfulUpwardEnumerable.ne_of_lt, hypothesis 5: necessary
/- FAILED: 9:156: unexpected identifier; expected ')' | 11:156: unexpected identifier; expected ')' | 9:156: unexpected identifier; expected ')' | 11:156: unexpected identifier; expected ')' | 12:156: unexpected identifier; expected ')' | 22:156: unexpected identifier; expected ')' | 12:156: unexpected identifier; expected ')' | 22:156: unexpected identifier; expected ')'
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.PRange.LawfulUpwardEnumerable.ne_of_lt.h5 : ¬∀ {α : Type} {inst : Std.PRange.UpwardEnumerable α} [self : Std.PRange.LawfulUpwardEnumerable α] (a b : α), a ≠ b := fun hc_h => absurd (@hc_h (Nat) ({ succ? := fun n => some (n + 2), succMany? := fun k n => some (n + 2 * k) } : Std.PRange.UpwardEnumerable Nat) (@Std.PRange.LawfulUpwardEnumerable.mk (Nat) (@Std.PRange.UpwardEnumerable.mk Nat
      (fun (n : Nat) =>
        @Option.some Nat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      fun (k n : Nat) =>
      @Option.some Nat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))) (by (try dsimp only);   (intros;
    simp_all [Std.PRange.UpwardEnumerable.LT, Std.PRange.UpwardEnumerable.LE, Std.PRange.succMany?, Std.PRange.succ?] <;>
      omega)) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all <;> omega))) (0) (0)) (by
  decide)
-/

-- Std.PartialOrderPackage.le_antisymm, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.PartialOrderPackage.le_antisymm.h4 : ¬∀ {α : Type} [self : Std.PartialOrderPackage α] (a b : α), b ≤ a → a = b := fun hc_h => absurd (@hc_h (Int : Type) (Int.instLinearOrderPackage.toPartialOrderPackage) (1) (0) (by
  decide)) (by
  decide)

-- Std.PartialOrderPackage.le_antisymm, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.PartialOrderPackage.le_antisymm.h5 : ¬∀ {α : Type} [self : Std.PartialOrderPackage α] (a b : α), a ≤ b → a = b := fun hc_h => absurd (@hc_h (Int : Type) (Int.instLinearOrderPackage.toPartialOrderPackage) (0) (1) (by
  decide)) (by
  decide)

-- USize.lt_of_lt_of_le, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.lt_of_lt_of_le.h3 : ¬∀ {a b c : USize}, b ≤ c → a < c := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 0) (USize.ofNat 0) (by
  decide)) (by
  decide)

-- Array.foldl_subtype, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldl_subtype.h7 : ¬∀ {α β : Type} {p : α → Prop} {xs : Array { x : α // p x }} {f : β → { x : α // p x } → β} {g : β → α → β} {x : β},
        Array.foldl f x xs = Array.foldl g x xs.unattach := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : Nat) (a_1 : { x : Nat // (fun (n : Nat) => n = 0) x }) => 0) (fun a b => a - b : Nat → Nat → Nat) (1)) (by
  decide +kernel)

-- List.foldl_subtype, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.foldl_subtype.h7 : ¬∀ {α β : Type} {p : α → Prop} {l : List { x : α // p x }} {f : β → { x : α // p x } → β} {g : β → α → β} {x : β},
        List.foldl f x l = List.foldl g x l.unattach := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : Nat) (a_1 : { x : Nat // (fun (n : Nat) => n = 0) x }) => 0) (fun a b => a - b : Nat → Nat → Nat) (1)) (by
  decide)

-- apply_minOn_le_right, hypothesis 4: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.apply_minOn_le_right.h4.inst : ¬False := by
  decide
theorem HypCheckProof.apply_minOn_le_right.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {x y : α}, f (minOn f x y) ≤ f y := fun hc_h => HypCheckProof.apply_minOn_le_right.h4.inst (@hc_h (Bool) (Nat) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (fun (a b : Bool) => instDecidableFalse) (fun (n : Nat) => n % 2 == 0) (0) (0))

-- left_le_apply_maxOn, hypothesis 4: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.left_le_apply_maxOn.h4.inst : ¬False := by
  decide
theorem HypCheckProof.left_le_apply_maxOn.h4 : ¬∀ {β α : Type} [le : LE β] [inst : DecidableLE β] {f : α → β} {x y : α}, f x ≤ f (maxOn f x y) := fun hc_h => HypCheckProof.left_le_apply_maxOn.h4.inst (@hc_h (Bool) (Nat) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (fun (a b : Bool) => instDecidableFalse) (fun (n : Nat) => n % 2 == 0) (0) (0))

-- Vector.append_right_le_iff, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.append_right_le_iff.h4 : ¬∀ {α : Type} {n m : Nat} [inst : LT α] {xs₁ xs₂ : Vector α n} (ys : Vector α m), xs₁ ++ ys ≤ xs₂ ++ ys ↔ xs₁ ≤ xs₂ := fun hc_h => absurd (@hc_h (Nat) (0) (1) (⟨fun a b => a ≤ b⟩ : LT Nat) (#v[]) (#v[]) (#v[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Vector.append_right_lt_iff, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.append_right_lt_iff.h4 : ¬∀ {α : Type} {n m : Nat} [inst : LT α] {xs₁ xs₂ : Vector α n} (ys : Vector α m), xs₁ ++ ys < xs₂ ++ ys ↔ xs₁ < xs₂ := fun hc_h => absurd (@hc_h (Nat) (0) (1) (⟨fun a b => a ≤ b⟩ : LT Nat) (#v[]) (#v[]) (#v[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Option.le_min, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.le_min.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : Min α] {a b c : Option α}, a ≤ Min.min b c ↔ a ≤ b ∧ a ≤ c := fun hc_h => absurd (@hc_h (Nat) (instLENat) (⟨fun a b => a - b⟩ : Min Nat) (Option.some 1) (Option.some 1) (Option.some 0)) (by
  simp)

-- Array.append_left_lt_iff, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.append_left_lt_iff.h2 : ¬∀ {α : Type} [inst : LT α] (xs : Array α) {ys zs : Array α}, xs ++ ys < xs ++ zs ↔ ys < zs := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (#[0]) (#[]) (#[])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.count_attachWith, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.count_attachWith.h4 : ¬∀ {α : Type} [inst : BEq α] {p : α → Prop} {l : List α} {a : { x : α // p x }} (a : α), a ∈ l → p a := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) (fun n => n = 0 : Nat → Prop) ([1]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x }))) (by
  decide)

-- Option.min_le_left, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.min_le_left.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : Min α] {a b : Option α}, Min.min a b ≤ a := fun hc_h => absurd (@hc_h (Bool) (Bool.instLE) (⟨fun a b => !a && !b⟩ : Min Bool) (Option.some Bool.false) (Option.some Bool.false)) (by
  (simp <;> decide))

-- Array.count_attachWith, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.count_attachWith.h4 : ¬∀ {α : Type} [inst : BEq α] {p : α → Prop} {xs : Array α} {a : { x : α // p x }} (a : α), a ∈ xs → p a := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) (fun n => n = 0 : Nat → Prop) (#[1]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x }))) (by
  decide)

-- Vector.getElem_unattach, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.getElem_unattach.h5 : ¬∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Vector { x : α // p x } n} (i : Nat), i < n := fun hc_h => absurd (@hc_h (Nat) (0) (fun n => n = 0 : Nat → Prop) (#v[]) (0)) (by
  decide)

-- Array.find?_subtype, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.find?_subtype.h5 : ¬∀ {α : Type} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        Option.map Subtype.val (Array.find? f xs) = Array.find? g xs.unattach := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- Vector.mem_attachWith, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.mem_attachWith.h4 : ¬∀ {α : Type} {n : Nat} {xs : Vector α n} {q : α → Prop} (x : { x : α // q x }) (x : α), x ∈ xs → q x := fun hc_h => absurd (@hc_h (Nat) (1) (#v[1]) (fun n => n = 0 : Nat → Prop) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x }))) (by
  decide)

-- USize.ofNatLT_mod, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.ofNatLT_mod.h2 : ¬∀ {a b : Nat}, b < 2 ^ System.Platform.numBits → a < 2 ^ System.Platform.numBits := fun hc_h => absurd (@hc_h (18446744073709551616) (0) (by
  grind)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.ofNatLT_mod, hypothesis 3: necessary
/- FAILED: 3:2: Tactic `decide` failed to reduce
  @decide (0 < 2 ^ System.Platform.numBits) (Nat.decLt 0 (2 ^ System.Platform.numBits))
to `true` or `false`.

Reduction got stuck at
  (Nat.succ 0).ble (2 ^ System.Platform.numBits) | 10:2: Tactic `decide` failed to reduce
  @decide (0 < 2 ^ System.Platform.numBits) (Nat.decLt 0 (2 ^ System.Platform.numBits))
to `true` or `false`.

Reduction got stuck at
  (Nat.succ 0).ble (2 ^ System.Platform.numBits) | 3:2: Tactic `decide` failed to reduce
  @decide (0 < 2 ^ System.Platform.numBits) (Nat.decLt 0 (2 ^ System.Platform.numBits))
to `true` or `false`.

Reduction got stuck at
  (Nat.succ 0).ble (2 ^ System.Platform.numBits) | 10:2: Tactic `decide` failed to reduce
  @decide (0 < 2 ^ System.Platform.numBits) (Nat.decLt 0 (2 ^ System.Platform.numBits))
to `true` or `false`.

Reduction got stuck at
  (Nat.succ 0).ble (2 ^ System.Platform.numBits) | 14:2: Tactic `decide` failed to reduce
  @decide (0 < 2 ^ System.Platform.numBits) (Nat.decLt 0 (2 ^ System.Platform.numBits))
to `true` or `false`.

Reduction got stuck at
  (Nat.succ 0).ble (2 ^ System.Platform.numBits) | 19:2: Tactic `decide` failed to reduce
  @decide (0 < 2 ^ System.Platform.numBits) (Nat.decLt 0 (2 ^ System.Platform.numBits))
to `true` or `false`.

Reduction got stuck at
  (Nat.succ 0).ble (2 ^ System.Platform.numBits) | 14:2: Tactic `decide` failed to reduce
  @decide (0 < 2 ^ System.Platform.numBits) (Nat.decLt 0 (2 ^ System.Platform.numBits))
to `true` or `false`.

Reduction got stuck at
  (Nat.succ 0).ble (2 ^ System.Platform.numBits) | 19:2: Tactic `decide` failed to reduce
  @decide (0 < 2 ^ System.Platform.numBits) (Nat.decLt 0 (2 ^ System.Platform.numBits))
to `true` or `false`.

Reduction got stuck at
  (Nat.succ 0).ble (2 ^ System.Platform.numBits)
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.ofNatLT_mod.h3 : ¬∀ {a b : Nat}, a < 2 ^ System.Platform.numBits → b < 2 ^ System.Platform.numBits := fun hc_h => absurd (@hc_h (0) (18446744073709551616) (by
  decide +kernel)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))
-/

-- Option.unattach_guard, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.unattach_guard.h4 : ¬∀ {α : Type} {p : α → Prop} {q : { x : α // p x } → Bool} {r : α → Bool} {x : { x : α // p x }},
        (Option.guard q x).unattach = Option.guard r x.val := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x }))) (by
  decide)

-- Option.unattach_filter, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.unattach_filter.h5 : ¬∀ {α : Type} {p : α → Prop} {o : Option { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        (Option.filter f o).unattach = Option.filter g o.unattach := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (Option.some (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide)

-- USize.sub_lt, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.sub_lt.h2 : ¬∀ {a b : USize}, b ≤ a → a - b < a := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 0) (by
  decide)) (by
  decide)

-- USize.sub_lt, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.sub_lt.h3 : ¬∀ {a b : USize}, 0 < b → a - b < a := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 1) (by
  simp)) (by
  decide)

-- List.append_left_le_iff, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.append_left_le_iff.h2 : ¬∀ {α : Type} [inst : LT α] (l₁ : List α) {l₂ l₃ : List α}, l₁ ++ l₂ ≤ l₁ ++ l₃ ↔ l₂ ≤ l₃ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) ([0]) ([]) ([])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.uset_eq_set, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.uset_eq_set.h4 : ¬∀ {α : Type} {xs : Array α} {v : α} {i : USize}, i.toNat < xs.size := fun hc_h => absurd (@hc_h (Nat) (#[]) (0) (USize.ofNat 0)) (by
  decide)

-- Vector.le_refl, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.le_refl.h3 : ¬∀ {α : Type} {n : Nat} [inst : LT α] (xs : Vector α n), xs ≤ xs := fun hc_h => absurd (@hc_h (Nat) (1) (⟨fun a b => a ≤ b⟩ : LT Nat) (#v[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.getElem_unattach, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.getElem_unattach.h4 : ¬∀ {α : Type} {p : α → Prop} {xs : Array { x : α // p x }} (i : Nat), i < xs.unattach.size := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (#[]) (0)) (by
  decide +kernel)

-- Vector.unattach_mk, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.unattach_mk.h4 : ¬∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Array { x : α // p x }}, xs.size = n := fun hc_h => absurd (@hc_h (Nat) (0) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })])) (by
  decide)

-- Int64.toISize_ofIntClamp, hypothesis 2: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Int64.toISize_ofIntClamp.h2.inst : ¬(Int64.ofIntClamp 9223372036854775808).toISize = ISize.ofInt 9223372036854775808 := by
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
theorem HypCheckProof.Int64.toISize_ofIntClamp.h2.prem0 : -2 ^ 63 ≤ 9223372036854775808 := by
  decide
theorem HypCheckProof.Int64.toISize_ofIntClamp.h2 : ¬∀ {n : Int}, -2 ^ 63 ≤ n → (Int64.ofIntClamp n).toISize = ISize.ofInt n := fun hc_h => HypCheckProof.Int64.toISize_ofIntClamp.h2.inst (@hc_h (9223372036854775808) HypCheckProof.Int64.toISize_ofIntClamp.h2.prem0)

-- Int16.toISize_ofInt, hypothesis 2: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Int16.toISize_ofInt.h2.inst : ¬(Int16.ofInt 32768).toISize = ISize.ofInt 32768 := by
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
theorem HypCheckProof.Int16.toISize_ofInt.h2.prem0 : Int16.minValue.toInt ≤ 32768 := by
  decide
theorem HypCheckProof.Int16.toISize_ofInt.h2 : ¬∀ {n : Int}, Int16.minValue.toInt ≤ n → (Int16.ofInt n).toISize = ISize.ofInt n := fun hc_h => HypCheckProof.Int16.toISize_ofInt.h2.inst (@hc_h (32768) HypCheckProof.Int16.toISize_ofInt.h2.prem0)

-- USize.sub_le, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.sub_le.h2 : ¬∀ {a b : USize}, a - b ≤ a := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 1)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.eq_of_toBitVec_eq, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.eq_of_toBitVec_eq.h2 : ¬∀ {a b : USize}, a = b := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 1)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- ISize.toInt.inj, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ISize.toInt.inj.h2 : ¬∀ {x y : ISize}, x = y := fun hc_h => absurd (@hc_h (ISize.ofInt 0) (ISize.ofInt 1)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.toBitVec_ne_of_ne, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.toBitVec_ne_of_ne.h2 : ¬∀ {a b : USize}, a.toBitVec ≠ b.toBitVec := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 0)) (by
  decide)

-- UInt64.toUSize_ofNatTruncate_of_lt, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.UInt64.toUSize_ofNatTruncate_of_lt.h1.inst : ¬(UInt64.ofNatClamp 18446744073709551616).toUSize = USize.ofNat 18446744073709551616 := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.UInt64.toUSize_ofNatTruncate_of_lt.h1 : ¬∀ {n : Nat}, (UInt64.ofNatClamp n).toUSize = USize.ofNat n := fun hc_h => HypCheckProof.UInt64.toUSize_ofNatTruncate_of_lt.h1.inst (@hc_h (18446744073709551616))

-- USize.toNat_ofNat_of_lt', hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.toNat_ofNat_of_lt'.h1 : ¬∀ {n : Nat}, (USize.ofNat n).toNat = n := fun hc_h => absurd (@hc_h (18446744073709551616)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.toFin_ofNatClamp_of_lt, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.toFin_ofNatClamp_of_lt.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.toFin_ofNatClamp_of_lt.h1 : ¬∀ {n : Nat}, n < USize.size := fun hc_h => HypCheckProof.USize.toFin_ofNatClamp_of_lt.h1.inst (@hc_h (18446744073709551616))

-- ISize.toInt_ofNat_of_lt_two_pow_numBits, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ISize.toInt_ofNat_of_lt_two_pow_numBits.h1 : ¬∀ {n : Nat}, (ISize.ofNat n).toInt = ↑n := fun hc_h => absurd (@hc_h (9223372036854775808)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- UInt16.toUSize_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.UInt16.toUSize_ofNat.h1.inst : Not
      (@Eq USize
        (@OfNat.ofNat UInt16 (@OfNat.ofNat Nat (nat_lit 65536) (instOfNatNat (nat_lit 65536)))
            (@UInt16.instOfNat (@OfNat.ofNat Nat (nat_lit 65536) (instOfNatNat (nat_lit 65536))))).toUSize
        (@OfNat.ofNat USize (@OfNat.ofNat Nat (nat_lit 65536) (instOfNatNat (nat_lit 65536)))
          (@USize.instOfNat (@OfNat.ofNat Nat (nat_lit 65536) (instOfNatNat (nat_lit 65536)))))) := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.UInt16.toUSize_ofNat.h1 : Not
      (∀ {n : Nat},
        @Eq USize (@OfNat.ofNat UInt16 n (@UInt16.instOfNat n)).toUSize (@OfNat.ofNat USize n (@USize.instOfNat n))) := fun hc_h => HypCheckProof.UInt16.toUSize_ofNat.h1.inst (@hc_h (@OfNat.ofNat Nat (nat_lit 65536) (instOfNatNat (nat_lit 65536))))

-- USize.toBitVec_ofNatClamp_of_lt, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.toBitVec_ofNatClamp_of_lt.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.toBitVec_ofNatClamp_of_lt.h1 : ¬∀ {n : Nat}, n < USize.size := fun hc_h => HypCheckProof.USize.toBitVec_ofNatClamp_of_lt.h1.inst (@hc_h (18446744073709551616))

-- ISize.ofBitVec_ofNatLT, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.ISize.ofBitVec_ofNatLT.h1.inst : ¬18446744073709551616 < 2 ^ System.Platform.numBits := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.ISize.ofBitVec_ofNatLT.h1 : ¬∀ (n : Nat), n < 2 ^ System.Platform.numBits := fun hc_h => HypCheckProof.ISize.ofBitVec_ofNatLT.h1.inst (@hc_h (18446744073709551616))

-- UInt8.toUSize_ofNat', hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt8.toUSize_ofNat'.h1 : ¬∀ {n : Nat}, (UInt8.ofNat n).toUSize = USize.ofNat n := fun hc_h => absurd (@hc_h (256)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.toUInt64_ofNatTruncate_of_lt, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.toUInt64_ofNatTruncate_of_lt.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.toUInt64_ofNatTruncate_of_lt.h1 : ¬∀ {n : Nat}, n < USize.size := fun hc_h => HypCheckProof.USize.toUInt64_ofNatTruncate_of_lt.h1.inst (@hc_h (18446744073709551616))

-- ISize.ofNat_int16ToNatClampNeg, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ISize.ofNat_int16ToNatClampNeg.h1 : ¬∀ (x : Int16), ISize.ofNat x.toNatClampNeg = x.toISize := fun hc_h => absurd (@hc_h (Int16.ofInt (-1))) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

