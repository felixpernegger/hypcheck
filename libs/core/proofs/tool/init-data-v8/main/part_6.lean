import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Array.foldlM_congr, hypothesis 14: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldlM_congr.h14 : ¬∀ {β α : Type} {start start' stop stop' : Nat} {m : Type → Type} [inst : Monad m] {f g : β → α → m β} {b : β}
        {xs xs' : Array α},
        xs = xs' → start = start' → stop = stop' → Array.foldlM f b xs start stop = Array.foldlM g b xs' start' stop' := fun hc_h => absurd (@hc_h (Nat) (Nat) (0) (0) (1) (1) (Option : Type → Type) (instMonadOption) (fun (a x : Nat) => Option.none) (fun (a : Nat) => Option.some) (0) (#[0]) (#[0]) rfl rfl rfl) (by
  decide)

-- Array.foldlM_congr, hypothesis 15: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldlM_congr.h15 : ¬∀ {β α : Type} {start start' stop stop' : Nat} {m : Type → Type} [inst : Monad m] {f g : β → α → m β} {b : β}
        {xs xs' : Array α},
        xs = xs' →
          (∀ (x : β) (y : α), f x y = g x y) →
            stop = stop' → Array.foldlM f b xs start stop = Array.foldlM g b xs' start' stop' := fun hc_h => absurd (@hc_h (Nat) (Nat) (0) (1) (1) (1) (Option : Type → Type) (instMonadOption) (fun (a x : Nat) => Option.none) (fun (a x : Nat) => Option.none) (0) (#[0]) (#[0]) rfl (by
  simp) rfl) (by
  decide)

-- Array.map_le, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.map_le.h6 : ¬∀ {α β : Type} [inst : LT α] [inst_1 : LT β] [inst_2 : Std.Asymm fun (x1 x2 : α) => x1 < x2]
        [inst_3 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_4 : Std.Trichotomous fun (x1 x2 : β) => x1 < x2]
        {xs ys : Array α} {f : α → β}, (∀ (x y : α), x < y → f x < f y) → xs ≤ ys → Array.map f xs ≤ Array.map f ys := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLTNat) (⟨fun a b => a ≤ b⟩ : LT Nat) _ _ (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (#[0]) (#[0]) (fun n => n + 1 : Nat → Nat) (by
  grind) (by
  decide)) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    simp <;> decide))

-- Array.flatMap_le_flatMap_iff, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.flatMap_le_flatMap_iff.h7 : ¬∀ {α β : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
        [inst_3 : Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → Array β),
        (∀ (a b : α) (zs : Array β), f a ++ zs = f b → a = b) →
          (∀ (a : α), f a ≠ #[]) → ∀ {xs ys : Array α}, Array.flatMap f xs ≤ Array.flatMap f ys ↔ xs ≤ ys := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (instLTNat) _ (fun n => #[n] : Nat → Array Nat) (by
  simp) (by
  simp) (#[0]) (#[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Vector.map_le_map_iff, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.map_le_map_iff.h6 : ¬∀ {α β : Type} {n : Nat} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
        (f : α → β), (∀ (a b : α), a < b → f a < f b) → ∀ {xs ys : Vector α n}, Vector.map f xs ≤ Vector.map f ys ↔ xs ≤ ys := fun hc_h => absurd (@hc_h (Nat) (Nat) (1) (instLTNat) _ (⟨fun a b => a ≤ b⟩ : LT Nat) (fun n => n + 1 : Nat → Nat) (by
  grind) (#v[0]) (#v[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    simp <;> decide))

-- Std.Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some, hypothesis 9: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some.h9.inst : ¬0 + 1 - 0 = 0 + 1 - 0 + 1 := by
  decide
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Std.Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some.h9.prem0 : 0 ≤ 0 := by
  decide
theorem HypCheckProof.Std.Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some.h9 : ¬∀ {α : Type} {inst : LT α} {inst_1 : Std.PRange.UpwardEnumerable α} {inst_2 : Std.Rxo.HasSize α}
        [self : Std.Rxo.LawfulHasSize α] (lo hi lo' : α),
        lo < hi → Std.Rxo.HasSize.size lo hi = Std.Rxo.HasSize.size lo' hi + 1 := fun hc_h => HypCheckProof.Std.Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some.h9.inst (@hc_h (Nat) ({ lt := fun (a b : Nat) => a ≤ b : LT Nat }) ({ succ? := fun (n : Nat) => Option.some (n + 1), succMany? := fun (k n : Nat) => Option.some (n + k + 1) :
      Std.PRange.UpwardEnumerable Nat }) ({ size := fun (lo hi : Nat) => hi + 1 - lo : Std.Rxo.HasSize Nat }) (@Std.Rxo.LawfulHasSize.mk (Nat) (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) (@Std.PRange.UpwardEnumerable.mk Nat
      (fun (n : Nat) =>
        @Option.some Nat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      fun (k n : Nat) =>
      @Option.some Nat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n k)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (@Std.Rxo.HasSize.mk Nat fun (lo hi : Nat) =>
      @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) hi (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) lo) (by (try dsimp only);   (intros; omega)) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all <;> omega))) (0) (0) (0) HypCheckProof.Std.Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some.h9.prem0)

-- Array.min_le_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.min_le_of_mem.h3 : ¬∀ {α : Type} [inst : Min α] [inst_1 : LE α] [inst_2 : Std.LawfulOrderMin α] {xs : Array α} {a : α} (ha : a ∈ xs),
        xs.min (Array.ne_empty_of_mem ha) ≤ a := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Bool.instMin) (⟨fun _ _ => False⟩ : LE Bool) (@Std.LawfulOrderMin.mk (Bool) (Bool.instMin) (@LE.mk Bool fun (x x_1 : Bool) => False) (@Std.MinEqOr.mk (Bool) (Bool.instMin) (by (try dsimp only);   decide)) (@Std.LawfulOrderInf.mk (Bool) (Bool.instMin) (@LE.mk Bool fun (x x_1 : Bool) => False) (by (try dsimp only);   decide))) (#[Bool.false]) (Bool.false) hc_k0) (by
  decide +kernel)

-- Array.min_le_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.min_le_of_mem.h4 : ¬∀ {α : Type} [inst : Min α] [inst_1 : LE α] [inst_2 : Std.IsLinearOrder α] {xs : Array α} {a : α} (ha : a ∈ xs),
        xs.min (Array.ne_empty_of_mem ha) ≤ a := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (⟨fun a b => a - b⟩ : Min Nat) (instLENat) _ (#[1, 0]) (0) hc_k0) (by
  decide +kernel)

-- List.append_left_le, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.append_left_le.h2 : ¬∀ {α : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {l₁ l₂ l₃ : List α},
        l₂ ≤ l₃ → l₁ ++ l₂ ≤ l₁ ++ l₃ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) ([0]) ([]) ([]) (by
  simp)) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.append_left_le, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.append_left_le.h2 : ¬∀ {α : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {xs ys zs : Array α},
        ys ≤ zs → xs ++ ys ≤ xs ++ zs := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (#[0]) (#[]) (#[]) (by
  simp)) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.minIdxOn?_replicate_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.minIdxOn?_replicate_of_pos.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {n : Nat} {a : α} {f : α → β},
        0 < n → List.minIdxOn? f (List.replicate n a) = Option.some 0 := fun hc_h => absurd (@hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) (2) (0) (fun n => n % 2 == 0 : Nat → Bool) (by
  decide)) (by
  decide)

-- List.minIdxOn_eq_zero_iff, hypothesis 4: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.List.minIdxOn_eq_zero_iff.h4.inst : ¬∀ (h : [0] ≠ []), List.minIdxOn (fun (n : Nat) => n % 2 == 0) [0] h = 0 ↔ ∀ (x : Nat), x ∈ [0] → False := by
  decide
theorem HypCheckProof.List.minIdxOn_eq_zero_iff.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs : List α} {f : α → β} (h : xs ≠ []),
        List.minIdxOn f xs h = 0 ↔ ∀ (x : α), x ∈ xs → f (xs.head h) ≤ f x := fun hc_h => HypCheckProof.List.minIdxOn_eq_zero_iff.h4.inst (fun hc_k0 => @hc_h (Bool) (Nat) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (fun (a b : Bool) => instDecidableFalse) ([0]) (fun (n : Nat) => n % 2 == 0) hc_k0)

-- Option.right_le_of_merge_le, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.right_le_of_merge_le.h3 : ¬∀ {α : Type} [inst : LE α] {f : α → α → α} {o₁ o₂ o₃ : Option α}, Option.merge f o₁ o₂ ≤ o₃ → o₂ ≤ o₃ := fun hc_h => absurd (@hc_h (Nat) (instLENat) (fun a b => a - b : Nat → Nat → Nat) (Option.some 0) (Option.some 1) (Option.some 0) (by
  simp)) (by
  simp)

-- Option.left_le_of_merge_le, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.left_le_of_merge_le.h3 : ¬∀ {α : Type} [inst : LE α] {f : α → α → α} {o₁ o₂ o₃ : Option α}, Option.merge f o₁ o₂ ≤ o₃ → o₁ ≤ o₃ := fun hc_h => absurd (@hc_h (Nat) (instLENat) (fun a b => a - b : Nat → Nat → Nat) (Option.some 1) (Option.some 1) (Option.some 0) (by
  simp)) (by
  simp)

-- Option.right_lt_of_merge_lt, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.right_lt_of_merge_lt.h3 : ¬∀ {α : Type} [inst : LT α] {f : α → α → α} {o₁ o₂ o₃ : Option α}, Option.merge f o₁ o₂ < o₃ → o₂ < o₃ := fun hc_h => absurd (@hc_h (Nat) (instLTNat) (fun a b => a - b : Nat → Nat → Nat) (Option.some 0) (Option.some 1) (Option.some 1) (by
  simp)) (by
  simp)

-- List.cons_le_cons_iff, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.cons_le_cons_iff.h2 : ¬∀ {α : Type} [inst : LT α] [i₂ : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {a b : α} {l₁ l₂ : List α},
        a :: l₁ ≤ b :: l₂ ↔ a < b ∨ a = b ∧ l₁ ≤ l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (0) (0) ([]) ([])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.le_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.le_of_lt.h2 : ¬∀ {α : Type} [inst : LT α] {l₁ l₂ : List α}, l₁ < l₂ → l₁ ≤ l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) ([0]) ([0]) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.IsPrefix.le, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.IsPrefix.le.h2 : ¬∀ {α : Type} [inst : LT α] {l₁ l₂ : List α}, l₁ <+: l₂ → l₁ ≤ l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) ([0]) ([0]) (by
  decide)) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.lt_asymm, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.lt_asymm.h2 : ¬∀ {α : Type} [inst : LT α] {l₁ l₂ : List α}, l₁ < l₂ → ¬l₂ < l₁ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) ([0]) ([0]) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.le_iff_lt_or_eq, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.le_iff_lt_or_eq.h3 : ¬∀ {α : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {l₁ l₂ : List α},
        l₁ ≤ l₂ ↔ l₁ < l₂ ∨ l₁ = l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) ([0]) ([0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.le_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.le_of_lt.h2 : ¬∀ {α : Type} [inst : LT α] {xs ys : Array α}, xs < ys → xs ≤ ys := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (#[0]) (#[0]) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Std.LinearOrderPackage.le_antisymm, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.LinearOrderPackage.le_antisymm.h4 : ¬∀ {α : Type} [self : Std.LinearOrderPackage α] (a b : α), b ≤ a → a = b := fun hc_h => absurd (@hc_h (Int : Type) (Int.instLinearOrderPackage) (1) (0) (by
  decide)) (by
  decide)

-- Std.LinearOrderPackage.le_antisymm, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.LinearOrderPackage.le_antisymm.h5 : ¬∀ {α : Type} [self : Std.LinearOrderPackage α] (a b : α), a ≤ b → a = b := fun hc_h => absurd (@hc_h (Int : Type) (Int.instLinearOrderPackage) (0) (1) (by
  decide)) (by
  decide)

-- USize.ofNatLT_mul, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.ofNatLT_mul.h2 : ¬∀ {a b : Nat}, b < 2 ^ System.Platform.numBits → a * b < 2 ^ System.Platform.numBits → a < 2 ^ System.Platform.numBits := fun hc_h => absurd (@hc_h (18446744073709551616) (0) (by
  grind) (by
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

-- USize.ofNatLT_mul, hypothesis 3: necessary
/- FAILED: 3:2: Tactic `decide` failed to reduce
  @decide (0 < 2 ^ System.Platform.numBits) (Nat.decLt 0 (2 ^ System.Platform.numBits))
to `true` or `false`.

Reduction got stuck at
  (Nat.succ 0).ble (2 ^ System.Platform.numBits) | 13:2: Tactic `decide` failed to reduce
  @decide (0 < 2 ^ System.Platform.numBits) (Nat.decLt 0 (2 ^ System.Platform.numBits))
to `true` or `false`.

Reduction got stuck at
  (Nat.succ 0).ble (2 ^ System.Platform.numBits) | 3:2: Tactic `decide` failed to reduce
  @decide (0 < 2 ^ System.Platform.numBits) (Nat.decLt 0 (2 ^ System.Platform.numBits))
to `true` or `false`.

Reduction got stuck at
  (Nat.succ 0).ble (2 ^ System.Platform.numBits) | 13:2: Tactic `decide` failed to reduce
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
theorem HypCheckProof.USize.ofNatLT_mul.h3 : ¬∀ {a b : Nat}, a < 2 ^ System.Platform.numBits → a * b < 2 ^ System.Platform.numBits → b < 2 ^ System.Platform.numBits := fun hc_h => absurd (@hc_h (0) (18446744073709551616) (by
  decide +kernel) (by
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
-/

-- Vector.foldl_subtype, hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.foldl_subtype.h8 : ¬∀ {α : Type} {n : Nat} {β : Type} {p : α → Prop} {xs : Vector { x : α // p x } n} {f : β → { x : α // p x } → β}
        {g : β → α → β} {x : β}, Vector.foldl f x xs = Vector.foldl g x xs.unattach := fun hc_h => absurd (@hc_h (Nat) (1) (Nat) (fun n => n = 0 : Nat → Prop) (#v[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : Nat) (a_1 : { x : Nat // (fun (n : Nat) => n = 0) x }) => 0) (fun a b => a - b : Nat → Nat → Nat) (1)) (by
  decide +kernel)

-- USize.lt_of_le_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.lt_of_le_of_lt.h4 : ¬∀ {a b c : USize}, a ≤ b → a < c := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 0) (USize.ofNat 0) (by
  decide)) (by
  decide)

-- List.maxIdxOn?_replicate, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.maxIdxOn?_replicate.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {n : Nat} {a : α} {f : α → β},
        List.maxIdxOn? f (List.replicate n a) = if n = 0 then Option.none else Option.some 0 := fun hc_h => absurd (@hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) (2) (0) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide)

-- Option.merge_le_iff, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.merge_le_iff.h6 : ¬∀ {α : Type} [inst : LE α] {f : α → α → α} {o₁ o₂ o₃ : Option α}, Option.merge f o₁ o₂ ≤ o₃ ↔ o₁ ≤ o₃ ∧ o₂ ≤ o₃ := fun hc_h => absurd (@hc_h (Nat) (instLENat) (fun a b => a - b : Nat → Nat → Nat) (Option.some 0) (Option.some 1) (Option.some 0)) (by
  simp)

-- List.minIdxOn?_eq_some_zero_iff, hypothesis 4: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.List.minIdxOn?_eq_some_zero_iff.h4.inst : ¬(List.minIdxOn? (fun (n : Nat) => n % 2 == 0) [0] = Option.some 0 ↔ ∃ (h : [0] ≠ []), ∀ (x : Nat), x ∈ [0] → False) := by
  decide
theorem HypCheckProof.List.minIdxOn?_eq_some_zero_iff.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs : List α} {f : α → β},
        List.minIdxOn? f xs = Option.some 0 ↔ ∃ (h : xs ≠ []), ∀ (x : α), x ∈ xs → f (xs.head h) ≤ f x := fun hc_h => HypCheckProof.List.minIdxOn?_eq_some_zero_iff.h4.inst (@hc_h (Bool) (Nat) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (fun (a b : Bool) => instDecidableFalse) ([0]) (fun (n : Nat) => n % 2 == 0))

-- Vector.all_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.all_subtype.h6 : ¬∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Vector { x : α // p x } n} {f : { x : α // p x } → Bool} {g : α → Bool},
        xs.all f = xs.unattach.all g := fun hc_h => absurd (@hc_h (Nat) (1) (fun n => n = 0 : Nat → Prop) (#v[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- Vector.count_attachWith, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.count_attachWith.h5 : ¬∀ {α : Type} {n : Nat} [inst : BEq α] {p : α → Prop} {xs : Vector α n} {a : { x : α // p x }} (a : α), a ∈ xs → p a := fun hc_h => absurd (@hc_h (Nat) (1) (instBEqOfDecidableEq) (fun n => n = 0 : Nat → Prop) (#v[1]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x }))) (by
  decide)

-- Vector.find?_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.find?_subtype.h6 : ¬∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Vector { x : α // p x } n} {f : { x : α // p x } → Bool} {g : α → Bool},
        Option.map Subtype.val (Vector.find? f xs) = Vector.find? g xs.unattach := fun hc_h => absurd (@hc_h (Nat) (1) (fun n => n = 0 : Nat → Prop) (#v[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- Vector.any_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.any_subtype.h6 : ¬∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Vector { x : α // p x } n} {f : { x : α // p x } → Bool} {g : α → Bool},
        xs.any f = xs.unattach.any g := fun hc_h => absurd (@hc_h (Nat) (1) (fun n => n = 0 : Nat → Prop) (#v[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- Array.findFinIdx?_subtype, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.findFinIdx?_subtype.h5 : ¬∀ {α : Type} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        Array.findFinIdx? f xs =
          Option.map (fun (i : Fin xs.unattach.size) => Fin.cast (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) i) (Array.findFinIdx? g xs.unattach) := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (#[(⟨0, (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- Array.findIdx?_subtype, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.findIdx?_subtype.h5 : ¬∀ {α : Type} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        Array.findIdx? f xs = Array.findIdx? g xs.unattach := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- List.any_subtype, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.any_subtype.h5 : ¬∀ {α : Type} {p : α → Prop} {l : List { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        l.any f = l.unattach.any g := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide)

