import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Array.allM_congr, hypothesis 12: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.allM_congr.h12 : ¬∀ {m : Type → Type} {α : Type} {start₁ start₂ stop₁ stop₂ : Nat} [inst : Monad m] {xs ys : Array α},
        xs = ys →
          ∀ {p q : α → m Bool},
            start₁ = start₂ → stop₁ = stop₂ → Array.allM p xs start₁ stop₁ = Array.allM q ys start₂ stop₂ := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (0) (0) (1) (1) (instMonadOption) (#[0]) (#[0]) rfl (fun n => some (n % 2 == 0) : Nat → Option Bool) (fun _ => none : Nat → Option Bool) rfl rfl) (by
  decide +kernel)

-- Array.filterMap_congr, hypothesis 12: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.filterMap_congr.h12 : ¬∀ {α β : Type} {as bs : Array α},
        as = bs →
          ∀ {f g : α → Option β},
            f = g →
              ∀ {start stop start' stop' : Nat},
                stop = stop' → Array.filterMap f as start stop = Array.filterMap g bs start' stop' := fun hc_h => absurd (@hc_h (Nat) (Nat) (#[0]) (#[0]) rfl (some : Nat → Option Nat) (some : Nat → Option Nat) rfl (0) (1) (1) (1) rfl) (by
  decide)

-- List.flatMap_le_flatMap_iff, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.flatMap_le_flatMap_iff.h7 : ¬∀ {α β : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
        [inst_3 : Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → List β),
        (∀ (a b : α), f a <+: f b → a = b) →
          (∀ (a : α), f a ≠ []) → ∀ {l₁ l₂ : List α}, List.flatMap f l₁ ≤ List.flatMap f l₂ ↔ l₁ ≤ l₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (instLTNat) _ (fun n => [n] : Nat → List Nat) (by
  simp) (by
  simp) ([0]) ([0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.map_le_map_iff, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.map_le_map_iff.h5 : ¬∀ {α β : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β] (f : α → β),
        (∀ (a b : α), a < b → f a < f b) → ∀ {xs ys : Array α}, Array.map f xs ≤ Array.map f ys ↔ xs ≤ ys := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLTNat) _ (⟨fun a b => a ≤ b⟩ : LT Nat) (fun n => n + 1 : Nat → Nat) (by
  grind) (#[0]) (#[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    simp <;> decide))

-- Array.map_le_map_iff, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.map_le_map_iff.h7 : ¬∀ {α β : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
        [inst_3 : Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → β) {xs ys : Array α},
        Array.map f xs ≤ Array.map f ys ↔ xs ≤ ys := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (instLTNat) _ (fun n => n + 1 : Nat → Nat) (#[0]) (#[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    simp <;> decide))

-- List.map_lt_map_iff, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.map_lt_map_iff.h5 : ¬∀ {α β : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β] (f : α → β),
        (∀ (a b : α), a < b → f a < f b) → ∀ {l₁ l₂ : List α}, List.map f l₁ < List.map f l₂ ↔ l₁ < l₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLTNat) _ (⟨fun a b => a ≤ b⟩ : LT Nat) (fun n => n + 1 : Nat → Nat) (by
  grind) ([0]) ([0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Option.merge_lt, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.merge_lt.h6 : ¬∀ {α : Type} [inst : LT α] {f : α → α → α} {o₁ o₂ o₃ : Option α}, o₁ < o₃ → o₂ < o₃ → Option.merge f o₁ o₂ < o₃ := fun hc_h => absurd (@hc_h (Bool) (Bool.instLT) (fun a b => !a || b : Bool → Bool → Bool) (Option.some Bool.false) (Option.some Bool.false) (Option.some Bool.true) (by
  rfl) (by
  rfl)) (by
  simp)

-- List.foldrM_subtype, hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.foldrM_subtype.h10 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] [inst_1 : LawfulMonad m] {p : α → Prop} {l : List { x : α // p x }}
        {f : { x : α // p x } → β → m β} {g : α → β → m β} {x : β}, List.foldrM f x l = List.foldrM g x l.unattach := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (instMonadOption) _ (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) (x : Nat) => Option.none) (fun (a : Nat) => Option.some) (0)) (by
  decide)

-- List.filterMapM_subtype, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.filterMapM_subtype.h9 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] [inst_1 : LawfulMonad m] {p : α → Prop} {l : List { x : α // p x }}
        {f : { x : α // p x } → m (Option β)} {g : α → m (Option β)}, List.filterMapM f l = List.filterMapM g l.unattach := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (instMonadOption) _ (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Option.none) (fun (a : Nat) => Option.some Option.none)) (by
  decide)

-- Array.foldr_subtype', hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldr_subtype'.h8 : ¬∀ {α β : Type} {start : Nat} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → β → β}
        {g : α → β → β} {x : β}, start = xs.size → Array.foldr f x xs start = Array.foldr g x xs.unattach := fun hc_h => absurd (@hc_h (Nat) (Nat) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })].size) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) (n : Nat) => n + 1) (fun a b => a - b : Nat → Nat → Nat) (0) rfl) (by
  decide +kernel)

-- Array.foldr_subtype', hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldr_subtype'.h9 : ¬∀ {α β : Type} {start : Nat} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → β → β}
        {g : α → β → β} {x : β},
        (∀ (x : α) (h : p x) (b : β), f (⟨x, h⟩ : { x : α // p x }) b = g x b) →
          Array.foldr f x xs start = Array.foldr g x xs.unattach := fun hc_h => absurd (@hc_h (Nat) (Bool) (0) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.not) (fun (a : Nat) => Bool.not) (Bool.false) (by
  simp)) (by
  decide +kernel)

-- List.flatMapM_subtype, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.flatMapM_subtype.h9 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] [inst_1 : LawfulMonad m] {p : α → Prop} {l : List { x : α // p x }}
        {f : { x : α // p x } → m (List β)} {g : α → m (List β)}, List.flatMapM f l = List.flatMapM g l.unattach := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (instMonadOption) _ (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Option.none) (fun (a : Nat) => Option.some [])) (by
  decide)

-- Array.mapM_subtype, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.mapM_subtype.h9 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] [inst_1 : LawfulMonad m] {p : α → Prop} {xs : Array { x : α // p x }}
        {f : { x : α // p x } → m β} {g : α → m β}, Array.mapM f xs = Array.mapM g xs.unattach := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (instMonadOption) _ (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Option.none) (some : Nat → Option Nat)) (by
  decide +kernel)

-- List.maxIdxOn_replicate, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.maxIdxOn_replicate.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {n : Nat} {a : α} {f : α → β} (h : List.replicate n a ≠ []),
        List.maxIdxOn f (List.replicate n a) h = 0 := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) (2) (0) (fun n => n % 2 == 0 : Nat → Bool) hc_k0) (by
  decide)

-- List.apply_minOn_append_le_left, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.apply_minOn_append_le_left.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs ys : List α} {f : α → β} (h : xs ≠ []),
        f (List.minOn f (xs ++ ys) (List.append_ne_nil_of_left_ne_nil h ys)) ≤ f (List.minOn f xs h) := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) ([0]) ([]) (fun n => n % 2 == 0 : Nat → Bool) hc_k0) (by
  decide)

-- List.maxIdxOn_eq_zero_iff, hypothesis 4: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.List.maxIdxOn_eq_zero_iff.h4.inst : ¬∀ (h : [0] ≠ []), List.maxIdxOn (fun (n : Nat) => n % 2 == 0) [0] h = 0 ↔ ∀ (x : Nat), x ∈ [0] → False := by
  decide
theorem HypCheckProof.List.maxIdxOn_eq_zero_iff.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs : List α} {f : α → β} (h : xs ≠ []),
        List.maxIdxOn f xs h = 0 ↔ ∀ (x : α), x ∈ xs → f x ≤ f (xs.head h) := fun hc_h => HypCheckProof.List.maxIdxOn_eq_zero_iff.h4.inst (fun hc_k0 => @hc_h (Bool) (Nat) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (fun (a b : Bool) => instDecidableFalse) ([0]) (fun (n : Nat) => n % 2 == 0) hc_k0)

-- Array.all_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.all_subtype.h6 : ¬∀ {α : Type} {stop : Nat} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        stop = xs.size → xs.all f 0 stop = xs.unattach.all g := fun hc_h => absurd (@hc_h (Nat) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })].size) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool) rfl) (by
  decide +kernel)

-- Array.all_subtype, hypothesis 7: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Array.all_subtype.h7.inst : ¬#[(⟨Bool.true, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Bool // (fun (b : Bool) => b = Bool.true) x })].all
          (fun (a : { x : Bool // (fun (b : Bool) => b = Bool.true) x }) => Bool.false) 0 0 =
        #[(⟨Bool.true, of_decide_eq_true (id (Eq.refl Bool.true))⟩ :
                  { x : Bool // (fun (b : Bool) => b = Bool.true) x })].unattach.all
          Bool.not := by
  decide +kernel
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Array.all_subtype.h7.prem0 : ∀ (x : Bool) (h : x = Bool.true),
      (fun (a : { x : Bool // (fun (b : Bool) => b = Bool.true) x }) => Bool.false)
          (⟨x, h⟩ : { x : Bool // (fun (b : Bool) => b = Bool.true) x }) =
        !x := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Array.all_subtype.h7 : ¬∀ {α : Type} {stop : Nat} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        (∀ (x : α) (h : p x), f (⟨x, h⟩ : { x : α // p x }) = g x) → xs.all f 0 stop = xs.unattach.all g := fun hc_h => HypCheckProof.Array.all_subtype.h7.inst (@hc_h (Bool) (0) (fun (b : Bool) => b = Bool.true) (#[(⟨Bool.true, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Bool // (fun (b : Bool) => b = Bool.true) x })]) (fun (a : { x : Bool // (fun (b : Bool) => b = Bool.true) x }) => Bool.false) (Bool.not) HypCheckProof.Array.all_subtype.h7.prem0)

-- Array.append_right_lt_iff_of_size_eq, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.append_right_lt_iff_of_size_eq.h2 : ¬∀ {α : Type} [inst : LT α] {xs₁ xs₂ : Array α} (ys : Array α),
        xs₁.size = xs₂.size → (xs₁ ++ ys < xs₂ ++ ys ↔ xs₁ < xs₂) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (#[]) (#[]) (#[0]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Vector.le_iff_exists, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.le_iff_exists.h3 : ¬∀ {α : Type} {n : Nat} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {xs ys : Vector α n},
        xs ≤ ys ↔ xs = ys ∨ ∃ (i : Nat), ∃ (h : i < n), (∀ (j : Nat) (hj : j < i), xs[j] = ys[j]) ∧ xs[i] < ys[i] := fun hc_h => absurd (@hc_h (Nat) (1) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (#v[0]) (#v[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.max?_eq_some_iff, hypothesis 5: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Array.max?_eq_some_iff.h5.inst : ¬(#[Bool.false].max? = Option.some Bool.false ↔ Bool.false ∈ #[Bool.false] ∧ ∀ (b : Bool), b ∈ #[Bool.false] → False) := by
  decide +kernel
theorem HypCheckProof.Array.max?_eq_some_iff.h5 : ¬∀ {α : Type} {a : α} [inst : Max α] [inst_1 : LE α] {xs : Array α} [inst_2 : Std.LawfulOrderMax α],
        xs.max? = Option.some a ↔ a ∈ xs ∧ ∀ (b : α), b ∈ xs → b ≤ a := fun hc_h => HypCheckProof.Array.max?_eq_some_iff.h5.inst (@hc_h (Bool) (Bool.false) (Bool.instMax) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (#[Bool.false]) (@Std.LawfulOrderMax.mk (Bool) (Bool.instMax) (@LE.mk Bool fun (x x_1 : Bool) => False) (@Std.MaxEqOr.mk (Bool) (Bool.instMax) (by (try dsimp only);   decide)) (@Std.LawfulOrderSup.mk (Bool) (Bool.instMax) (@LE.mk Bool fun (x x_1 : Bool) => False) (by (try dsimp only);   decide))))

-- Array.max?_eq_some_iff, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.max?_eq_some_iff.h6 : ¬∀ {α : Type} {a : α} [inst : Max α] [inst_1 : LE α] {xs : Array α} [inst_2 : Std.IsLinearOrder α],
        xs.max? = Option.some a ↔ a ∈ xs ∧ ∀ (b : α), b ∈ xs → b ≤ a := fun hc_h => absurd (@hc_h (Nat) (0) (⟨fun a b => a - b⟩ : Max Nat) (instLENat) (#[0, 1]) _) (by
  decide +kernel)

-- Array.exists_of_eraseP, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.exists_of_eraseP.h5 : ¬∀ {α : Type} {p : α → Bool} {xs : Array α} {a : α},
        a ∈ xs →
          ∃ (a : α),
            ∃ (ys : Array α),
              ∃ (zs : Array α),
                (∀ (b : α), b ∈ ys → ¬p b = Bool.true) ∧ p a = Bool.true ∧ xs = ys.push a ++ zs ∧ xs.eraseP p = ys ++ zs := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) (#[1]) (1) (by
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

-- Array.lt_asymm, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.lt_asymm.h2 : ¬∀ {α : Type} [inst : LT α] {xs ys : Array α}, xs < ys → ¬ys < xs := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (#[0]) (#[0]) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.le_iff_exists, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.le_iff_exists.h2 : ¬∀ {α : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {xs ys : Array α},
        xs ≤ ys ↔
          xs = ys.take xs.size ∨
            ∃ (i : Nat),
              ∃ (h₁ : i < xs.size), ∃ (h₂ : i < ys.size), (∀ (j : Nat) (hj : j < i), xs[j] = ys[j]) ∧ xs[i] < ys[i] := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (#[0]) (#[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.exists_of_eraseP, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.exists_of_eraseP.h5 : ¬∀ {α : Type} {p : α → Bool} {l : List α} {a : α},
        a ∈ l →
          ∃ (a : α),
            ∃ (l₁ : List α),
              ∃ (l₂ : List α),
                (∀ (b : α), b ∈ l₁ → ¬p b = Bool.true) ∧ p a = Bool.true ∧ l = l₁ ++ a :: l₂ ∧ List.eraseP p l = l₁ ++ l₂ := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) ([1]) (1) (by
  decide)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- Std.PRange.LinearlyUpwardEnumerable.eq_of_succ?_eq, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Std.PRange.LinearlyUpwardEnumerable.eq_of_succ?_eq.h5 : ¬∀ {α : Type} {inst : Std.PRange.UpwardEnumerable α} [self : Std.PRange.LinearlyUpwardEnumerable α] (a b : α), a = b := fun hc_h => absurd (@hc_h (Nat) ({ succ? := fun n => some (n + 2), succMany? := fun k n => some (n + 2 * k) } : Std.PRange.UpwardEnumerable Nat) (@Std.PRange.LinearlyUpwardEnumerable.mk (Nat) (@Std.PRange.UpwardEnumerable.mk Nat
      (fun (n : Nat) =>
        @Option.some Nat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      fun (k n : Nat) =>
      @Option.some Nat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))) (by (try dsimp only);   (intros; simp_all; done))) (0) (1)) (by
  decide)

-- le_apply_minOn_iff, hypothesis 4: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.le_apply_minOn_iff.h4.inst : ¬(Bool.false = (fun (n : Nat) => n % 2 == 0) (minOn (fun (n : Nat) => n % 2 == 0) 0 1) ↔
        Bool.false = (fun (n : Nat) => n % 2 == 0) 0 ∧ Bool.false = (fun (n : Nat) => n % 2 == 0) 1) := by
  decide
theorem HypCheckProof.le_apply_minOn_iff.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {x y : α} {b : β},
        b ≤ f (minOn f x y) ↔ b ≤ f x ∧ b ≤ f y := fun hc_h => HypCheckProof.le_apply_minOn_iff.h4.inst (@hc_h (Bool) (Nat) ({ le := fun (a b : Bool) => a = b : LE Bool }) (fun (a b : Bool) => instDecidableEqBool a b) (fun (n : Nat) => n % 2 == 0) (0) (1) (Bool.false))

-- Array.foldr_subtype, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldr_subtype.h7 : ¬∀ {α β : Type} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → β → β} {g : α → β → β} {x : β},
        Array.foldr f x xs = Array.foldr g x xs.unattach := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) (n : Nat) => n + 1) (fun a b => a - b : Nat → Nat → Nat) (0)) (by
  decide +kernel)

-- List.foldr_subtype, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.foldr_subtype.h7 : ¬∀ {α β : Type} {p : α → Prop} {l : List { x : α // p x }} {f : { x : α // p x } → β → β} {g : α → β → β} {x : β},
        List.foldr f x l = List.foldr g x l.unattach := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) (n : Nat) => n + 1) (fun a b => a - b : Nat → Nat → Nat) (0)) (by
  decide)

-- List.minIdxOn?_replicate, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.minIdxOn?_replicate.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {n : Nat} {a : α} {f : α → β},
        List.minIdxOn? f (List.replicate n a) = if n = 0 then Option.none else Option.some 0 := fun hc_h => absurd (@hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) (2) (0) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide)

-- Array.findSome?_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.findSome?_subtype.h6 : ¬∀ {α β : Type} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → Option β} {g : α → Option β},
        Array.findSome? f xs = Array.findSome? g xs.unattach := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Option.none) (some : Nat → Option Nat)) (by
  decide +kernel)

-- Array.map_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.map_subtype.h6 : ¬∀ {α β : Type} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → β} {g : α → β},
        Array.map f xs = Array.map g xs.unattach := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => 0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- Option.bind_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.bind_subtype.h6 : ¬∀ {α β : Type} {p : α → Prop} {o : Option { x : α // p x }} {f : { x : α // p x } → Option β} {g : α → Option β},
        o.bind f = o.unattach.bind g := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n = 0 : Nat → Prop) (Option.some (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Option.none) (some : Nat → Option Nat)) (by
  decide)

-- USize.ofNatLT_le_iff_le, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.ofNatLT_le_iff_le.h2 : ¬∀ {a b : Nat}, b < USize.size → a < USize.size := fun hc_h => absurd (@hc_h (18446744073709551616) (0) (by
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

-- USize.ofNatLT_le_iff_le, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.ofNatLT_le_iff_le.h3 : ¬∀ {a b : Nat}, a < USize.size → b < USize.size := fun hc_h => absurd (@hc_h (0) (18446744073709551616) (by
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

-- USize.ofNatLT_div, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.ofNatLT_div.h2 : ¬∀ {a b : Nat}, b < 2 ^ System.Platform.numBits → a < 2 ^ System.Platform.numBits := fun hc_h => absurd (@hc_h (18446744073709551616) (0) (by
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

-- USize.ofNatLT_div, hypothesis 3: necessary
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
theorem HypCheckProof.USize.ofNatLT_div.h3 : ¬∀ {a b : Nat}, a < 2 ^ System.Platform.numBits → b < 2 ^ System.Platform.numBits := fun hc_h => absurd (@hc_h (0) (18446744073709551616) (by
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

-- ISize.lt_of_le_of_ne, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ISize.lt_of_le_of_ne.h3 : ¬∀ {a b : ISize}, a ≤ b → a < b := fun hc_h => absurd (@hc_h (ISize.ofInt 0) (ISize.ofInt 0) (by
  simp)) (by
  simp)

-- USize.le_antisymm, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.le_antisymm.h2 : ¬∀ {a b : USize}, b ≤ a → a = b := fun hc_h => absurd (@hc_h (USize.ofNat 1) (USize.ofNat 0) (by
  decide)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.le_antisymm, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.le_antisymm.h3 : ¬∀ {a b : USize}, a ≤ b → a = b := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 1) (by
  decide)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- Option.min_le_right, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.min_le_right.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : Min α] {a b : Option α}, Min.min a b ≤ b := fun hc_h => absurd (@hc_h (Nat) (instLENat) (⟨fun a b => a - b⟩ : Min Nat) (Option.some 1) (Option.some 0)) (by
  simp)

-- Array.unattach_filter, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.unattach_filter.h5 : ¬∀ {α : Type} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        (Array.filter f xs).unattach = Array.filter g xs.unattach := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- Vector.le_total, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.le_total.h3 : ¬∀ {α : Type} {n : Nat} [inst : LT α] (xs ys : Vector α n), xs ≤ ys ∨ ys ≤ xs := fun hc_h => absurd (@hc_h (Nat) (1) (⟨fun a b => a ≤ b⟩ : LT Nat) (#v[0]) (#v[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.le_append_left, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.le_append_left.h2 : ¬∀ {α : Type} [inst : LT α] {xs ys : Array α}, xs ≤ xs ++ ys := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (#[0]) (#[])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Option.getD_attachWith, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.getD_attachWith.h3 : ¬∀ {α : Type} {p : α → Prop} {o : Option α} {fallback : { x : α // p x }} (x : α), o = Option.some x → p x := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) (Option.some 1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x }))) (by
  decide)

-- List.uset_toArray, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.uset_toArray.h4 : ¬∀ {α : Type} {l : List α} {i : USize} {a : α}, i.toNat < l.toArray.size := fun hc_h => absurd (@hc_h (Nat) ([]) (USize.ofNat 0) (0)) (by
  decide)

-- Array.size_uset, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.size_uset.h4 : ¬∀ {α : Type} {xs : Array α} {v : α} {i : USize}, i.toNat < xs.size := fun hc_h => absurd (@hc_h (Nat) (#[]) (0) (USize.ofNat 0)) (by
  decide)

-- List.lt_irrefl, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.lt_irrefl.h2 : ¬∀ {α : Type} [inst : LT α] (l : List α), ¬l < l := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) ([0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.lt_irrefl, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.lt_irrefl.h2 : ¬∀ {α : Type} [inst : LT α] (xs : Array α), ¬xs < xs := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (#[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Int8.toISize_ofInt, hypothesis 2: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Int8.toISize_ofInt.h2.inst : ¬(Int8.ofInt 128).toISize = ISize.ofInt 128 := by
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
theorem HypCheckProof.Int8.toISize_ofInt.h2.prem0 : Int8.minValue.toInt ≤ 128 := by
  decide
theorem HypCheckProof.Int8.toISize_ofInt.h2 : ¬∀ {n : Int}, Int8.minValue.toInt ≤ n → (Int8.ofInt n).toISize = ISize.ofInt n := fun hc_h => HypCheckProof.Int8.toISize_ofInt.h2.inst (@hc_h (128) HypCheckProof.Int8.toISize_ofInt.h2.prem0)

-- Int64.toISize_ofIntTruncate, hypothesis 2: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.Int64.toISize_ofIntTruncate.h2.inst : ¬(Int64.ofIntClamp 9223372036854775808).toISize = ISize.ofInt 9223372036854775808 := by
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
theorem HypCheckProof.Int64.toISize_ofIntTruncate.h2.prem0 : -2 ^ 63 ≤ 9223372036854775808 := by
  decide
theorem HypCheckProof.Int64.toISize_ofIntTruncate.h2 : ¬∀ {n : Int}, -2 ^ 63 ≤ n → (Int64.ofIntClamp n).toISize = ISize.ofInt n := fun hc_h => HypCheckProof.Int64.toISize_ofIntTruncate.h2.inst (@hc_h (9223372036854775808) HypCheckProof.Int64.toISize_ofIntTruncate.h2.prem0)

-- USize.ofNat_sub, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.ofNat_sub.h2 : ¬∀ {a b : Nat}, USize.ofNat (a - b) = USize.ofNat a - USize.ofNat b := fun hc_h => absurd (@hc_h (0) (1)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.ofNat_le_iff, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.ofNat_le_iff.h2 : ¬∀ {n : USize} {m : Nat}, USize.ofNat m ≤ n ↔ m ≤ n.toNat := fun hc_h => absurd (@hc_h (USize.ofNat 0) (18446744073709551616)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.lt_or_eq_of_le, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.lt_or_eq_of_le.h2 : ¬∀ {a b : USize}, a < b ∨ a = b := fun hc_h => absurd (@hc_h (USize.ofNat 1) (USize.ofNat 0)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- ISize.ofNat_sub, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ISize.ofNat_sub.h2 : ¬∀ (a b : Nat), ISize.ofNat (a - b) = ISize.ofNat a - ISize.ofNat b := fun hc_h => absurd (@hc_h (0) (1)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.le_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.le_of_lt.h2 : ¬∀ {a b : USize}, a ≤ b := fun hc_h => absurd (@hc_h (USize.ofNat 1) (USize.ofNat 0)) (by
  (simp <;> decide))

-- USize.lt_or_lt_of_ne, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.lt_or_lt_of_ne.h2 : ¬∀ {a b : USize}, a < b ∨ b < a := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 0)) (by
  decide)

-- ISize.lt_or_lt_of_ne, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ISize.lt_or_lt_of_ne.h2 : ¬∀ {a b : ISize}, a < b ∨ b < a := fun hc_h => absurd (@hc_h (ISize.ofInt 0) (ISize.ofInt 0)) (by
  simp)

-- USize.mod_lt, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.mod_lt.h2 : ¬∀ (a : USize) {b : USize}, a % b < b := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 0)) (by
  decide)

-- USize.toNat_sub_of_le, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.toNat_sub_of_le.h2 : ¬∀ (a b : USize), (a - b).toNat = a.toNat - b.toNat := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 1)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.ofNat_lt_iff, hypothesis 2: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.ofNat_lt_iff.h2.inst : ¬(USize.ofNat 18446744073709551616 < USize.ofNat 1 ↔ 18446744073709551616 < (USize.ofNat 1).toNat) := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.ofNat_lt_iff.h2 : ¬∀ {n : USize} {m : Nat}, USize.ofNat m < n ↔ m < n.toNat := fun hc_h => HypCheckProof.USize.ofNat_lt_iff.h2.inst (@hc_h (USize.ofNat 1) (18446744073709551616))

-- USize.toBitVec_eq_of_eq, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.toBitVec_eq_of_eq.h2 : ¬∀ {a b : USize}, a.toBitVec = b.toBitVec := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 1)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.toUInt64_ofNatClamp_of_lt, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.toUInt64_ofNatClamp_of_lt.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.toUInt64_ofNatClamp_of_lt.h1 : ¬∀ {n : Nat}, n < USize.size := fun hc_h => HypCheckProof.USize.toUInt64_ofNatClamp_of_lt.h1.inst (@hc_h (18446744073709551616))

-- UInt64.toUSize_ofNatClamp_of_le, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.UInt64.toUSize_ofNatClamp_of_le.h1.inst : ¬(UInt64.ofNatClamp 0).toUSize =
        USize.ofNatLT (USize.size - 1)
          (Or.casesOn (motive := fun (t : USize.size = 4294967296 ∨ USize.size = 18446744073709551616) =>
            USize.size_eq = t → USize.size - 1 < USize.size) USize.size_eq
            (fun (h : USize.size = 4294967296) (h_1 : USize.size_eq = Or.inl h) =>
              of_eq_true
                (Eq.trans (congr (congrArg LT.lt (congrFun' (congrArg HSub.hSub h) 1)) h)
                  (Nat.lt_add_one._simp_1 4294967295)))
            (fun (h : USize.size = 18446744073709551616) (h_1 : USize.size_eq = Or.inr h) =>
              of_eq_true
                (Eq.trans (congr (congrArg LT.lt (congrFun' (congrArg HSub.hSub h) 1)) h)
                  (Nat.lt_add_one._simp_1 18446744073709551615)))
            (Eq.refl USize.size_eq)) := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.UInt64.toUSize_ofNatClamp_of_le.h1 : ¬∀ {n : Nat},
        (UInt64.ofNatClamp n).toUSize =
          USize.ofNatLT (USize.size - 1)
            (Or.casesOn (motive := fun (t : USize.size = 4294967296 ∨ USize.size = 18446744073709551616) =>
              USize.size_eq = t → USize.size - 1 < USize.size) USize.size_eq
              (fun (h : USize.size = 4294967296) (h_1 : USize.size_eq = Or.inl h) =>
                of_eq_true
                  (Eq.trans (congr (congrArg LT.lt (congrFun' (congrArg HSub.hSub h) 1)) h)
                    (Nat.lt_add_one._simp_1 4294967295)))
              (fun (h : USize.size = 18446744073709551616) (h_1 : USize.size_eq = Or.inr h) =>
                of_eq_true
                  (Eq.trans (congr (congrArg LT.lt (congrFun' (congrArg HSub.hSub h) 1)) h)
                    (Nat.lt_add_one._simp_1 18446744073709551615)))
              (Eq.refl USize.size_eq)) := fun hc_h => HypCheckProof.UInt64.toUSize_ofNatClamp_of_le.h1.inst (@hc_h (0))

-- USize.toUInt64_ofNatLT, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.toUInt64_ofNatLT.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.toUInt64_ofNatLT.h1 : ¬∀ {n : Nat}, n < USize.size := fun hc_h => HypCheckProof.USize.toUInt64_ofNatLT.h1.inst (@hc_h (18446744073709551616))

-- UInt16.toUSize_ofNat', hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt16.toUSize_ofNat'.h1 : ¬∀ {n : Nat}, (UInt16.ofNat n).toUSize = USize.ofNat n := fun hc_h => absurd (@hc_h (65536)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- Int16.toISize_ofNat', hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int16.toISize_ofNat'.h1 : ¬∀ {n : Nat}, (Int16.ofNat n).toISize = ISize.ofNat n := fun hc_h => absurd (@hc_h (32768)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

