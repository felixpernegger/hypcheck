import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- List.map_le, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.map_le.h6 : ¬∀ {α β : Type} [inst : LT α] [inst_1 : LT β] [inst_2 : Std.Asymm fun (x1 x2 : α) => x1 < x2]
        [inst_3 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_4 : Std.Trichotomous fun (x1 x2 : β) => x1 < x2]
        {l₁ l₂ : List α} {f : α → β}, (∀ (x y : α), x < y → f x < f y) → l₁ ≤ l₂ → List.map f l₁ ≤ List.map f l₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (instLTNat) (⟨fun a b => a ≤ b⟩ : LT Nat) _ _ (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) ([0]) ([0]) (fun n => n + 1 : Nat → Nat) (by
  grind) (by
  decide)) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.flatMap_lt_flatMap_iff, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.flatMap_lt_flatMap_iff.h7 : ¬∀ {α β : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_2 : LT β]
        [inst_3 : Std.Asymm fun (x1 x2 : β) => x1 < x2] (f : α → Array β),
        (∀ (a b : α) (zs : Array β), f a ++ zs = f b → a = b) →
          (∀ (a : α), f a ≠ #[]) → ∀ {xs ys : Array α}, Array.flatMap f xs < Array.flatMap f ys ↔ xs < ys := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (instLTNat) _ (fun n => #[n] : Nat → Array Nat) (by
  simp) (by
  simp) (#[0]) (#[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.apply_minOn_le_apply_minOn_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.apply_minOn_le_apply_minOn_of_subset.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs ys : List α} {f : α → β} (hxs : ys ⊆ xs) (hys : ys ≠ []),
        f
            (List.minOn f xs
              ((fun {α : Type} {xs ys : List α} (hxs : ys ⊆ xs) (hys : ys ≠ []) (h : xs = []) =>
                  False.elim
                    (Eq.mp (Eq.trans List.subset_nil._simp_1 (eq_false hys))
                      (Eq.mp (congrArg (fun (_a : List α) => ys ⊆ _a) h) hxs)))
                hxs hys)) ≤
          f (List.minOn f ys hys) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) ([0]) ([0]) (fun n => n % 2 == 0 : Nat → Bool) hc_k0 hc_k1) (by
  decide)

-- Array.le_antisymm, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.le_antisymm.h4 : ¬∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : Std.IsLinearOrder α] {xs ys : Array α},
        xs ≤ ys → ys ≤ xs → xs = ys := fun hc_h => absurd (@hc_h (Bool) (⟨fun a b => a = b⟩ : LT Bool) (Bool.instLE) (@Std.IsLinearOrder.mk (Bool) (Bool.instLE) (@Std.IsPartialOrder.mk (Bool) (Bool.instLE) (@Std.IsPreorder.mk (Bool) (Bool.instLE) (by (try dsimp only);   decide) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (#[Bool.false]) (#[Bool.true]) (by
  (letI _hcd0 : @DecidableRel Bool Bool (@LT.lt Bool (@LT.mk Bool fun (a b : Bool) => @Eq Bool a b)) :=
      fun (a b : Bool) => instDecidableEqBool a b;
    decide)) (by
  (letI _hcd0 : @DecidableRel Bool Bool (@LT.lt Bool (@LT.mk Bool fun (a b : Bool) => @Eq Bool a b)) :=
      fun (a b : Bool) => instDecidableEqBool a b;
    decide))) (by
  decide)

-- Option.merge_le, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.merge_le.h6 : ¬∀ {α : Type} [inst : LE α] {f : α → α → α} {o₁ o₂ o₃ : Option α}, o₁ ≤ o₃ → o₂ ≤ o₃ → Option.merge f o₁ o₂ ≤ o₃ := fun hc_h => absurd (@hc_h (Bool) (Bool.instLE) (fun a b => !a || b : Bool → Bool → Bool) (Option.some Bool.false) (Option.some Bool.false) (Option.some Bool.false) (by
  simp) (by
  simp)) (by
  (simp <;> decide))

-- List.MergeSort.Internal.splitInTwo_fst_le_splitInTwo_snd, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.MergeSort.Internal.splitInTwo_fst_le_splitInTwo_snd.h4 : ¬∀ {α : Type} {n : Nat} {le : α → α → Prop} {l : { l : List α // l.length = n }} (a b : α),
        a ∈ (List.MergeSort.Internal.splitInTwo l).fst.val → b ∈ (List.MergeSort.Internal.splitInTwo l).snd.val → le a b := fun hc_h => absurd (@hc_h (Nat) (2) (fun a b => a < b : Nat → Nat → Prop) ((⟨[1, 0], of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { l : List Nat // l.length = 2 })) (1) (0) (by
  decide) (by
  decide)) (by
  decide)

-- List.MergeSort.Internal.splitInTwo_fst_le_splitInTwo_snd, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.MergeSort.Internal.splitInTwo_fst_le_splitInTwo_snd.h7 : ¬∀ {α : Type} {n : Nat} {le : α → α → Prop} {l : { l : List α // l.length = n }},
        List.Pairwise le l.val → ∀ (a b : α), b ∈ (List.MergeSort.Internal.splitInTwo l).snd.val → le a b := fun hc_h => absurd (@hc_h (Nat) (2) (fun a b => a < b : Nat → Nat → Prop) ((⟨[0, 1], of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { l : List Nat // l.length = 2 })) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1) (1) (by
  decide)) (by
  decide)

-- List.MergeSort.Internal.splitInTwo_fst_le_splitInTwo_snd, hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.MergeSort.Internal.splitInTwo_fst_le_splitInTwo_snd.h8 : ¬∀ {α : Type} {n : Nat} {le : α → α → Prop} {l : { l : List α // l.length = n }},
        List.Pairwise le l.val → ∀ (a b : α), a ∈ (List.MergeSort.Internal.splitInTwo l).fst.val → le a b := fun hc_h => absurd (@hc_h (Nat) (1) (fun a b => a < b : Nat → Nat → Prop) ((⟨[0], of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { l : List Nat // l.length = 1 })) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0) (0) (by
  decide)) (by
  decide)

-- Array.foldl_subtype', hypothesis 8: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldl_subtype'.h8 : ¬∀ {α β : Type} {stop : Nat} {p : α → Prop} {xs : Array { x : α // p x }} {f : β → { x : α // p x } → β} {g : β → α → β}
        {x : β}, stop = xs.size → Array.foldl f x xs 0 stop = Array.foldl g x xs.unattach := fun hc_h => absurd (@hc_h (Nat) (Nat) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })].size) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : Nat) (a_1 : { x : Nat // (fun (n : Nat) => n = 0) x }) => 0) (fun a b => a - b : Nat → Nat → Nat) (1) rfl) (by
  decide +kernel)

-- List.mapM_subtype, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.mapM_subtype.h9 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] [inst_1 : LawfulMonad m] {p : α → Prop} {l : List { x : α // p x }}
        {f : { x : α // p x } → m β} {g : α → m β}, List.mapM f l = List.mapM g l.unattach := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (instMonadOption) _ (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Option.none) (some : Nat → Option Nat)) (by
  decide)

-- Vector.append_le_append_iff, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.append_le_append_iff.h4 : ¬∀ {α : Type} {n m : Nat} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {xs₁ xs₂ : Vector α n}
        {ys₁ ys₂ : Vector α m}, xs₁ ++ ys₁ ≤ xs₂ ++ ys₂ ↔ xs₁ < xs₂ ∨ xs₁ = xs₂ ∧ ys₁ ≤ ys₂ := fun hc_h => absurd (@hc_h (Nat) (1) (0) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (#v[0]) (#v[0]) (#v[]) (#v[])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.maxIdxOn?_replicate_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.maxIdxOn?_replicate_of_pos.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {n : Nat} {a : α} {f : α → β},
        0 < n → List.maxIdxOn? f (List.replicate n a) = Option.some 0 := fun hc_h => absurd (@hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) (2) (0) (fun n => n % 2 == 0 : Nat → Bool) (by
  decide)) (by
  decide)

-- Array.map_lt, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.map_lt.h7 : ¬∀ {α β : Type} [inst : LT α] [inst_1 : LT β] {xs ys : Array α} {f : α → β}, xs < ys → Array.map f xs < Array.map f ys := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (instLTNat) (#[0]) (#[0]) (fun n => n + 1 : Nat → Nat) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))) (by
  decide +kernel)

-- List.le_apply_maxOn_append_left, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.le_apply_maxOn_append_left.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs ys : List α} {f : α → β} (h : xs ≠ []),
        f (List.maxOn f xs h) ≤ f (List.maxOn f (xs ++ ys) (List.append_ne_nil_of_left_ne_nil h ys)) := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) ([0]) ([]) (fun n => n % 2 == 0 : Nat → Bool) hc_k0) (by
  decide)

-- List.le_apply_minOn_iff, hypothesis 4: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.List.le_apply_minOn_iff.h4.inst : ¬∀ (h : [0, 1] ≠ []),
        Bool.false = (fun (n : Nat) => n % 2 == 0) (List.minOn (fun (n : Nat) => n % 2 == 0) [0, 1] h) ↔
          ∀ (x : Nat), x ∈ [0, 1] → Bool.false = (fun (n : Nat) => n % 2 == 0) x := by
  decide
theorem HypCheckProof.List.le_apply_minOn_iff.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs : List α} {f : α → β} (h : xs ≠ []) {b : β},
        b ≤ f (List.minOn f xs h) ↔ ∀ (x : α), x ∈ xs → b ≤ f x := fun hc_h => HypCheckProof.List.le_apply_minOn_iff.h4.inst (fun hc_k0 => @hc_h (Bool) (Nat) ({ le := fun (a b : Bool) => a = b : LE Bool }) (fun (a b : Bool) => instDecidableEqBool a b) ([0, 1]) (fun (n : Nat) => n % 2 == 0) hc_k0 (Bool.false))

-- Array.any_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.any_subtype.h6 : ¬∀ {α : Type} {stop : Nat} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        stop = xs.size → xs.any f 0 stop = xs.unattach.any g := fun hc_h => absurd (@hc_h (Nat) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })].size) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool) rfl) (by
  decide +kernel)

-- Array.any_subtype, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.any_subtype.h7 : ¬∀ {α : Type} {stop : Nat} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        (∀ (x : α) (h : p x), f (⟨x, h⟩ : { x : α // p x }) = g x) → xs.any f 0 stop = xs.unattach.any g := fun hc_h => absurd (@hc_h (Nat) (0) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.true) (fun n => n % 2 == 0 : Nat → Bool) (by
  simp)) (by
  decide +kernel)

-- Option.right_le_max, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.right_le_max.h4 : ¬∀ {α : Type} [inst : LE α] [inst_1 : Max α], (∀ (x : α), x ≤ x) → ∀ {a b : Option α}, b ≤ Max.max a b := fun hc_h => absurd (@hc_h (Nat) (instLENat) (⟨fun a b => a - b⟩ : Max Nat) (by
  simp) (Option.some 0) (Option.some 1)) (by
  simp)

-- Vector.map_subtype, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.map_subtype.h7 : ¬∀ {α : Type} {n : Nat} {β : Type} {p : α → Prop} {xs : Vector { x : α // p x } n} {f : { x : α // p x } → β}
        {g : α → β}, Vector.map f xs = Vector.map g xs.unattach := fun hc_h => absurd (@hc_h (Nat) (1) (Nat) (fun n => n = 0 : Nat → Prop) (#v[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => 0) (fun n => n + 1 : Nat → Nat)) (by
  decide +kernel)

-- List.map_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.map_subtype.h6 : ¬∀ {α β : Type} {p : α → Prop} {l : List { x : α // p x }} {f : { x : α // p x } → β} {g : α → β},
        List.map f l = List.map g l.unattach := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => 0) (fun n => n + 1 : Nat → Nat)) (by
  decide)

-- Vector.findFinIdx?_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.findFinIdx?_subtype.h6 : ¬∀ {α : Type} {n : Nat} {p : α → Prop} {xs : Vector { x : α // p x } n} {f : { x : α // p x } → Bool} {g : α → Bool},
        Vector.findFinIdx? f xs = Vector.findFinIdx? g xs.unattach := fun hc_h => absurd (@hc_h (Nat) (1) (fun n => n = 0 : Nat → Prop) (#v[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- Array.exists_of_uset, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.exists_of_uset.h4 : ¬∀ {α : Type} {xs : Array α} {i : USize} {d : α}, i.toNat < xs.size := fun hc_h => absurd (@hc_h (Nat) (#[]) (USize.ofNat 0) (0)) (by
  decide)

-- List.le_refl, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.le_refl.h2 : ¬∀ {α : Type} [inst : LT α] (l : List α), l ≤ l := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) ([0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- ISize.toInt_ofInt_of_two_pow_numBits_le, hypothesis 2: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.ISize.toInt_ofInt_of_two_pow_numBits_le.h2.inst : ¬(ISize.ofInt 9223372036854775808).toInt = 9223372036854775808 := by
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
theorem HypCheckProof.ISize.toInt_ofInt_of_two_pow_numBits_le.h2.prem0 : -2 ^ (System.Platform.numBits - 1) ≤ 9223372036854775808 := by
  grind
theorem HypCheckProof.ISize.toInt_ofInt_of_two_pow_numBits_le.h2 : ¬∀ {n : Int}, -2 ^ (System.Platform.numBits - 1) ≤ n → (ISize.ofInt n).toInt = n := fun hc_h => HypCheckProof.ISize.toInt_ofInt_of_two_pow_numBits_le.h2.inst (@hc_h (9223372036854775808) HypCheckProof.ISize.toInt_ofInt_of_two_pow_numBits_le.h2.prem0)

-- Array.ugetElem_eq_getElem, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.ugetElem_eq_getElem.h3 : ¬∀ {α : Type} {xs : Array α} {i : USize}, i.toNat < xs.size := fun hc_h => absurd (@hc_h (Nat) (#[]) (USize.ofNat 0)) (by
  decide)

-- USize.lt_asymm, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.lt_asymm.h2 : ¬∀ {a b : USize}, ¬b < a := fun hc_h => absurd (@hc_h (USize.ofNat 1) (USize.ofNat 0)) (by
  (simp <;> decide))

-- USize.eq_of_toFin_eq, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.eq_of_toFin_eq.h2 : ¬∀ {a b : USize}, a = b := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 1)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- Membership.mem.lower, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Membership.mem.lower.h2 : ¬∀ {i : Nat} {r : Std.Legacy.Range}, r.start ≤ i := fun hc_h => absurd (@hc_h (0) ([1:0])) (by
  decide)

-- Membership.mem.upper, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Membership.mem.upper.h2 : ¬∀ {i : Nat} {r : Std.Legacy.Range}, i < r.stop := fun hc_h => absurd (@hc_h (0) ([:0])) (by
  decide)

-- Membership.mem.step, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Membership.mem.step.h2 : ¬∀ {i : Nat} {r : Std.Legacy.Range}, (i - r.start) % r.step = 0 := fun hc_h => absurd (@hc_h (1) ([:0:2])) (by
  decide)

-- USize.lt_ofNat_iff, hypothesis 2: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.lt_ofNat_iff.h2.inst : ¬(USize.ofNat 0 < USize.ofNat 18446744073709551616 ↔ (USize.ofNat 0).toNat < 18446744073709551616) := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.lt_ofNat_iff.h2 : ¬∀ {n : USize} {m : Nat}, n < USize.ofNat m ↔ n.toNat < m := fun hc_h => HypCheckProof.USize.lt_ofNat_iff.h2.inst (@hc_h (USize.ofNat 0) (18446744073709551616))

-- USize.mod_eq_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.mod_eq_of_lt.h2 : ¬∀ {a b : USize}, a % b = a := fun hc_h => absurd (@hc_h (USize.ofNat 1) (USize.ofNat 1)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- UInt8.toUSize_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.UInt8.toUSize_ofNat.h1.inst : Not
      (@Eq USize
        (@OfNat.ofNat UInt8 (@OfNat.ofNat Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))
            (@UInt8.instOfNat (@OfNat.ofNat Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))).toUSize
        (@OfNat.ofNat USize (@OfNat.ofNat Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))
          (@USize.instOfNat (@OfNat.ofNat Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))))) := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.UInt8.toUSize_ofNat.h1 : Not
      (∀ {n : Nat},
        @Eq USize (@OfNat.ofNat UInt8 n (@UInt8.instOfNat n)).toUSize (@OfNat.ofNat USize n (@USize.instOfNat n))) := fun hc_h => HypCheckProof.UInt8.toUSize_ofNat.h1.inst (@hc_h (@OfNat.ofNat Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))

-- USize.ofNatLT_eq_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.ofNatLT_eq_ofNat.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.ofNatLT_eq_ofNat.h1 : ¬∀ (n : Nat), n < USize.size := fun hc_h => HypCheckProof.USize.ofNatLT_eq_ofNat.h1.inst (@hc_h (18446744073709551616))

-- USize.toFin_ofNatTruncate_of_lt, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.toFin_ofNatTruncate_of_lt.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.toFin_ofNatTruncate_of_lt.h1 : ¬∀ {n : Nat}, n < USize.size := fun hc_h => HypCheckProof.USize.toFin_ofNatTruncate_of_lt.h1.inst (@hc_h (18446744073709551616))

-- UInt64.toUSize_ofNatClamp_of_lt, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.UInt64.toUSize_ofNatClamp_of_lt.h1.inst : ¬(UInt64.ofNatClamp 18446744073709551616).toUSize = USize.ofNat 18446744073709551616 := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.UInt64.toUSize_ofNatClamp_of_lt.h1 : ¬∀ {n : Nat}, (UInt64.ofNatClamp n).toUSize = USize.ofNat n := fun hc_h => HypCheckProof.UInt64.toUSize_ofNatClamp_of_lt.h1.inst (@hc_h (18446744073709551616))

-- USize.toUInt8_ofNatLT, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.toUInt8_ofNatLT.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.toUInt8_ofNatLT.h1 : ¬∀ {n : Nat}, n < USize.size := fun hc_h => HypCheckProof.USize.toUInt8_ofNatLT.h1.inst (@hc_h (18446744073709551616))

-- ISize.ofNat_int32ToNatClampNeg, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ISize.ofNat_int32ToNatClampNeg.h1 : ¬∀ (x : Int32), ISize.ofNat x.toNatClampNeg = x.toISize := fun hc_h => absurd (@hc_h (Int32.ofInt (-1))) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.toUInt32_ofNatLT, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.toUInt32_ofNatLT.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.toUInt32_ofNatLT.h1 : ¬∀ {n : Nat}, n < USize.size := fun hc_h => HypCheckProof.USize.toUInt32_ofNatLT.h1.inst (@hc_h (18446744073709551616))

-- USize.toBitVec_ofNatLT, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.toBitVec_ofNatLT.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.toBitVec_ofNatLT.h1 : ¬∀ {n : Nat}, n < USize.size := fun hc_h => HypCheckProof.USize.toBitVec_ofNatLT.h1.inst (@hc_h (18446744073709551616))

-- USize.toISize_ofNatLT, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.toISize_ofNatLT.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.toISize_ofNatLT.h1 : ¬∀ {n : Nat}, n < USize.size := fun hc_h => HypCheckProof.USize.toISize_ofNatLT.h1.inst (@hc_h (18446744073709551616))

-- ISize.ofNat_int8ToNatClampNeg, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ISize.ofNat_int8ToNatClampNeg.h1 : ¬∀ (x : Int8), ISize.ofNat x.toNatClampNeg = x.toISize := fun hc_h => absurd (@hc_h (Int8.ofInt (-1))) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- UInt64.toUSize_ofNatTruncate_of_le, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.UInt64.toUSize_ofNatTruncate_of_le.h1.inst : ¬(UInt64.ofNatClamp 0).toUSize =
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
theorem HypCheckProof.UInt64.toUSize_ofNatTruncate_of_le.h1 : ¬∀ {n : Nat},
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
              (Eq.refl USize.size_eq)) := fun hc_h => HypCheckProof.UInt64.toUSize_ofNatTruncate_of_le.h1.inst (@hc_h (0))

