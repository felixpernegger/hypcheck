import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- Array.foldl_congr, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldl_congr.h4 : ¬∀ {α β : Type} {as bs : Array α} {f g : β → α → β},
        f = g →
          ∀ {a b : β},
            a = b →
              ∀ {start start' stop stop' : Nat},
                start = start' → stop = stop' → Array.foldl f a as start stop = Array.foldl g b bs start' stop' := fun hc_h => absurd (@hc_h (Nat) (Bool) (#[]) (#[0]) (fun (a : Bool) (n : Nat) => n % 2 == 0) (fun (a : Bool) (n : Nat) => n % 2 == 0) rfl (Bool.false) (Bool.false) rfl (0) (0) (1) (1) rfl rfl) (by
  decide)

-- Array.foldl_congr, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldl_congr.h7 : ¬∀ {α β : Type} {as bs : Array α},
        as = bs →
          ∀ {f g : β → α → β} {a b : β},
            a = b →
              ∀ {start start' stop stop' : Nat},
                start = start' → stop = stop' → Array.foldl f a as start stop = Array.foldl g b bs start' stop' := fun hc_h => absurd (@hc_h (Nat) (Nat) (#[1]) (#[1]) rfl (fun a b => a - b : Nat → Nat → Nat) (fun a b => a + b : Nat → Nat → Nat) (0) (0) rfl (0) (0) (1) (1) rfl rfl) (by
  decide)

-- Array.foldl_congr, hypothesis 15: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldl_congr.h15 : ¬∀ {α β : Type} {as bs : Array α},
        as = bs →
          ∀ {f g : β → α → β},
            f = g →
              ∀ {a b : β},
                a = b →
                  ∀ {start start' stop stop' : Nat},
                    stop = stop' → Array.foldl f a as start stop = Array.foldl g b bs start' stop' := fun hc_h => absurd (@hc_h (Nat) (Bool) (#[0]) (#[0]) rfl (fun (a : Bool) (n : Nat) => n % 2 == 0) (fun (a : Bool) (n : Nat) => n % 2 == 0) rfl (Bool.false) (Bool.false) rfl (0) (1) (1) (1) rfl) (by
  decide)

-- Array.foldl_congr, hypothesis 16: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldl_congr.h16 : ¬∀ {α β : Type} {as bs : Array α},
        as = bs →
          ∀ {f g : β → α → β},
            f = g →
              ∀ {a b : β},
                a = b →
                  ∀ {start start' stop stop' : Nat},
                    start = start' → Array.foldl f a as start stop = Array.foldl g b bs start' stop' := fun hc_h => absurd (@hc_h (Nat) (Bool) (#[0]) (#[0]) rfl (fun (a : Bool) (n : Nat) => n % 2 == 0) (fun (a : Bool) (n : Nat) => n % 2 == 0) rfl (Bool.false) (Bool.false) rfl (0) (0) (0) (1) rfl) (by
  decide)

-- Vector.map_le, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.map_le.h7 : ¬∀ {α β : Type} {n : Nat} [inst : LT α] [inst_1 : LT β] [inst_2 : Std.Asymm fun (x1 x2 : α) => x1 < x2]
        [inst_3 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] [inst_4 : Std.Trichotomous fun (x1 x2 : β) => x1 < x2]
        {xs ys : Vector α n} {f : α → β}, (∀ (x y : α), x < y → f x < f y) → xs ≤ ys → Vector.map f xs ≤ Vector.map f ys := fun hc_h => absurd (@hc_h (Nat) (Nat) (1) (instLTNat) (⟨fun a b => a ≤ b⟩ : LT Nat) _ _ (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (#v[0]) (#v[0]) (fun n => n + 1 : Nat → Nat) (by
  grind) (by
  decide)) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    simp <;> decide))

-- Array.filter_congr, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.filter_congr.h6 : ¬∀ {α : Type} {xs ys : Array α},
        xs = ys →
          ∀ {f g : α → Bool} {start stop start' stop' : Nat},
            start = start' → stop = stop' → Array.filter f xs start stop = Array.filter g ys start' stop' := fun hc_h => absurd (@hc_h (Nat) (#[0]) (#[0]) rfl (fun n => n % 2 == 0 : Nat → Bool) (fun _ => false : Nat → Bool) (0) (1) (0) (1) rfl rfl) (by
  decide)

-- Vector.lex_eq_false_iff_exists, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.lex_eq_false_iff_exists.h7 : ¬∀ {α : Type} {n : Nat} [inst : BEq α] [inst_1 : PartialEquivBEq α] (lt : α → α → Bool),
        (∀ (x y : α), (x == y) = Bool.true → lt x y = Bool.false) →
          (∀ (x y : α), lt x y = Bool.true → lt y x = Bool.false) →
            ∀ {xs ys : Vector α n},
              xs.lex ys lt = Bool.false ↔
                (ys.isEqv xs fun (x1 x2 : α) => x1 == x2) = Bool.true ∨
                  ∃ (i : Nat),
                    ∃ (h : i < n), (∀ (j : Nat) (hj : j < i), (xs[j] == ys[j]) = Bool.true) ∧ lt ys[i] xs[i] = Bool.true := fun hc_h => absurd (@hc_h (Int : Type) (1) (Int.instLinearOrderPackage.toBEq) _ (fun (a a_1 : Int) => Bool.false) (by
  simp) (by
  simp) (#v[0]) (#v[1])) (by
  decide)

-- Vector.append_left_le, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.append_left_le.h4 : ¬∀ {α : Type} {n m : Nat} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {xs : Vector α n}
        {ys ys' : Vector α m}, ys ≤ ys' → xs ++ ys ≤ xs ++ ys' := fun hc_h => absurd (@hc_h (Nat) (1) (0) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (#v[0]) (#v[]) (#v[]) (by
  simp)) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.foldlM_subtype, hypothesis 10: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.foldlM_subtype.h10 : ¬∀ {m : Type → Type} {α β : Type} {stop : Nat} [inst : Monad m] {p : α → Prop} {xs : Array { x : α // p x }}
        {f : β → { x : α // p x } → m β} {g : β → α → m β} {x : β},
        stop = xs.size → Array.foldlM f x xs 0 stop = Array.foldlM g x xs.unattach 0 stop := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })].size) (instMonadOption) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : Nat) (a_1 : { x : Nat // (fun (n : Nat) => n = 0) x }) => Option.none) (fun (a : Nat) => Option.some) (0) rfl) (by
  decide +kernel)

-- Array.append_le_append_iff_of_size_eq, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.append_le_append_iff_of_size_eq.h2 : ¬∀ {α : Type} [inst : LT α] [inst_1 : Std.Trichotomous fun (x1 x2 : α) => x1 < x2] {xs₁ xs₂ ys₁ ys₂ : Array α},
        xs₁.size = xs₂.size → (xs₁ ++ ys₁ ≤ xs₂ ++ ys₂ ↔ xs₁ < xs₂ ∨ xs₁ = xs₂ ∧ ys₁ ≤ ys₂) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (@Std.Trichotomous.mk (Nat) (fun (x1 x2 : Nat) => @LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) x1 x2) (by (try dsimp only);   (intros; omega))) (#[0]) (#[0]) (#[]) (#[]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.apply_get_minOn?_le_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.apply_get_minOn?_le_of_mem.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs),
        f ((List.minOn? f xs).get (List.isSome_minOn?_of_mem h)) ≤ f x := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) (fun n => n % 2 == 0 : Nat → Bool) ([0]) (0) hc_k0) (by
  decide)

-- List.le_apply_maxOn_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.le_apply_maxOn_of_mem.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs : List α} {f : α → β} {y : α} (hx : y ∈ xs),
        f y ≤ f (List.maxOn f xs (List.ne_nil_of_mem hx)) := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) ([0]) (fun n => n % 2 == 0 : Nat → Bool) (0) hc_k0) (by
  decide)

-- List.le_apply_minOn_take, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.le_apply_minOn_take.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs : List α} {f : α → β} {i : Nat} (h : List.take i xs ≠ []),
        f (List.minOn f xs (List.ne_nil_of_take_ne_nil h)) ≤ f (List.minOn f (List.take i xs) h) := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) ([0]) (fun n => n % 2 == 0 : Nat → Bool) (1) hc_k0) (by
  decide)

-- List.apply_maxOn_le_iff, hypothesis 4: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.List.apply_maxOn_le_iff.h4.inst : Not
      (∀
        (h :
          @Ne (List Nat)
            (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)))
            (@List.nil Nat)),
        Iff
          (@Eq Bool
            ((fun (n : Nat) =>
                @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
                  (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@List.maxOn Bool Nat (@LE.mk Bool fun (a b : Bool) => @Eq Bool a b)
                (fun (a b : Bool) => instDecidableEqBool a b)
                (fun (n : Nat) =>
                  @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
                    (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)))
                h))
            Bool.false)
          (∀ (x : Nat),
            @Membership.mem Nat (List Nat) (@List.instMembership Nat)
                (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat)))
                x →
              @Eq Bool
                ((fun (n : Nat) =>
                    @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
                      (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  x)
                Bool.false)) := by
  decide
theorem HypCheckProof.List.apply_maxOn_le_iff.h4 : Not
      (∀ {β α : Type} [inst : LE β] [inst_1 : @DecidableLE β inst] {xs : List α} {f : α → β}
        (h : @Ne (List α) xs (@List.nil α)) {b : β},
        Iff (@LE.le β inst (f (@List.maxOn β α inst inst_1 f xs h)) b)
          (∀ (x : α), @Membership.mem α (List α) (@List.instMembership α) xs x → @LE.le β inst (f x) b)) := fun hc_h => HypCheckProof.List.apply_maxOn_le_iff.h4.inst (fun hc_k0 => @hc_h (Bool) (Nat) (@LE.mk Bool fun (a b : Bool) => @Eq Bool a b) (fun (a b : Bool) => instDecidableEqBool a b) (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat))) (fun (n : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) hc_k0 (Bool.false))

-- List.le_apply_maxOn_append_right, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.le_apply_maxOn_append_right.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs ys : List α} {f : α → β} (h : ys ≠ []),
        f (List.maxOn f ys h) ≤ f (List.maxOn f (xs ++ ys) (List.append_ne_nil_of_right_ne_nil xs h)) := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) ([]) ([0]) (fun n => n % 2 == 0 : Nat → Bool) hc_k0) (by
  decide)

-- List.apply_maxOn_take_le, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.apply_maxOn_take_le.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs : List α} {f : α → β} {i : Nat} (h : List.take i xs ≠ []),
        f (List.maxOn f (List.take i xs) h) ≤ f (List.maxOn f xs (List.ne_nil_of_take_ne_nil h)) := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) ([0]) (fun n => n % 2 == 0 : Nat → Bool) (1) hc_k0) (by
  decide)

-- List.le_apply_get_maxOn?_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.le_apply_get_maxOn?_of_mem.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {xs : List α} {x : α} (h : x ∈ xs),
        f x ≤ f ((List.maxOn? f xs).get (List.isSome_maxOn?_of_mem h)) := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) (fun n => n % 2 == 0 : Nat → Bool) ([0]) (0) hc_k0) (by
  decide)

-- List.apply_minOn_append_le_right, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.apply_minOn_append_le_right.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs ys : List α} {f : α → β} (h : ys ≠ []),
        f (List.minOn f (xs ++ ys) (List.append_ne_nil_of_right_ne_nil xs h)) ≤ f (List.minOn f ys h) := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) ([]) ([0]) (fun n => n % 2 == 0 : Nat → Bool) hc_k0) (by
  decide)

-- List.minIdxOn_replicate, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.minIdxOn_replicate.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {n : Nat} {a : α} {f : α → β} (h : List.replicate n a ≠ []),
        List.minIdxOn f (List.replicate n a) h = 0 := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (Nat) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableFalse) (2) (0) (fun n => n % 2 == 0 : Nat → Bool) hc_k0) (by
  decide)

-- Array.append_right_le_iff_of_size_eq, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.append_right_le_iff_of_size_eq.h2 : ¬∀ {α : Type} [inst : LT α] {xs₁ xs₂ : Array α} (ys : Array α),
        xs₁.size = xs₂.size → (xs₁ ++ ys ≤ xs₂ ++ ys ↔ xs₁ ≤ xs₂) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (#[]) (#[]) (#[0]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Vector.lt_asymm, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.lt_asymm.h3 : ¬∀ {α : Type} {n : Nat} [inst : LT α] {xs ys : Vector α n}, xs < ys → ¬ys < xs := fun hc_h => absurd (@hc_h (Nat) (1) (⟨fun a b => a ≤ b⟩ : LT Nat) (#v[0]) (#v[0]) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.foldlM_subtype, hypothesis 9: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.foldlM_subtype.h9 : ¬∀ {m : Type → Type} {α β : Type} [inst : Monad m] {p : α → Prop} {l : List { x : α // p x }}
        {f : β → { x : α // p x } → m β} {g : β → α → m β} {x : β}, List.foldlM f x l = List.foldlM g x l.unattach := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (instMonadOption) (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : Nat) (a_1 : { x : Nat // (fun (n : Nat) => n = 0) x }) => Option.none) (fun (a : Nat) => Option.some) (0)) (by
  decide)

-- apply_maxOn_le_iff, hypothesis 4: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.apply_maxOn_le_iff.h4.inst : Not
      (Iff
        (@Eq Bool
          ((fun (n : Nat) =>
              @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
                (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@maxOn Bool Nat (@LE.mk Bool fun (a b : Bool) => @Eq Bool a b) (fun (a b : Bool) => instDecidableEqBool a b)
              (fun (n : Nat) =>
                @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
                  (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Bool.false)
        (And
          (@Eq Bool
            ((fun (n : Nat) =>
                @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
                  (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            Bool.false)
          (@Eq Bool
            ((fun (n : Nat) =>
                @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
                  (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            Bool.false))) := by
  decide
theorem HypCheckProof.apply_maxOn_le_iff.h4 : Not
      (∀ {β α : Type} [inst : LE β] [inst_1 : @DecidableLE β inst] {f : α → β} {x y : α} {b : β},
        Iff (@LE.le β inst (f (@maxOn β α inst inst_1 f x y)) b) (And (@LE.le β inst (f x) b) (@LE.le β inst (f y) b))) := fun hc_h => HypCheckProof.apply_maxOn_le_iff.h4.inst (@hc_h (Bool) (Nat) (@LE.mk Bool fun (a b : Bool) => @Eq Bool a b) (fun (a b : Bool) => instDecidableEqBool a b) (fun (n : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Bool.false))

-- USize.le_trans, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.le_trans.h3 : ¬∀ {a b c : USize}, b ≤ c → a ≤ c := fun hc_h => absurd (@hc_h (USize.ofNat 1) (USize.ofNat 0) (USize.ofNat 0) (by
  decide)) (by
  (simp <;> decide))

-- USize.le_trans, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.le_trans.h4 : ¬∀ {a b c : USize}, a ≤ b → a ≤ c := fun hc_h => absurd (@hc_h (USize.ofNat 1) (USize.ofNat 1) (USize.ofNat 0) (by
  simp)) (by
  (simp <;> decide))

-- ISize.lt_of_le_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ISize.lt_of_le_of_lt.h4 : ¬∀ {a b c : ISize}, a ≤ b → a < c := fun hc_h => absurd (@hc_h (ISize.ofInt 0) (ISize.ofInt 0) (ISize.ofInt 0) (by
  simp)) (by
  simp)

-- right_le_apply_maxOn, hypothesis 4: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.right_le_apply_maxOn.h4.inst : ¬False := by
  decide
theorem HypCheckProof.right_le_apply_maxOn.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {x y : α}, f y ≤ f (maxOn f x y) := fun hc_h => HypCheckProof.right_le_apply_maxOn.h4.inst (@hc_h (Bool) (Nat) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (fun (a b : Bool) => instDecidableFalse) (fun (n : Nat) => n % 2 == 0) (0) (0))

-- apply_minOn_le_left, hypothesis 4: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.apply_minOn_le_left.h4.inst : ¬False := by
  decide
theorem HypCheckProof.apply_minOn_le_left.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {f : α → β} {x y : α}, f (minOn f x y) ≤ f x := fun hc_h => HypCheckProof.apply_minOn_le_left.h4.inst (@hc_h (Bool) (Nat) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (fun (a b : Bool) => instDecidableFalse) (fun (n : Nat) => n % 2 == 0) (0) (0))

-- Vector.append_left_lt_iff, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.append_left_lt_iff.h4 : ¬∀ {α : Type} {n m : Nat} [inst : LT α] (xs : Vector α n) {ys ys' : Vector α m}, xs ++ ys < xs ++ ys' ↔ ys < ys' := fun hc_h => absurd (@hc_h (Nat) (1) (0) (⟨fun a b => a ≤ b⟩ : LT Nat) (#v[0]) (#v[]) (#v[])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Vector.findSome?_subtype, hypothesis 7: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.findSome?_subtype.h7 : ¬∀ {α : Type} {n : Nat} {β : Type} {p : α → Prop} {xs : Vector { x : α // p x } n} {f : { x : α // p x } → Option β}
        {g : α → Option β}, Vector.findSome? f xs = Vector.findSome? g xs.unattach := fun hc_h => absurd (@hc_h (Nat) (1) (Nat) (fun n => n = 0 : Nat → Prop) (#v[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Option.none) (some : Nat → Option Nat)) (by
  decide +kernel)

-- Option.max_le, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.max_le.h3 : ¬∀ {α : Type} [inst : LE α] [inst_1 : Max α] {a b c : Option α}, Max.max a b ≤ c ↔ a ≤ c ∧ b ≤ c := fun hc_h => absurd (@hc_h (Nat) (instLENat) (⟨fun a b => a - b⟩ : Max Nat) (Option.some 0) (Option.some 1) (Option.some 0)) (by
  simp)

-- Array.filterMap_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.filterMap_subtype.h6 : ¬∀ {α β : Type} {p : α → Prop} {xs : Array { x : α // p x }} {f : { x : α // p x } → Option β} {g : α → Option β},
        Array.filterMap f xs = Array.filterMap g xs.unattach := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n = 0 : Nat → Prop) (#[(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Option.none) (some : Nat → Option Nat)) (by
  decide +kernel)

-- Option.map_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.map_subtype.h6 : ¬∀ {α β : Type} {p : α → Prop} {o : Option { x : α // p x }} {f : { x : α // p x } → β} {g : α → β},
        Option.map f o = Option.map g o.unattach := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n = 0 : Nat → Prop) (Option.some (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => 0) (fun n => n + 1 : Nat → Nat)) (by
  decide)

-- Option.unattach_merge, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Option.unattach_merge.h4 : ¬∀ {α : Type} {p : α → Prop} {f : { x : α // p x } → { x : α // p x } → { x : α // p x }} {g : α → α → α}
        {o o' : Option { x : α // p x }}, (Option.merge f o o').unattach = Option.merge g o.unattach o'.unattach := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 = 0 : Nat → Prop) (fun (a a_1 : { x : Nat // (fun (n : Nat) => n % 2 = 0) x }) =>
      (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n % 2 = 0) x })) (fun a b => a - b : Nat → Nat → Nat) (Option.some (⟨2, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n % 2 = 0) x })) (Option.some (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n % 2 = 0) x }))) (by
  decide)

-- List.filterMap_subtype, hypothesis 6: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.filterMap_subtype.h6 : ¬∀ {α β : Type} {p : α → Prop} {l : List { x : α // p x }} {f : { x : α // p x } → Option β} {g : α → Option β},
        List.filterMap f l = List.filterMap g l.unattach := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Option.none) (some : Nat → Option Nat)) (by
  decide)

-- List.maxIdxOn?_eq_some_zero_iff, hypothesis 4: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.List.maxIdxOn?_eq_some_zero_iff.h4.inst : ¬(List.maxIdxOn? (fun (n : Nat) => n % 2 == 0) [0] = Option.some 0 ↔ ∃ (h : [0] ≠ []), ∀ (x : Nat), x ∈ [0] → False) := by
  decide
theorem HypCheckProof.List.maxIdxOn?_eq_some_zero_iff.h4 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] {xs : List α} {f : α → β},
        List.maxIdxOn? f xs = Option.some 0 ↔ ∃ (h : xs ≠ []), ∀ (x : α), x ∈ xs → f x ≤ f (xs.head h) := fun hc_h => HypCheckProof.List.maxIdxOn?_eq_some_zero_iff.h4.inst (@hc_h (Bool) (Nat) ({ le := fun (x x_1 : Bool) => False : LE Bool }) (fun (a b : Bool) => instDecidableFalse) ([0]) (fun (n : Nat) => n % 2 == 0))

-- USize.lt_of_le_of_ne, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.lt_of_le_of_ne.h3 : ¬∀ {a b : USize}, a ≤ b → a < b := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 0) (by
  decide)) (by
  decide)

-- USize.ofNatLT_lt_iff_lt, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.ofNatLT_lt_iff_lt.h2 : ¬∀ {a b : Nat}, b < USize.size → a < USize.size := fun hc_h => absurd (@hc_h (18446744073709551616) (0) (by
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

-- USize.ofNatLT_lt_iff_lt, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.ofNatLT_lt_iff_lt.h3 : ¬∀ {a b : Nat}, a < USize.size → b < USize.size := fun hc_h => absurd (@hc_h (0) (18446744073709551616) (by
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

-- USize.ofNatLT_sub, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.ofNatLT_sub.h2 : ¬∀ {a b : Nat}, b ≤ a → a < 2 ^ System.Platform.numBits := fun hc_h => absurd (@hc_h (18446744073709551616) (0) (by
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

-- USize.ofNat_le_iff_le, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.ofNat_le_iff_le.h2 : ¬∀ {a b : Nat}, b < USize.size → (USize.ofNat a ≤ USize.ofNat b ↔ a ≤ b) := fun hc_h => absurd (@hc_h (18446744073709551616) (0) (by
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

-- List.unattach_filter, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.unattach_filter.h5 : ¬∀ {α : Type} {p : α → Prop} {l : List { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        (List.filter f l).unattach = List.filter g l.unattach := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide)

-- List.find?_subtype, hypothesis 5: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.find?_subtype.h5 : ¬∀ {α : Type} {p : α → Prop} {l : List { x : α // p x }} {f : { x : α // p x } → Bool} {g : α → Bool},
        Option.map Subtype.val (List.find? f l) = List.find? g l.unattach := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) ([(⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x })]) (fun (a : { x : Nat // (fun (n : Nat) => n = 0) x }) => Bool.false) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide)

-- List.cons_lt_cons_self, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.cons_lt_cons_self.h3 : ¬∀ {α : Type} {a : α} [inst : LT α] {l₁ l₂ : List α}, a :: l₁ < a :: l₂ ↔ l₁ < l₂ := fun hc_h => absurd (@hc_h (Nat) (0) (⟨fun a b => a ≤ b⟩ : LT Nat) ([]) ([])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.append_left_lt_iff, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.append_left_lt_iff.h2 : ¬∀ {α : Type} [inst : LT α] (l₁ : List α) {l₂ l₃ : List α}, l₁ ++ l₂ < l₁ ++ l₃ ↔ l₂ < l₃ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) ([0]) ([]) ([])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.le_total, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.le_total.h2 : ¬∀ {α : Type} [inst : LT α] (l₁ l₂ : List α), l₁ ≤ l₂ ∨ l₂ ≤ l₁ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) ([0]) ([0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Array.le_total, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.le_total.h2 : ¬∀ {α : Type} [inst : LT α] (xs ys : Array α), xs ≤ ys ∨ ys ≤ xs := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (#[0]) (#[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- Vector.lt_irrefl, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Vector.lt_irrefl.h3 : ¬∀ {α : Type} {n : Nat} [inst : LT α] (xs : Vector α n), ¬xs < xs := fun hc_h => absurd (@hc_h (Nat) (1) (⟨fun a b => a ≤ b⟩ : LT Nat) (#v[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- List.getElem_unattach, hypothesis 4: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.List.getElem_unattach.h4 : ¬∀ {α : Type} {p : α → Prop} {l : List { x : α // p x }} (i : Nat), i < l.unattach.length := fun hc_h => absurd (@hc_h (Nat) (fun n => n = 0 : Nat → Prop) ([]) (0)) (by
  decide)

-- Array.mem_attachWith, hypothesis 3: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.mem_attachWith.h3 : ¬∀ {α : Type} {xs : Array α} {q : α → Prop} (x : { x : α // q x }) (x : α), x ∈ xs → q x := fun hc_h => absurd (@hc_h (Nat) (#[1]) (fun n => n = 0 : Nat → Prop) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : Nat // (fun (n : Nat) => n = 0) x }))) (by
  decide)

-- Array.le_refl, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Array.le_refl.h2 : ¬∀ {α : Type} [inst : LT α] (xs : Array α), xs ≤ xs := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (#[0])) (by
  (letI _hcd0 : @DecidableRel Nat Nat (@LT.lt Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)) :=
      fun (a b : Nat) => a.decLe b;
    decide))

-- USize.le_of_eq, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.le_of_eq.h2 : ¬∀ {a b : USize}, a ≤ b := fun hc_h => absurd (@hc_h (USize.ofNat 1) (USize.ofNat 0)) (by
  (simp <;> decide))

-- UInt16.toUSize_shiftLeft_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt16.toUSize_shiftLeft_of_lt.h2 : ¬∀ (a b : UInt16), (a <<< b).toUSize = a.toUSize <<< b.toUSize % 65536 := fun hc_h => absurd (@hc_h (UInt16.ofNat 1) (UInt16.ofNat 16)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- UInt8.toUSize_shiftLeft_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.UInt8.toUSize_shiftLeft_of_lt.h2 : ¬∀ (a b : UInt8), (a <<< b).toUSize = a.toUSize <<< b.toUSize % 256 := fun hc_h => absurd (@hc_h (UInt8.ofNat 1) (UInt8.ofNat 8)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.ofNat_shiftLeft, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.ofNat_shiftLeft.h2 : ¬∀ (a b : Nat), USize.ofNat (a <<< b) = USize.ofNat a <<< USize.ofNat b := fun hc_h => absurd (@hc_h (1) (64)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.toNat.inj, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.toNat.inj.h2 : ¬∀ {a b : USize}, a = b := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 1)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- ISize.toBitVec.inj, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.ISize.toBitVec.inj.h2 : ¬∀ {x y : ISize}, x = y := fun hc_h => absurd (@hc_h (ISize.ofInt 0) (ISize.ofInt 1)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.le_ofNat_iff, hypothesis 2: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.le_ofNat_iff.h2 : ¬∀ {n : USize} {m : Nat}, n ≤ USize.ofNat m ↔ n.toNat ≤ m := fun hc_h => absurd (@hc_h (USize.ofNat 1) (18446744073709551616)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.ofBitVec_ofNatLT, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.ofBitVec_ofNatLT.h1.inst : ¬18446744073709551616 < 2 ^ System.Platform.numBits := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.ofBitVec_ofNatLT.h1 : ¬∀ {n : Nat}, n < 2 ^ System.Platform.numBits := fun hc_h => HypCheckProof.USize.ofBitVec_ofNatLT.h1.inst (@hc_h (18446744073709551616))

-- USize.toBitVec_ofNatTruncate_of_lt, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.toBitVec_ofNatTruncate_of_lt.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.toBitVec_ofNatTruncate_of_lt.h1 : ¬∀ {n : Nat}, n < USize.size := fun hc_h => HypCheckProof.USize.toBitVec_ofNatTruncate_of_lt.h1.inst (@hc_h (18446744073709551616))

-- USize.toNat_ofNatLT, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.toNat_ofNatLT.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.toNat_ofNatLT.h1 : ¬∀ {n : Nat}, n < USize.size := fun hc_h => HypCheckProof.USize.toNat_ofNatLT.h1.inst (@hc_h (18446744073709551616))

-- USize.toUInt16_ofNatLT, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.toUInt16_ofNatLT.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.toUInt16_ofNatLT.h1 : ¬∀ {n : Nat}, n < USize.size := fun hc_h => HypCheckProof.USize.toUInt16_ofNatLT.h1.inst (@hc_h (18446744073709551616))

-- USize.ofFin_mk, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.ofFin_mk.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.ofFin_mk.h1 : ¬∀ {n : Nat}, n < USize.size := fun hc_h => HypCheckProof.USize.ofFin_mk.h1.inst (@hc_h (18446744073709551616))

-- USize.toNat_ofNat_of_lt, hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.USize.toNat_ofNat_of_lt.h1 : ¬∀ {n : Nat}, USize.toNat (OfNat.ofNat n) = n := fun hc_h => absurd (@hc_h (18446744073709551616)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- Int8.toISize_ofNat', hypothesis 1: necessary
set_option maxHeartbeats 40000 in
theorem HypCheckProof.Int8.toISize_ofNat'.h1 : ¬∀ {n : Nat}, (Int8.ofNat n).toISize = ISize.ofNat n := fun hc_h => absurd (@hc_h (128)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- USize.toFin_ofNatLT, hypothesis 1: necessary
set_option maxHeartbeats 2000 in
theorem HypCheckProof.USize.toFin_ofNatLT.h1.inst : ¬18446744073709551616 < USize.size := by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide)
theorem HypCheckProof.USize.toFin_ofNatLT.h1 : ¬∀ {n : Nat}, n < USize.size := fun hc_h => HypCheckProof.USize.toFin_ofNatLT.h1.inst (@hc_h (18446744073709551616))

