import Init

/-! Proofs emitted by HypCheck.lean (Lean 4.37.0, commit a2ec8251001440c7dda5f060c51276e369ef08b9). -/

-- List.max_map_eq_max, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.max_map_eq_max.h5 : ¬∀ {α β : Type} [inst : Max α] [inst_1 : LE α] [inst_2 : DecidableLE α] [inst_3 : Max β] [inst_4 : LE β]
        [inst_5 : DecidableLE β] [inst_6 : Std.IsLinearPreorder β] [inst_7 : Std.LawfulOrderLeftLeaningMax β] {f : α → β},
        (∀ (a b : α), f a ≤ f b ↔ a ≤ b) → ∀ {l : List α} {h : l ≠ []}, (List.map f l).max (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = f (l.max h) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (Nat) (⟨fun a b => a - b⟩ : Max Nat) (instLENat) (Nat.decLe) (Nat.instMax) (instLENat) (Nat.decLe) _ _ (fun n => n + 1 : Nat → Nat) hc_k0 ([0, 1]) hc_k1) (by
  simp)

-- List.max_map_eq_max, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.max_map_eq_max.h10 : ¬∀ {α β : Type} [inst : Max α] [inst_1 : LE α] [inst_2 : DecidableLE α] [inst_3 : Std.LawfulOrderLeftLeaningMax α]
        [inst_4 : Max β] [inst_5 : LE β] [inst_6 : DecidableLE β] [inst_7 : Std.IsLinearPreorder β] {f : α → β},
        (∀ (a b : α), f a ≤ f b ↔ a ≤ b) → ∀ {l : List α} {h : l ≠ []}, (List.map f l).max (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = f (l.max h) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (Nat) (Nat.instMax) (instLENat) (Nat.decLe) _ (⟨fun a b => a - b⟩ : Max Nat) (instLENat) (Nat.decLe) _ (fun n => n + 1 : Nat → Nat) hc_k0 ([0, 1]) hc_k1) (by
  simp)

-- List.max_map_eq_max, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.max_map_eq_max.h12 : ¬∀ {α β : Type} [inst : Max α] [inst_1 : LE α] [inst_2 : DecidableLE α] [inst_3 : Std.LawfulOrderLeftLeaningMax α]
        [inst_4 : Max β] [inst_5 : LE β] [inst_6 : DecidableLE β] [inst_7 : Std.IsLinearPreorder β]
        [inst_8 : Std.LawfulOrderLeftLeaningMax β] {f : α → β} {l : List α} {h : l ≠ []},
        (List.map f l).max (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = f (l.max h) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Bool) (Nat.instMax) (instLENat) (Nat.decLe) _ (Bool.instMax) (Bool.instLE) (Bool.instDecidableLe) (@Std.IsLinearPreorder.mk (Bool) (Bool.instLE) (@Std.IsPreorder.mk (Bool) (Bool.instLE) (by (try dsimp only);   decide) (by (try dsimp only);   decide)) (by (try dsimp only);   decide)) (@Std.LawfulOrderLeftLeaningMax.mk (Bool) (Bool.instMax) (Bool.instLE) (by (try dsimp only);   decide) (by (try dsimp only);   decide)) (fun n => n % 2 == 0 : Nat → Bool) ([0, 1]) hc_k0) (by
  decide)

-- Vector.lex_eq_false_iff_exists, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.lex_eq_false_iff_exists.h5 : ¬∀ {α : Type} {n : Nat} [inst : BEq α] [inst_1 : PartialEquivBEq α] (lt : α → α → Bool),
        (∀ (x y : α), lt x y = Bool.true → lt y x = Bool.false) →
          (∀ (x y : α), lt x y = Bool.false → lt y x = Bool.false → (x == y) = Bool.true) →
            ∀ {xs ys : Vector α n},
              xs.lex ys lt = Bool.false ↔
                (ys.isEqv xs fun (x1 x2 : α) => x1 == x2) = Bool.true ∨
                  ∃ (i : Nat),
                    ∃ (h : i < n), (∀ (j : Nat) (hj : j < i), (xs[j] == ys[j]) = Bool.true) ∧ lt ys[i] xs[i] = Bool.true := fun hc_h => absurd (@hc_h (Nat) (1) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (@PartialEquivBEq.mk (Nat) (@BEq.mk Nat fun (a b : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done))) (fun a b => a < b : Nat → Nat → Bool) (by
  grind) (by
  grind) (#v[0]) (#v[1])) (by
  decide)

-- Vector.set_comm, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.set_comm.h9 : ¬∀ {α : Type} {n i j : Nat} (a b : α) {xs : Vector α n} {hi : i < n} {hj : j < n},
        (xs.set i a hi).set j b hj = (xs.set j b hj).set i a hi := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (1) (0) (0) (0) (1) (#v[0]) hc_k0 hc_k1) (by
  decide)

-- List.min_map, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.min_map.h6 : ¬∀ {β α : Type} [inst : LE β] [inst_1 : DecidableLE β] [inst_2 : Min β] [inst_3 : Std.IsLinearPreorder β] {xs : List α}
        {f : α → β} (h : xs ≠ []), (List.map f xs).min (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = f (List.minOn f xs h) := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (Nat) (instLENat) (Nat.decLe) (⟨fun a b => a - b⟩ : Min Nat) _ ([0, 1]) (fun n => n + 1 : Nat → Nat) hc_k0) (by
  decide)

-- Vector.set_eraseIdx_gt, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Vector.set_eraseIdx_gt.h8.{u_1} : ∀ {α : Type u_1} {n : Nat} {xs : Vector α n} {i : Nat} {w : i < n} {j : Nat} {a : α}, j < i → j < n - 1 := by
  (intros; omega)

-- Array.getElem_set_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.getElem_set_ne.h7 : ¬∀ {α : Type} {xs : Array α} {i : Nat} (h' : i < xs.size) {v : α} {j : Nat} (pj : j < xs.size),
        GetElem.getElem (xs.set i v h') j (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = GetElem.getElem xs j pj := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (#[0]) (0) hc_k0 (1) (0) hc_k1) (by
  decide)

-- List.min?_eq_some_iff_subtype, hypothesis 6: necessary
/- FAILED: 80:2: failed to synthesize
  Decidable ¬([false].min? = some false ↔ false ∈ [false] ∧ ∀ (b : Bool), b ∈ [false] → false ≤ b)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 87:2: failed to synthesize
  Decidable ¬([false].min? = some false ↔ false ∈ [false] ∧ ∀ (b : Bool), b ∈ [false] → false ≤ b)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 80:2: failed to synthesize
  Decidable ¬([false].min? = some false ↔ false ∈ [false] ∧ ∀ (b : Bool), b ∈ [false] → false ≤ b)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 87:2: failed to synthesize
  Decidable ¬([false].min? = some false ↔ false ∈ [false] ∧ ∀ (b : Bool), b ∈ [false] → false ≤ b)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 5:63: failed to synthesize instance of type class
  Min { x // x ∈ [false] }

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 115:78: (deterministic) timeout at `elaborator`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 5:63: failed to synthesize instance of type class
  Min { x // x ∈ [false] }

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 17:144: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.min?_eq_some_iff_subtype.h6 : ¬∀ {α : Type} {a : α} [inst : Min α] [inst_1 : LE α] {xs : List α} [inst_2 : Std.MinEqOr α]
        [inst_3 : Std.LawfulOrderMin { x : α // x ∈ xs }], xs.min? = Option.some a ↔ a ∈ xs ∧ ∀ (b : α), b ∈ xs → a ≤ b := fun hc_h => absurd (@hc_h (Bool) (Bool.false) (Bool.instMin) (⟨fun _ _ => False⟩ : LE Bool) ([Bool.false]) (@Std.MinEqOr.mk (Bool) (Bool.instMin) (by (try dsimp only);   decide)) ((@Std.LawfulOrderMin.mk (@Subtype Bool fun (x : Bool) =>
      @Membership.mem Bool (List Bool) (@List.instMembership Bool) (@List.cons Bool Bool.false (@List.nil Bool)) x) (@Subtype.instMin Bool Bool.instMin
      (@Std.MinEqOr.mk Bool Bool.instMin
        (@of_decide_eq_true
          (∀ (a b : Bool), Or (@Eq Bool (@Min.min Bool Bool.instMin a b) a) (@Eq Bool (@Min.min Bool Bool.instMin a b) b))
          (@Bool.instDecidableForallOfDecidablePred
            (fun (a : Bool) =>
              ∀ (b : Bool), Or (@Eq Bool (@Min.min Bool Bool.instMin a b) a) (@Eq Bool (@Min.min Bool Bool.instMin a b) b))
            fun (a : Bool) =>
            @Bool.instDecidableForallOfDecidablePred
              (fun (b : Bool) =>
                Or (@Eq Bool (@Min.min Bool Bool.instMin a b) a) (@Eq Bool (@Min.min Bool Bool.instMin a b) b))
              fun (a_1 : Bool) =>
              @instDecidableOr (@Eq Bool (@Min.min Bool Bool.instMin a a_1) a)
                (@Eq Bool (@Min.min Bool Bool.instMin a a_1) a_1) (instDecidableEqBool (@Min.min Bool Bool.instMin a a_1) a)
                (instDecidableEqBool (@Min.min Bool Bool.instMin a a_1) a_1))
          (@id
            (@Eq Bool
              (@Decidable.decide
                (∀ (a b : Bool),
                  Or (@Eq Bool (@Min.min Bool Bool.instMin a b) a) (@Eq Bool (@Min.min Bool Bool.instMin a b) b))
                (@Bool.instDecidableForallOfDecidablePred
                  (fun (a : Bool) =>
                    ∀ (b : Bool),
                      Or (@Eq Bool (@Min.min Bool Bool.instMin a b) a) (@Eq Bool (@Min.min Bool Bool.instMin a b) b))
                  fun (a : Bool) =>
                  @Bool.instDecidableForallOfDecidablePred
                    (fun (b : Bool) =>
                      Or (@Eq Bool (@Min.min Bool Bool.instMin a b) a) (@Eq Bool (@Min.min Bool Bool.instMin a b) b))
                    fun (a_1 : Bool) =>
                    @instDecidableOr (@Eq Bool (@Min.min Bool Bool.instMin a a_1) a)
                      (@Eq Bool (@Min.min Bool Bool.instMin a a_1) a_1)
                      (instDecidableEqBool (@Min.min Bool Bool.instMin a a_1) a)
                      (instDecidableEqBool (@Min.min Bool Bool.instMin a a_1) a_1)))
              Bool.true)
            (@Eq.refl Bool Bool.true))))
      fun (x : Bool) =>
      @Membership.mem Bool (List Bool) (@List.instMembership Bool) (@List.cons Bool Bool.false (@List.nil Bool)) x) (@Subtype.instLE Bool (@LE.mk Bool fun (x x_1 : Bool) => False) fun (x : Bool) =>
      @Membership.mem Bool (List Bool) (@List.instMembership Bool) (@List.cons Bool Bool.false (@List.nil Bool)) x) inferInstance (@Std.LawfulOrderInf.mk (@Subtype Bool fun (x : Bool) =>
      @Membership.mem Bool (List Bool) (@List.instMembership Bool) (@List.cons Bool Bool.false (@List.nil Bool)) x) (@Subtype.instMin Bool Bool.instMin
      (@Std.MinEqOr.mk Bool Bool.instMin
        (@of_decide_eq_true
          (∀ (a b : Bool), Or (@Eq Bool (@Min.min Bool Bool.instMin a b) a) (@Eq Bool (@Min.min Bool Bool.instMin a b) b))
          (@Bool.instDecidableForallOfDecidablePred
            (fun (a : Bool) =>
              ∀ (b : Bool), Or (@Eq Bool (@Min.min Bool Bool.instMin a b) a) (@Eq Bool (@Min.min Bool Bool.instMin a b) b))
            fun (a : Bool) =>
            @Bool.instDecidableForallOfDecidablePred
              (fun (b : Bool) =>
                Or (@Eq Bool (@Min.min Bool Bool.instMin a b) a) (@Eq Bool (@Min.min Bool Bool.instMin a b) b))
              fun (a_1 : Bool) =>
              @instDecidableOr (@Eq Bool (@Min.min Bool Bool.instMin a a_1) a)
                (@Eq Bool (@Min.min Bool Bool.instMin a a_1) a_1) (instDecidableEqBool (@Min.min Bool Bool.instMin a a_1) a)
                (instDecidableEqBool (@Min.min Bool Bool.instMin a a_1) a_1))
          (@id
            (@Eq Bool
              (@Decidable.decide
                (∀ (a b : Bool),
                  Or (@Eq Bool (@Min.min Bool Bool.instMin a b) a) (@Eq Bool (@Min.min Bool Bool.instMin a b) b))
                (@Bool.instDecidableForallOfDecidablePred
                  (fun (a : Bool) =>
                    ∀ (b : Bool),
                      Or (@Eq Bool (@Min.min Bool Bool.instMin a b) a) (@Eq Bool (@Min.min Bool Bool.instMin a b) b))
                  fun (a : Bool) =>
                  @Bool.instDecidableForallOfDecidablePred
                    (fun (b : Bool) =>
                      Or (@Eq Bool (@Min.min Bool Bool.instMin a b) a) (@Eq Bool (@Min.min Bool Bool.instMin a b) b))
                    fun (a_1 : Bool) =>
                    @instDecidableOr (@Eq Bool (@Min.min Bool Bool.instMin a a_1) a)
                      (@Eq Bool (@Min.min Bool Bool.instMin a a_1) a_1)
                      (instDecidableEqBool (@Min.min Bool Bool.instMin a a_1) a)
                      (instDecidableEqBool (@Min.min Bool Bool.instMin a a_1) a_1)))
              Bool.true)
            (@Eq.refl Bool Bool.true))))
      fun (x : Bool) =>
      @Membership.mem Bool (List Bool) (@List.instMembership Bool) (@List.cons Bool Bool.false (@List.nil Bool)) x) (@Subtype.instLE Bool (@LE.mk Bool fun (x x_1 : Bool) => False) fun (x : Bool) =>
      @Membership.mem Bool (List Bool) (@List.instMembership Bool) (@List.cons Bool Bool.false (@List.nil Bool)) x) (by (try dsimp only);   grind))))) (by
  decide)
-/

-- List.max?_eq_some_iff_subtype, hypothesis 6: necessary
/- FAILED: 80:2: failed to synthesize
  Decidable ¬([false].max? = some false ↔ false ∈ [false] ∧ ∀ (b : Bool), b ∈ [false] → b ≤ false)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 87:2: failed to synthesize
  Decidable ¬([false].max? = some false ↔ false ∈ [false] ∧ ∀ (b : Bool), b ∈ [false] → b ≤ false)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 80:2: failed to synthesize
  Decidable ¬([false].max? = some false ↔ false ∈ [false] ∧ ∀ (b : Bool), b ∈ [false] → b ≤ false)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 87:2: failed to synthesize
  Decidable ¬([false].max? = some false ↔ false ∈ [false] ∧ ∀ (b : Bool), b ∈ [false] → b ≤ false)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 5:63: failed to synthesize instance of type class
  Max { x // x ∈ [false] }

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 115:87: (deterministic) timeout at `elaborator`, maximum number of heartbeats (300) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 5:63: failed to synthesize instance of type class
  Max { x // x ∈ [false] }

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 17:144: `grind` has failed, use `+verbose` to obtain diagnostic information
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.max?_eq_some_iff_subtype.h6 : ¬∀ {α : Type} {a : α} [inst : Max α] [inst_1 : LE α] {xs : List α} [inst_2 : Std.MaxEqOr α]
        [inst_3 : Std.LawfulOrderMax { x : α // x ∈ xs }], xs.max? = Option.some a ↔ a ∈ xs ∧ ∀ (b : α), b ∈ xs → b ≤ a := fun hc_h => absurd (@hc_h (Bool) (Bool.false) (Bool.instMax) (⟨fun _ _ => False⟩ : LE Bool) ([Bool.false]) (@Std.MaxEqOr.mk (Bool) (Bool.instMax) (by (try dsimp only);   decide)) ((@Std.LawfulOrderMax.mk (@Subtype Bool fun (x : Bool) =>
      @Membership.mem Bool (List Bool) (@List.instMembership Bool) (@List.cons Bool Bool.false (@List.nil Bool)) x) (@Subtype.instMax Bool Bool.instMax
      (@Std.MaxEqOr.mk Bool Bool.instMax
        (@of_decide_eq_true
          (∀ (a b : Bool), Or (@Eq Bool (@Max.max Bool Bool.instMax a b) a) (@Eq Bool (@Max.max Bool Bool.instMax a b) b))
          (@Bool.instDecidableForallOfDecidablePred
            (fun (a : Bool) =>
              ∀ (b : Bool), Or (@Eq Bool (@Max.max Bool Bool.instMax a b) a) (@Eq Bool (@Max.max Bool Bool.instMax a b) b))
            fun (a : Bool) =>
            @Bool.instDecidableForallOfDecidablePred
              (fun (b : Bool) =>
                Or (@Eq Bool (@Max.max Bool Bool.instMax a b) a) (@Eq Bool (@Max.max Bool Bool.instMax a b) b))
              fun (a_1 : Bool) =>
              @instDecidableOr (@Eq Bool (@Max.max Bool Bool.instMax a a_1) a)
                (@Eq Bool (@Max.max Bool Bool.instMax a a_1) a_1) (instDecidableEqBool (@Max.max Bool Bool.instMax a a_1) a)
                (instDecidableEqBool (@Max.max Bool Bool.instMax a a_1) a_1))
          (@id
            (@Eq Bool
              (@Decidable.decide
                (∀ (a b : Bool),
                  Or (@Eq Bool (@Max.max Bool Bool.instMax a b) a) (@Eq Bool (@Max.max Bool Bool.instMax a b) b))
                (@Bool.instDecidableForallOfDecidablePred
                  (fun (a : Bool) =>
                    ∀ (b : Bool),
                      Or (@Eq Bool (@Max.max Bool Bool.instMax a b) a) (@Eq Bool (@Max.max Bool Bool.instMax a b) b))
                  fun (a : Bool) =>
                  @Bool.instDecidableForallOfDecidablePred
                    (fun (b : Bool) =>
                      Or (@Eq Bool (@Max.max Bool Bool.instMax a b) a) (@Eq Bool (@Max.max Bool Bool.instMax a b) b))
                    fun (a_1 : Bool) =>
                    @instDecidableOr (@Eq Bool (@Max.max Bool Bool.instMax a a_1) a)
                      (@Eq Bool (@Max.max Bool Bool.instMax a a_1) a_1)
                      (instDecidableEqBool (@Max.max Bool Bool.instMax a a_1) a)
                      (instDecidableEqBool (@Max.max Bool Bool.instMax a a_1) a_1)))
              Bool.true)
            (@Eq.refl Bool Bool.true))))
      fun (x : Bool) =>
      @Membership.mem Bool (List Bool) (@List.instMembership Bool) (@List.cons Bool Bool.false (@List.nil Bool)) x) (@Subtype.instLE Bool (@LE.mk Bool fun (x x_1 : Bool) => False) fun (x : Bool) =>
      @Membership.mem Bool (List Bool) (@List.instMembership Bool) (@List.cons Bool Bool.false (@List.nil Bool)) x) inferInstance (@Std.LawfulOrderSup.mk (@Subtype Bool fun (x : Bool) =>
      @Membership.mem Bool (List Bool) (@List.instMembership Bool) (@List.cons Bool Bool.false (@List.nil Bool)) x) (@Subtype.instMax Bool Bool.instMax
      (@Std.MaxEqOr.mk Bool Bool.instMax
        (@of_decide_eq_true
          (∀ (a b : Bool), Or (@Eq Bool (@Max.max Bool Bool.instMax a b) a) (@Eq Bool (@Max.max Bool Bool.instMax a b) b))
          (@Bool.instDecidableForallOfDecidablePred
            (fun (a : Bool) =>
              ∀ (b : Bool), Or (@Eq Bool (@Max.max Bool Bool.instMax a b) a) (@Eq Bool (@Max.max Bool Bool.instMax a b) b))
            fun (a : Bool) =>
            @Bool.instDecidableForallOfDecidablePred
              (fun (b : Bool) =>
                Or (@Eq Bool (@Max.max Bool Bool.instMax a b) a) (@Eq Bool (@Max.max Bool Bool.instMax a b) b))
              fun (a_1 : Bool) =>
              @instDecidableOr (@Eq Bool (@Max.max Bool Bool.instMax a a_1) a)
                (@Eq Bool (@Max.max Bool Bool.instMax a a_1) a_1) (instDecidableEqBool (@Max.max Bool Bool.instMax a a_1) a)
                (instDecidableEqBool (@Max.max Bool Bool.instMax a a_1) a_1))
          (@id
            (@Eq Bool
              (@Decidable.decide
                (∀ (a b : Bool),
                  Or (@Eq Bool (@Max.max Bool Bool.instMax a b) a) (@Eq Bool (@Max.max Bool Bool.instMax a b) b))
                (@Bool.instDecidableForallOfDecidablePred
                  (fun (a : Bool) =>
                    ∀ (b : Bool),
                      Or (@Eq Bool (@Max.max Bool Bool.instMax a b) a) (@Eq Bool (@Max.max Bool Bool.instMax a b) b))
                  fun (a : Bool) =>
                  @Bool.instDecidableForallOfDecidablePred
                    (fun (b : Bool) =>
                      Or (@Eq Bool (@Max.max Bool Bool.instMax a b) a) (@Eq Bool (@Max.max Bool Bool.instMax a b) b))
                    fun (a_1 : Bool) =>
                    @instDecidableOr (@Eq Bool (@Max.max Bool Bool.instMax a a_1) a)
                      (@Eq Bool (@Max.max Bool Bool.instMax a a_1) a_1)
                      (instDecidableEqBool (@Max.max Bool Bool.instMax a a_1) a)
                      (instDecidableEqBool (@Max.max Bool Bool.instMax a a_1) a_1)))
              Bool.true)
            (@Eq.refl Bool Bool.true))))
      fun (x : Bool) =>
      @Membership.mem Bool (List Bool) (@List.instMembership Bool) (@List.cons Bool Bool.false (@List.nil Bool)) x) (@Subtype.instLE Bool (@LE.mk Bool fun (x x_1 : Bool) => False) fun (x : Bool) =>
      @Membership.mem Bool (List Bool) (@List.instMembership Bool) (@List.cons Bool Bool.false (@List.nil Bool)) x) (by (try dsimp only);   grind))))) (by
  decide)
-/

-- Vector.getElem_eraseIdx_of_ge, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Vector.getElem_eraseIdx_of_ge.h4.{u_1} : ∀ {α : Type u_1} {n : Nat} {xs : Vector α n} {i j : Nat}, j < n - 1 → i ≤ j → i < n := by
  (intros; omega)

-- List.filterMapM_toArray', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.filterMapM_toArray'.h5 : ¬∀ {m : Type → Type} {α β : Type} {stop : Nat} [inst : Monad m] {l : List α} {f : α → m (Option β)},
        stop = l.length → Array.filterMapM f l.toArray 0 stop = List.toArray <$> List.filterMapM f l := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) ([].length) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) ([]) (fun (a : Nat) => (0, Option.none)) rfl) (by
  decide)

-- List.Nodup.getElem_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.getElem_inj.h4 : ¬∀ {α : Type} {i j : Nat} {xs : List α} {hi : i < xs.length} {hj : j < xs.length}, xs[i] = xs[j] ↔ i = j := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (0) (1) ([0, 0]) hc_k0 hc_k1) (by
  decide)

-- Array.getElem_eraseIdx_of_ge, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.getElem_eraseIdx_of_ge.h6 : ¬∀ {α : Type} {xs : Array α} {i : Nat} (w : i < xs.size) {j : Nat} (h : j < (xs.eraseIdx i w).size),
        GetElem.getElem (xs.eraseIdx i w) j h = GetElem.getElem xs (j + 1) (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (#[0, 1]) (1) hc_k0 (0) hc_k1) (by
  decide +kernel)

-- Array.getElem_eraseIdx_of_lt, hypothesis 5: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Array.getElem_eraseIdx_of_lt.h5.{u_1} : ∀ {α : Type u_1} {xs : Array α} {i : Nat} (w : i < xs.size) {j : Nat}, j < i → j < (xs.eraseIdx i w).size := by
  (intros; grind)

-- List.getElem_inj, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_inj.h6 : ¬∀ {α : Type} {i j : Nat} {xs : List α} {h₀ : i < xs.length} {h₁ : j < xs.length}, xs[i] = xs[j] ↔ i = j := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (0) (1) ([0, 0]) hc_k0 hc_k1) (by
  decide)

-- Array.foldr_induction, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.foldr_induction.h5 : ¬∀ {α β : Type} {as : Array α} (motive : Nat → β → Prop) {init : β} {f : α → β → β},
        (∀ (i : Fin as.size) (b : β), motive (↑i + 1) b → motive (↑i) (f as[i] b)) → motive 0 (Array.foldr f init as) := fun hc_h => absurd (@hc_h (Nat) (Nat) (#[]) (fun a b => a < b : Nat → Nat → Prop) (0) (fun a b => a - b : Nat → Nat → Nat) (by
  grind)) (by
  decide)

-- Vector.eraseIdx_append_of_lt_size, hypothesis 7: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Vector.eraseIdx_append_of_lt_size.h7.der.{u_1} : ∀ {α : Type u_1} {n m : Nat} {xs : Vector α n} {k : Nat}, k < n → ∀ (xs' : Vector α m), k < n + m := by
  (intros; omega)
theorem HypCheckProof.Vector.eraseIdx_append_of_lt_size.h7.{u_1} : ∀ {α : Type u_1} {n m : Nat} {xs : Vector α n} {k : Nat} (hk : k < n) (xs' : Vector α m),
      (xs ++ xs').eraseIdx k (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = Vector.cast (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) (xs.eraseIdx k hk ++ xs') := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Vector.eraseIdx_append_of_lt_size hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.Vector.eraseIdx_append_of_lt_size.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6)

