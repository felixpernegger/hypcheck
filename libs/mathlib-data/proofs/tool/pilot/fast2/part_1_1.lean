import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- List.SortedLT.getElem_lt_getElem_of_lt, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.getElem_lt_getElem_of_lt.h7 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedLT → ∀ ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄, i < j → j < l.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) (Nat.instPreorder) (by
  decide) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.MapsTo.prodMap, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.prodMap.h11 : ¬∀ {α₁ α₂ β₁ β₂ : Type} {s₁ : Set α₁} {s₂ : Set α₂} {t₁ : Set β₁} {t₂ : Set β₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂},
        Set.MapsTo f₁ s₁ t₁ → Set.MapsTo (fun (x : α₁ × α₂) => (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- List.pairwise_cons_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwise_cons_of_mem.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a b : α} [inst : IsTrans α R],
        b ∈ l → (List.Pairwise R (a :: l) ↔ R a b ∧ List.Pairwise R l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0, 1]) (0) (1) _ (by
  decide)) (by
  decide +kernel)

-- List.IsPrefix.idxOf_eq_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.idxOf_eq_of_mem.h7 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α],
        l₁ <+: l₂ → ∀ {a : α}, List.idxOf a l₁ = List.idxOf a l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (instBEqOfDecidableEq) _ (by
  decide) (1)) (by
  decide +kernel)

-- Fintype.card_compl_eq_card_compl, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_compl_eq_card_compl.h8 : ¬∀ {α : Type} [inst : Finite α] (p q : α → Prop) [inst : Fintype { x : α // p x }] [inst : Fintype { x : α // ¬p x }]
        [inst_1 : Fintype { x : α // q x }] [inst_2 : Fintype { x : α // ¬q x }],
        Fintype.card { x : α // ¬p x } = Fintype.card { x : α // ¬q x } := fun hc_h => absurd (@hc_h (Bool) _ (fun b => b = true : Bool → Prop) (fun _ => False : Bool → Prop) (Fintype.subtypeEq Bool.true) (Subtype.fintype fun (x : Bool) => ¬(fun (b : Bool) => b = Bool.true) x) (Subtype.fintype fun (x : Bool) => False) (Subtype.fintype fun (x : Bool) => ¬(fun (x : Bool) => False) x)) (by
  decide +kernel)

-- List.SortedLT.eq_of_mem_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.eq_of_mem_iff.h5 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁.SortedLT → (∀ (a : α), a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0]) ([0, 0]) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- EReal.mul_le_of_forall_lt_of_nonneg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.mul_le_of_forall_lt_of_nonneg.h4 : ¬∀ {a b c : EReal}, 0 ≤ a → (∀ a' ∈ Set.Ioo 0 a, ∀ b' ∈ Set.Ioo 0 b, a' * b' ≤ c) → a * b ≤ c := fun hc_h => absurd (@hc_h (0) (0) (⊥) (by
  rfl) (by
  simp)) (by
  decide +kernel)

-- Nat.bitwise_bit', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bitwise_bit'.h6 : ¬∀ {f : Bool → Bool → Bool} (a : Bool) (m : ℕ) (b : Bool) (n : ℕ),
        (m = 0 → a = Bool.true) → Nat.bitwise f (Nat.bit a m) (Nat.bit b n) = Nat.bit (f a b) (Nat.bitwise f m n) := fun hc_h => absurd (@hc_h (fun a b => !a || b : Bool → Bool → Bool) (Bool.false) (1) (Bool.false) (0) (by
  decide)) (by
  decide +kernel)

-- Set.SurjOn.mapsTo_compl, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.mapsTo_compl.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.SurjOn f s t → Set.MapsTo f sᶜ tᶜ := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({b : Bool | b = Bool.true}) ({n : ℕ | n = 0}) (fun _ => 0 : Bool → ℕ) (by
  simp)) (by
  simp)

-- Nat.factorization_choose_prime_pow_add_factorization, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose_prime_pow_add_factorization.h4 : ¬∀ {p n k : ℕ}, Nat.Prime p → k ≠ 0 → ((p ^ n).choose k).factorization p + k.factorization p = n := fun hc_h => absurd (@hc_h (2) (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.mem_of_subset_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_of_subset_of_mem.h4 : ¬∀ {α : Type} {s₁ s₂ : Set α} {a : α}, a ∈ s₁ → a ∈ s₂ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (0) (by
  decide)) (by
  decide +kernel)

-- Disjoint.notMem_of_mem_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.notMem_of_mem_left.h5 : ¬∀ {α : Type} {s t : Set α}, Disjoint s t → ∀ ⦃a : α⦄, a ∉ t := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp) (0)) (by
  decide +kernel)

-- ENat.add_lt_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.add_lt_add.h5 : ¬∀ {a b c d : ℕ∞}, a < c → a + b < c + d := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Function.Injective.existsUnique_of_mem_range, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.existsUnique_of_mem_range.h5 : ¬∀ {α β : Type} {f : α → β}, Function.Injective f → ∀ {b : β}, ∃! a : α, f a = b := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) (2)) (by
  nofun)

-- Fin.val_sub_castPred_of_ge, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_sub_castPred_of_ge.h4 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, b ≠ Fin.last n → a ≤ b := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Valid.right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid.right.h6 : ¬∀ {α : Type} [inst : Preorder α] {s : ℕ} {l : Ordnode α} {x : α} {r : Ordnode α}, r.Valid := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (0) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil)) (by
  nofun)

-- Nat.digitsAux_def, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digitsAux_def.h3 : ¬∀ (b : ℕ) (h : 2 ≤ b) (n : ℕ), b.digitsAux h n = n % b :: b.digitsAux h (n / b) := fun hc_h => absurd (fun hc_k0 => @hc_h (2) hc_k0 (0)) (by
  decide +kernel)

-- Function.Injective.invOfMemRange_surjective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.invOfMemRange_surjective.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst : DecidableEq β] {f : α → β}, Function.Injective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (instDecidableEqNat) (fun _ => 0 : Bool → ℕ)) (by
  decide +kernel)

-- Function.Injective.preimage_image, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.preimage_image.h3 : ¬∀ {α β : Type} {f : α → β} (s : Set α), f ⁻¹' f '' s = s := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ => 0 : Bool → ℕ) ({b : Bool | b = Bool.true})) (by
  simp)

-- Disjoint.inter_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.inter_eq.h3 : ¬∀ {α : Type} {s t : Set α}, s ∩ t = ∅ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- Set.encard_pair, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_pair.h3 : Not
      (∀ {α : Type} {x y : α},
        @Eq ENat
          (@Set.encard α
            (@Insert.insert α (Set α) (@Set.instInsert α) x (@Singleton.singleton α (Set α) (@Set.instSingletonSet α) y)))
          (@OfNat.ofNat ENat (nat_lit 2)
            (@instOfNatAtLeastTwo ENat (nat_lit 2) ENat.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  simp)

-- List.exists_of_length_succ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.exists_of_length_succ.h3 : ¬∀ {α : Type} {n : ℕ} (l : List α), ∃ (h : α) (t : List α), l = h :: t := fun hc_h => absurd (@hc_h (ℕ) (0) ([])) (by
  simp)

-- List.SortedLT.reverse, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.reverse.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.reverse.SortedGT := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- Set.Nontrivial.pair_subset, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.pair_subset.h2 : ¬∀ {α : Type} {s : Set α}, ∃ (x : α) (y : α), x ≠ y ∧ {x, y} ⊆ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Set.eq_univ_of_univ_subset, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_univ_of_univ_subset.h2 : ¬∀ {α : Type} {s : Set α}, s = Set.univ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Set.Nonempty.encard_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.encard_pos.h2 : ¬∀ {α : Type} {s : Set α}, 0 < s.encard := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

