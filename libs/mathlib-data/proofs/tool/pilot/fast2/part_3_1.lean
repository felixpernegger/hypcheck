import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Finset.mulAntidiagonal_mono_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mulAntidiagonal_mono_right.h3 : ¬∀ {α : Type} [inst : CommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO} {a : α}
        {u : Set α} {hu : u.IsPWO}, u ⊆ t → IsOrderedCancelMonoid α := fun hc_h => absurd (@hc_h (Bool) (BooleanRing.toCommRing.toCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (Bool.false) ({b : Bool | b = Bool.true}) (by
  simp) (by
  rfl)) (by
  exact fun hc_c =>
    absurd
      (hc_c.le_of_mul_le_mul_left (Bool.false : Bool) (Bool.true : Bool) (Bool.false : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.IsChain.cons_induction, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons_induction.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a : α} (p : α → Prop) (l : List α), List.IsChain r (a :: l) → p a → ∀ i ∈ l, p i := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (fun n => n = 0 : ℕ → Prop) ([1]) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1) (by
  decide)) (by
  decide +kernel)

-- Finsupp.nonTorsionWeight_of, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.nonTorsionWeight_of.h9 : ¬∀ {σ M : Type} (R : Type) [inst : Semiring R] (w : σ → M) [inst_1 : AddCommMonoid M] [inst_2 : Module R M]
        [inst_3 : IsDomain R] [inst_4 : Module.IsTorsionFree R M], Finsupp.NonTorsionWeight R w := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instSemiring) (fun _ => 0 : ℕ → ℕ) (Nat.instAddCommMonoid) (Semiring.toModule) _ _) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_zero_of_smul_eq_zero (r := (1 : ℕ)) (s := (0 : ℕ))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.next_cons_cons_eq', hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.next_cons_cons_eq'.h6.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y z : α), x = y → x ∈ y :: z :: l := by
  (intros; simp_all; done)
theorem HypCheckProof.List.next_cons_cons_eq'.h6.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y z : α) (hx : x = y),
      (y :: z :: l).next x (HypCheckProof.List.next_cons_cons_eq'.h6.der l x y z hx) = z := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @List.next_cons_cons_eq' hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.List.next_cons_cons_eq'.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6) hc_x6

-- StrictMono.codRestrict, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictMono.codRestrict.h5 : ¬∀ {α β : Type} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β} {s : Set β} (hs : ∀ (x : α), f x ∈ s),
        StrictMono (Set.codRestrict f s hs) := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (ℕ) (Bool.instPartialOrder.toPreorder) (Nat.instPreorder) (fun _ => 0 : Bool → ℕ) ({n : ℕ | n = 0}) hc_k0) (by
  decide +kernel)

-- List.Nodup.union, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.union.h3 : ¬∀ {α : Type} {l₂ : List α} [inst : BEq α] (l₁ : List α), l₂.Nodup → (l₁ ∪ l₂).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0]) (⟨fun a b => a != b⟩ : BEq ℕ) ([0]) (by
  decide)) (by
  decide +kernel)

-- Rat.mk_num_ne_zero_of_ne_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.mk_num_ne_zero_of_ne_zero.h4 : ¬∀ {q : ℚ} {n : ℤ} {d : ℤ}, q ≠ 0 → n ≠ 0 := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- List.relationReflTransGen_of_exists_isChain, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.relationReflTransGen_of_exists_isChain.h4 : ¬∀ {α : Type} {r : α → α → Prop} (l : List α), List.IsChain r l → l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (by
  decide)) (by
  decide +kernel)

-- Fin.cast_inj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.cast_inj.h2 : ¬∀ {n m : ℕ} {a b : Fin n}, n = m := fun hc_h => absurd (@hc_h (1) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Set.image_compl_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_compl_eq.h4 : ¬∀ {α β : Type} {f : α → β} {s : Set α}, f '' sᶜ = (f '' s)ᶜ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Function.Surjective.nonempty_preimage, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.nonempty_preimage.h3 : ¬∀ {α β : Type} {f : α → β} {s : Set β}, (f ⁻¹' s).Nonempty ↔ s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun _ => true : ℕ → Bool) ({b : Bool | b = Bool.false})) (by
  simp)

-- Fin.castLE_inj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castLE_inj.h2 : ¬∀ {n m : ℕ} {a b : Fin m}, m ≤ n := fun hc_h => absurd (@hc_h (0) (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Part.right_dom_of_sub_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.right_dom_of_sub_dom.h4 : ¬∀ {α : Type} [inst : Sub α] {a : Part α} {b : Part α}, b.Dom := fun hc_h => absurd (@hc_h (ℕ) (instSubNat) (0) (⊥)) (by
  nofun)

-- List.lookmap_id', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lookmap_id'.h2 : ¬∀ {α : Type} (f : α → Option α) (l : List α), List.lookmap f l = l := fun hc_h => absurd (@hc_h (ℕ) (fun n => some (n + 1) : ℕ → Option ℕ) ([0])) (by
  decide +kernel)

-- Fin.zero_ne_one', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.zero_ne_one'.h1 : Not
      (∀ {n : Nat},
        @Ne
          (Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@OfNat.ofNat
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (nat_lit 0)
            (@Fin.instOfNat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (nat_lit 0)))
          (@OfNat.ofNat
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (nat_lit 1)
            (@Fin.instOfNat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (nat_lit 1)))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- List.Ico.pred_singleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.pred_singleton.h1 : ¬∀ {m : ℕ}, List.Ico (m - 1) m = [m - 1] := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.pow_left_injective, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_left_injective.h1 : ¬∀ {n : ℕ}, Function.Injective fun (a : ℕ) => a ^ n := fun hc_h => absurd (@hc_h (0)) (by
  simp)

