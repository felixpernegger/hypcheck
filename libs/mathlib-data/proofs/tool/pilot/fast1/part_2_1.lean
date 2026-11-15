import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Ordnode.balanceL_eq_balance', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.balanceL_eq_balance'.h6 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α},
        l.Balanced →
          r.Balanced →
            r.Sized →
              ((∃ (l' : ℕ), Ordnode.Raised l' l.size ∧ Ordnode.BalancedSz l' r.size) ∨
                  ∃ (r' : ℕ), Ordnode.Raised r.size r' ∧ Ordnode.BalancedSz l.size r') →
                l.balanceL x r = l.balance' x r := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.nil) (by
  decide) (by
  decide) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Set.EqOn.prodMap, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.prodMap.h10 : ¬∀ {α β γ δ : Type} {s : Set α} {t : Set β} {f f' : α → γ} {g g' : β → δ},
        Set.EqOn g g' t → Set.EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- List.Pairwise.rel_getLast_of_rel_getLast_getLast, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_getLast_of_rel_getLast_getLast.h6 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α},
        List.Pairwise R l → ∀ (ha : a ∈ l), R a (l.getLast (List.ne_nil_of_mem ha)) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- Set.mem_biUnion, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_biUnion.h7 : ¬∀ {α β : Type} {s : Set α} {t : α → Set β} {x : α} {y : β}, x ∈ s → y ∈ ⋃ x ∈ s, t x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) (0) (1) (by
  decide)) (by
  simp)

-- Set.eq_of_subset_of_card_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_subset_of_card_le.h5 : ¬∀ {α : Type} {s t : Set α} [inst : Fintype ↑s] [inst_1 : Fintype ↑t], Fintype.card ↑t ≤ Fintype.card ↑s → s = t := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.true})) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.false})) (by
  decide)) (by
  simp)

-- Int.ModEq.add_left_cancel, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.add_left_cancel.h6 : ¬∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → c ≡ d [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Set.notMem_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.notMem_subset.h4 : ¬∀ {α : Type} {a : α} {s t : Set α}, a ∉ t → a ∉ s := fun hc_h => absurd (@hc_h (ℕ) (0) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  decide)) (by
  decide +kernel)

-- Subtype.coind_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.coind_injective.h4 : ¬∀ {α β : Type} {f : α → β} {p : β → Prop}, Function.Injective f → ∀ (a : α), p (f a) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n = 0 : ℕ → Prop) (by
  decide)) (by
  decide +kernel)

-- List.prev_eq_getElem?_idxOf_pred_of_ne_head, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_eq_getElem?_idxOf_pred_of_ne_head.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {a : α}, a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0)) (by
  decide +kernel)

-- Nat.chineseRemainderOfList_lt_prod, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.chineseRemainderOfList_lt_prod.h5 : ¬∀ {ι : Type} (a s : ι → ℕ) (l : List ι) (co : List.Pairwise (Function.onFun Nat.Coprime s) l),
        ↑(Nat.chineseRemainderOfList a s l co) < (List.map s l).prod := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) ([0]) hc_k0) (by
  decide +kernel)

-- List.SortedLE.sortedLT_of_nodup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLE.sortedLT_of_nodup.h3 : ¬∀ {α : Type} [inst : PartialOrder α] {l : List α}, l.Nodup → l.SortedLT := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([1, 0]) (by
  decide)) (by
  decide +kernel)

-- multiplicity_base_pow_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.multiplicity_base_pow_mul.h2 : ¬∀ {p n : ℕ}, n ≠ 0 → ∀ (k : ℕ), multiplicity p (p ^ k * n) = multiplicity p n + k := fun hc_h => absurd (@hc_h (1) (1) (by
  decide) (1)) (by
  simp)

-- List.interleaves_append_singleton_append_singleton_of_length_eq_length, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.interleaves_append_singleton_append_singleton_of_length_eq_length.h6 : ¬∀ {α : Type} {r : α → α → Prop} {l₁ l₂ : List α} {a b : α},
        List.Interleaves r (l₁ ++ [a]) (l₂ ++ [b]) ↔ r b a ∧ List.Interleaves r l₁ (l₂ ++ [b]) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ([]) ([0]) (0) (0)) (by
  simp)

-- List.prev_cons_cons_eq, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.prev_cons_cons_eq.h5.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x z : α), x ∈ x :: z :: l := by
  (intros; solve_by_elim)
theorem HypCheckProof.List.prev_cons_cons_eq.h5.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x z : α),
      (x :: z :: l).prev x (HypCheckProof.List.prev_cons_cons_eq.h5.der l x z) = (z :: l).getLast (List.cons_ne_nil z l) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @List.prev_cons_cons_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.List.prev_cons_cons_eq.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- List.nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {a : α} (d : α), Option.some (l.nextOr a d) = l[List.idxOf a l + 1]? := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0) (0)) (by
  decide +kernel)

-- Nat.nth_mem_of_lt_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_mem_of_lt_card.h3 : ¬∀ {p : ℕ → Prop} {n : ℕ}, (Set.ofPred p).Finite → p (Nat.nth p n) := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (0) (by
  simp)) (by
  decide +kernel)

-- Int.ModEq.of_mul_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.of_mul_left.h4 : ¬∀ {n a b : ℤ} (m : ℤ), a ≡ b [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- Fin.lt_castPred_succ_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.lt_castPred_succ_iff.h3 : ¬∀ {n : ℕ} {a : Fin (n + 1)} {b : Fin (n + 1)}, a.succ ≠ Fin.last (n + 1) := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Nat.le_nth_count', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_nth_count'.h3 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {n : ℕ}, n ≤ Nat.nth p (Nat.count p n) := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (1)) (by
  simp)

-- EReal.top_div_of_pos_ne_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.top_div_of_pos_ne_top.h1 : ¬∀ {a : EReal}, a ≠ ⊤ → ⊤ / a = ⊤ := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  simp)

-- EReal.top_div_of_pos_ne_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.top_div_of_pos_ne_top.h2 : ¬∀ {a : EReal}, 0 < a → ⊤ / a = ⊤ := fun hc_h => absurd (@hc_h (⊤) (by
  decide)) (by
  simp)

-- Fin.mk_zero', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.mk_zero'.h1 : ¬∀ (n : ℕ), NeZero n := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Rat.inv_ofNat_den, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.inv_ofNat_den.h1 : Not
      (∀ (a : Nat),
        @Eq Nat (@Inv.inv Rat Rat.instInv (@OfNat.ofNat Rat a (@Rat.instOfNat a))).den
          (@OfNat.ofNat Nat a (instOfNatNat a))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Nat.sq_mul_squarefree_of_pos', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.sq_mul_squarefree_of_pos'.h1 : ¬∀ {n : ℕ}, ∃ (a : ℕ) (b : ℕ), (b + 1) ^ 2 * (a + 1) = n ∧ Squarefree (a + 1) := fun hc_h => absurd (@hc_h (0)) (by
  simp)

