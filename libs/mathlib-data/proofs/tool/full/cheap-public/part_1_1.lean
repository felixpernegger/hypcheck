import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Set.PairwiseDisjoint.elim_set, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h4.inst : ¬0 = 2 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h4.prem0 : 0 ∈ {n : ℕ | n % 2 = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h4.prem1 : 2 ∈ {n : ℕ | n % 2 = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h4.prem2 : 0 ∈ (fun (a : ℕ) => {n : ℕ | n = 0}) 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h4.prem3 : 0 ∈ (fun (a : ℕ) => {n : ℕ | n = 0}) 2 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h4 : ¬∀ {α ι : Type} {s : Set ι} {f : ι → Set α} {i j : ι}, i ∈ s → j ∈ s → ∀ a ∈ f i, a ∈ f j → i = j := fun hc_h => HypCheckProof.Set.PairwiseDisjoint.elim_set.h4.inst (@hc_h (ℕ) (ℕ) ({n : ℕ | n % 2 = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) (0) (2) HypCheckProof.Set.PairwiseDisjoint.elim_set.h4.prem0 HypCheckProof.Set.PairwiseDisjoint.elim_set.h4.prem1 (0) HypCheckProof.Set.PairwiseDisjoint.elim_set.h4.prem2 HypCheckProof.Set.PairwiseDisjoint.elim_set.h4.prem3)

-- Set.PairwiseDisjoint.elim_set, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h7.inst : ¬1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h7.prem0 : {n : ℕ | n = 0}.PairwiseDisjoint fun (a : ℕ) => {n : ℕ | n = 0} := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h7.prem1 : 0 ∈ {n : ℕ | n = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h7.prem2 : 0 ∈ (fun (a : ℕ) => {n : ℕ | n = 0}) 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h7.prem3 : 0 ∈ (fun (a : ℕ) => {n : ℕ | n = 0}) 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h7 : ¬∀ {α ι : Type} {s : Set ι} {f : ι → Set α}, s.PairwiseDisjoint f → ∀ {i j : ι}, j ∈ s → ∀ a ∈ f i, a ∈ f j → i = j := fun hc_h => HypCheckProof.Set.PairwiseDisjoint.elim_set.h7.inst (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) HypCheckProof.Set.PairwiseDisjoint.elim_set.h7.prem0 (1) (0) HypCheckProof.Set.PairwiseDisjoint.elim_set.h7.prem1 (0) HypCheckProof.Set.PairwiseDisjoint.elim_set.h7.prem2 HypCheckProof.Set.PairwiseDisjoint.elim_set.h7.prem3)

-- Set.PairwiseDisjoint.elim_set, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h8.inst : ¬0 = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h8.prem0 : {n : ℕ | n = 0}.PairwiseDisjoint fun (a : ℕ) => {n : ℕ | n = 0} := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h8.prem1 : 0 ∈ {n : ℕ | n = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h8.prem2 : 0 ∈ (fun (a : ℕ) => {n : ℕ | n = 0}) 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h8.prem3 : 0 ∈ (fun (a : ℕ) => {n : ℕ | n = 0}) 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.PairwiseDisjoint.elim_set.h8 : ¬∀ {α ι : Type} {s : Set ι} {f : ι → Set α}, s.PairwiseDisjoint f → ∀ {i j : ι}, i ∈ s → ∀ a ∈ f i, a ∈ f j → i = j := fun hc_h => HypCheckProof.Set.PairwiseDisjoint.elim_set.h8.inst (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) HypCheckProof.Set.PairwiseDisjoint.elim_set.h8.prem0 (0) (1) HypCheckProof.Set.PairwiseDisjoint.elim_set.h8.prem1 (0) HypCheckProof.Set.PairwiseDisjoint.elim_set.h8.prem2 HypCheckProof.Set.PairwiseDisjoint.elim_set.h8.prem3)

-- Finset.vaddAntidiagonal_min_vadd_min, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.vaddAntidiagonal_min_vadd_min.h5 : ¬∀ {G P : Type} [inst : LinearOrder G] [inst_1 : LinearOrder P] [inst_2 : VAdd G P] {s : Set G} {t : Set P},
        s.IsWF → t.IsWF → s.Nonempty → t.Nonempty → IsOrderedCancelVAdd G P := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.linearOrder) (Bool.linearOrder) (instVAddOfAdd) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (by
  simp) (by
  simp)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedVAdd.vadd_le_vadd_left (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.vaddAntidiagonal_min_vadd_min, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.vaddAntidiagonal_min_vadd_min.h10 : ¬∀ {G P : Type} [inst : LinearOrder G] [inst_1 : LinearOrder P] [inst_2 : VAdd G P] [inst_3 : IsOrderedCancelVAdd G P]
        {s : Set G} {t : Set P}, s.IsWF → t.IsWF → t.Nonempty → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instLinearOrder) (instVAddOfAdd) _ ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- Finset.vaddAntidiagonal_min_vadd_min, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.vaddAntidiagonal_min_vadd_min.h11 : ¬∀ {G P : Type} [inst : LinearOrder G] [inst_1 : LinearOrder P] [inst_2 : VAdd G P] [inst_3 : IsOrderedCancelVAdd G P]
        {s : Set G} {t : Set P}, s.IsWF → t.IsWF → s.Nonempty → t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instLinearOrder) (instVAddOfAdd) _ ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- Finset.antidiagonal_mono_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.antidiagonal_mono_left.h3 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO} {a : α}
        {u : Set α} {hu : u.IsPWO}, u ⊆ s → IsOrderedCancelAddMonoid α := fun hc_h => absurd (@hc_h (Bool) (CommRing.toCommSemiring.toAddCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (Bool.false) ({b : Bool | b = Bool.true}) (by
  simp) (by
  rfl)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedAddMonoid.add_le_add_left (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.addAntidiagonal_mono_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.addAntidiagonal_mono_right.h3 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO} {a : α}
        {u : Set α} {hu : u.IsPWO}, u ⊆ t → IsOrderedCancelAddMonoid α := fun hc_h => absurd (@hc_h (Bool) (CommRing.toCommSemiring.toAddCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (Bool.false) ({b : Bool | b = Bool.true}) (by
  simp) (by
  rfl)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedAddMonoid.add_le_add_left (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.IsChain.concat_induction, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.concat_induction.h8.inst : ¬(fun (n : ℕ) => n = 0) 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.concat_induction.h8.prem0 : List.IsChain (fun (a b : ℕ) => a < b) ([0] ++ [1]) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.concat_induction.h8.prem1 : (fun (n : ℕ) => n = 0) (([0] ++ [1]).head (List.concat_ne_nil 1 [0])) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.concat_induction.h8.prem2 : 1 ∈ [0] ++ [1] := by
  decide
theorem HypCheckProof.List.IsChain.concat_induction.h8 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        List.IsChain r (l ++ [b]) → (l ++ [b]).head (List.concat_ne_nil b l) = a → p a → ∀ i ∈ l ++ [b], p i := fun hc_h => HypCheckProof.List.IsChain.concat_induction.h8.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (([0] ++ [1]).head (List.concat_ne_nil 1 [0])) (1) (fun (n : ℕ) => n = 0) ([0]) HypCheckProof.List.IsChain.concat_induction.h8.prem0 rfl HypCheckProof.List.IsChain.concat_induction.h8.prem1 (1) HypCheckProof.List.IsChain.concat_induction.h8.prem2)

-- List.IsChain.concat_induction, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.concat_induction.h9 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        List.IsChain r (l ++ [b]) →
          (l ++ [b]).head (List.concat_ne_nil b l) = a → (∀ ⦃x y : α⦄, r x y → p x → p y) → ∀ i ∈ l ++ [b], p i := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ (0) (fun _ => False : ℕ → Prop) ([]) (by
  decide) rfl (by
  simp) (0) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.concat_induction, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.concat_induction.h11.inst : ¬(fun (n : ℕ) => n = 0) 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.concat_induction.h11.prem0 : List.IsChain (fun (a b : ℕ) => a = b) ([] ++ [0]) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.concat_induction.h11.prem1 : ∀ ⦃x y : ℕ⦄, x = y → x = 0 → (fun (n : ℕ) => n = 0) y := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.concat_induction.h11.prem2 : (fun (n : ℕ) => n = 0) (([] ++ [0]).head (List.concat_ne_nil 0 [])) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.IsChain.concat_induction.h11 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        List.IsChain r (l ++ [b]) →
          (l ++ [b]).head (List.concat_ne_nil b l) = a → (∀ ⦃x y : α⦄, r x y → p x → p y) → p a → ∀ (i : α), p i := fun hc_h => HypCheckProof.List.IsChain.concat_induction.h11.inst (@hc_h (ℕ) (fun (a b : ℕ) => a = b) (([] ++ [0]).head (List.concat_ne_nil 0 [])) (0) (fun (n : ℕ) => n = 0) ([]) HypCheckProof.List.IsChain.concat_induction.h11.prem0 rfl HypCheckProof.List.IsChain.concat_induction.h11.prem1 HypCheckProof.List.IsChain.concat_induction.h11.prem2 (1))

-- Set.EqOn.cancel_left, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.cancel_left.h10 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {f₁ f₂ : α → β} {g : β → γ},
        Set.EqOn (g ∘ f₁) (g ∘ f₂) s → Set.InjOn g t → Set.MapsTo f₂ s t → Set.EqOn f₁ f₂ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- Set.EqOn.cancel_left, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.cancel_left.h11 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {f₁ f₂ : α → β} {g : β → γ},
        Set.EqOn (g ∘ f₁) (g ∘ f₂) s → Set.InjOn g t → Set.MapsTo f₁ s t → Set.EqOn f₁ f₂ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- List.pair_sublist_insertionSort', hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.pair_sublist_insertionSort'.h10.inst : ¬[0, 0].Sublist (List.insertionSort (fun (a b : ℕ) => a ≤ b) []) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.pair_sublist_insertionSort'.h10.prem0 : (fun (a b : ℕ) => a ≤ b) 0 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.pair_sublist_insertionSort'.h10 : ¬∀ {α : Type} {r : α → α → Prop} [inst : DecidableRel r] [inst_1 : Std.Antisymm r] [inst_2 : Std.Total r]
        [inst_3 : IsTrans α r] {a b : α} {l : List α}, r a b → [a, b].Sublist (List.insertionSort r l) := fun hc_h => HypCheckProof.List.pair_sublist_insertionSort'.h10.inst (@hc_h (ℕ) (fun (a b : ℕ) => a ≤ b) (Nat.decLe) _ _ _ (0) (0) ([]) HypCheckProof.List.pair_sublist_insertionSort'.h10.prem0)

-- Prod.Lex.trans, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.Lex.trans.h9 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop} [inst : IsTrans α r] [inst : IsTrans β s] {x y z : α × β},
        Prod.Lex r s y z → Prod.Lex r s x z := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) _ _ ((0, 1)) ((0, 0)) ((0, 1)) (by
  decide)) (by
  decide +kernel)

-- Prod.Lex.trans, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.Lex.trans.h10 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop} [inst : IsTrans α r] [inst : IsTrans β s] {x y z : α × β},
        Prod.Lex r s x y → Prod.Lex r s x z := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) _ _ ((0, 0)) ((0, 1)) ((0, 0)) (by
  decide)) (by
  decide +kernel)

-- List.next_getLast_cons, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.next_getLast_cons.h4.gneg.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α),
      ∀ x ∉ l,
        ∀ (y : α) (h : x ∈ y :: l), x ≠ y → x = (y :: l).getLast (List.cons_ne_nil y l) → l.Nodup → (y :: l).next x h = y := by
  (intros; grind)
theorem HypCheckProof.List.next_getLast_cons.h4.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y : α) (h : x ∈ y :: l),
      x ≠ y → x = (y :: l).getLast (List.cons_ne_nil y l) → l.Nodup → (y :: l).next x h = y := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9
  exact Classical.byCases (fun hc_h => @List.next_getLast_cons hc_x0 hc_x1 hc_x2 hc_x3 hc_h hc_x5 hc_x6 hc_x7 hc_x8 hc_x9) (fun hc_hn => @HypCheckProof.List.next_getLast_cons.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn hc_x5 hc_x6 hc_x7 hc_x8 hc_x9)
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.next_getLast_cons.h4.derivable.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y : α),
      x ∈ y :: l → x ≠ y → x = (y :: l).getLast (List.cons_ne_nil y l) → l.Nodup → x ∈ l := by
  (intros; grind)

-- List.next_getLast_cons, hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.next_getLast_cons.h6.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α),
      ∀ x ∈ l, ∀ (y : α), x ≠ y → x = (y :: l).getLast (List.cons_ne_nil y l) → l.Nodup → x ∈ y :: l := by
  (intros; solve_by_elim)
theorem HypCheckProof.List.next_getLast_cons.h6.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x : α) (h : x ∈ l) (y : α) (hy : x ≠ y)
      (hx : x = (y :: l).getLast (List.cons_ne_nil y l)) (hl : l.Nodup),
      (y :: l).next x (HypCheckProof.List.next_getLast_cons.h6.der l x h y hy hx hl) = y := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8
  exact @List.next_getLast_cons hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.List.next_getLast_cons.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8) hc_x6 hc_x7 hc_x8

-- List.next_getLast_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_getLast_cons.h7 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α),
        ∀ x ∈ l, ∀ (y : α) (h : x ∈ y :: l), x = (y :: l).getLast (List.cons_ne_nil y l) → l.Nodup → (y :: l).next x h = y := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) (instDecidableEqNat) ([0, 1]) _ hc_k0 (1) hc_k1 rfl hc_k2) (by
  decide +kernel)

-- List.next_getLast_cons, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_getLast_cons.h8 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α),
        ∀ x ∈ l, ∀ (y : α) (h : x ∈ y :: l), x ≠ y → l.Nodup → (y :: l).next x h = y := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (ℕ) (instDecidableEqNat) ([0, 1]) (0) hc_k0 (2) hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- List.next_getLast_cons, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_getLast_cons.h9 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α),
        ∀ x ∈ l, ∀ (y : α) (h : x ∈ y :: l), x ≠ y → x = (y :: l).getLast (List.cons_ne_nil y l) → (y :: l).next x h = y := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) (instDecidableEqNat) ([0, 0]) _ hc_k0 (1) hc_k1 hc_k2 rfl) (by
  decide +kernel)

-- Finset.addAntidiagonal_min_mul_min, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.addAntidiagonal_min_mul_min.h3 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : LinearOrder α] {s t : Set α},
        s.IsWF → t.IsWF → s.Nonempty → t.Nonempty → IsOrderedCancelAddMonoid α := fun hc_h => absurd (@hc_h (Bool) (CommRing.toCommSemiring.toAddCommMonoid) (Bool.linearOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (by
  simp) (by
  simp)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedAddMonoid.add_le_add_left (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.addAntidiagonal_min_mul_min, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.addAntidiagonal_min_mul_min.h8 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : LinearOrder α] [inst : IsOrderedCancelAddMonoid α] {s t : Set α},
        s.IsWF → t.IsWF → t.Nonempty → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddCommMonoid) (Nat.instLinearOrder) _ ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- Finset.addAntidiagonal_min_mul_min, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.addAntidiagonal_min_mul_min.h9 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : LinearOrder α] [inst : IsOrderedCancelAddMonoid α] {s t : Set α},
        s.IsWF → t.IsWF → s.Nonempty → t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddCommMonoid) (Nat.instLinearOrder) _ ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- Finset.mulAntidiagonal_min_mul_min, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mulAntidiagonal_min_mul_min.h3 : ¬∀ {α : Type} [inst : CommMonoid α] [inst_1 : LinearOrder α] {s t : Set α},
        s.IsWF → t.IsWF → s.Nonempty → t.Nonempty → IsOrderedCancelMonoid α := fun hc_h => absurd (@hc_h (Bool) (BooleanRing.toCommRing.toCommMonoid) (Bool.linearOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (by
  simp) (by
  simp)) (by
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

-- Set.IsWF.min_mul, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.IsWF.min_mul.h5 : ¬∀ {α : Type} {s t : Set α} [inst : CommMonoid α] [inst_1 : LinearOrder α],
        s.IsWF → t.IsWF → s.Nonempty → t.Nonempty → IsOrderedCancelMonoid α := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (BooleanRing.toCommRing.toCommMonoid) (Bool.linearOrder) (by
  simp) (by
  simp) (by
  simp) (by
  simp)) (by
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

-- List.sublist_insertionSort', hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sublist_insertionSort'.h9 : ¬∀ {α : Type} {r : α → α → Prop} [inst : DecidableRel r] [inst_1 : Std.Antisymm r] [inst_2 : Std.Total r]
        [inst_3 : IsTrans α r] {l c : List α}, List.Pairwise r c → c.Sublist (List.insertionSort r l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (Nat.decLe) _ _ _ ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- Set.InjOn.ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.ne.h6 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {x y : α}, x ∈ s → y ∈ s → x ≠ y → f x ≠ f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n % 2 = 0}) (fun _ => 0 : ℕ → ℕ) (0) (2) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.InjOn.ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.ne.h7 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {x y : α}, Set.InjOn f s → y ∈ s → x ≠ y → f x ≠ f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (1) (0) (by
  simp) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.InjOn.ne, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.ne.h8 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {x y : α}, Set.InjOn f s → x ∈ s → x ≠ y → f x ≠ f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (0) (1) (by
  simp) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.InjOn.ne, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.ne.h9 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → f x ≠ f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (0) (0) (by
  simp) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.InjOn.mem_of_mem_image, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.mem_of_mem_image.h7 : ¬∀ {α β : Type} {s s₁ : Set α} {f : α → β} {x : α}, Set.InjOn f s → x ∈ s → f x ∈ f '' s₁ → x ∈ s₁ := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) (fun _ => 0 : Bool → ℕ) (Bool.false) (by
  simp) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Set.InjOn.mem_of_mem_image, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.mem_of_mem_image.h8 : ¬∀ {α β : Type} {s s₁ : Set α} {f : α → β} {x : α}, Set.InjOn f s → s₁ ⊆ s → f x ∈ f '' s₁ → x ∈ s₁ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (1) (by
  simp) (by
  rfl) (by
  simp)) (by
  decide +kernel)

-- Set.InjOn.mem_of_mem_image, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.mem_of_mem_image.h9 : ¬∀ {α β : Type} {s s₁ : Set α} {f : α → β} {x : α}, Set.InjOn f s → s₁ ⊆ s → x ∈ s → x ∈ s₁ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ) (0) (by
  simp) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- Matrix.map_algebraMap, hypothesis 14: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.map_algebraMap.h14 : ¬∀ {n R α β : Type} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R] [inst_3 : Semiring α]
        [inst_4 : Semiring β] [inst_5 : Algebra R α] [inst_6 : Algebra R β] (r : R) (f : α → β),
        f 0 = 0 → ((Algebra.algebraMap R (Matrix n n α)) r).map f = (Algebra.algebraMap R (Matrix n n β)) r := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (ℕ) (Bool.fintype) (instDecidableEqBool) (Nat.instCommSemiring) (Nat.instSemiring) (Nat.instSemiring) (Algebra.id ℕ) (Algebra.id ℕ) (1) (fun _ => 0 : ℕ → ℕ) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- List.IsChain.backwards_concat_induction, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.backwards_concat_induction.h5 : ¬∀ {α : Type} {r : α → α → Prop} {b : α} (p : α → Prop) (l : List α),
        (∀ ⦃x y : α⦄, r x y → p y → p x) → p b → ∀ i ∈ l, p i := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (fun n => n = 0 : ℕ → Prop) ([1]) (by
  omega) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.backwards_concat_induction, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.backwards_concat_induction.h6 : ¬∀ {α : Type} {r : α → α → Prop} {b : α} (p : α → Prop) (l : List α), List.IsChain r (l ++ [b]) → p b → ∀ i ∈ l, p i := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop) (Bool.true) (fun b => b = true : Bool → Prop) ([Bool.false]) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.backwards_concat_induction, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.backwards_concat_induction.h9 : ¬∀ {α : Type} {r : α → α → Prop} {b : α} (p : α → Prop) (l : List α),
        List.IsChain r (l ++ [b]) → (∀ ⦃x y : α⦄, r x y → p y → p x) → p b → ∀ (i : α), p i := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (fun n => n = 0 : ℕ → Prop) ([]) (by
  decide) (by
  omega) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1)) (by
  decide +kernel)

-- List.inj_on_of_nodup_map, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.inj_on_of_nodup_map.h6 : ¬∀ {α β : Type} {f : α → β} {l : List α}, (List.map f l).Nodup → ∀ ⦃x y : α⦄, y ∈ l → f x = f y → x = y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ([0]) (by
  decide) (1) (0) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- List.inj_on_of_nodup_map, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.inj_on_of_nodup_map.h8 : ¬∀ {α β : Type} {f : α → β} {l : List α}, (List.map f l).Nodup → ∀ ⦃x : α⦄, x ∈ l → ∀ ⦃y : α⦄, f x = f y → x = y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ([0]) (by
  decide) (0) (by
  decide) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- List.inj_on_of_nodup_map, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.inj_on_of_nodup_map.h9 : ¬∀ {α β : Type} {f : α → β} {l : List α}, (List.map f l).Nodup → ∀ ⦃x : α⦄, x ∈ l → ∀ ⦃y : α⦄, y ∈ l → x = y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ([0, 1]) (by
  decide) (0) (by
  decide) (1) (by
  decide)) (by
  decide +kernel)

-- Directed.finite_le, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Directed.finite_le.h8 : ¬∀ {α : Type} {r : α → α → Prop} [inst : IsTrans α r] {ι κ : Type} [inst : Nonempty ι] [inst : Finite κ] {f : ι → α}
        (g : κ → ι), ∃ (z : ι), ∀ (i : κ), r (f (g i)) (f z) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ (ℕ) (Bool) _ _ (fun _ => 0 : ℕ → ℕ) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  simp)

-- Equiv.piFinsetUnion_left, hypothesis 10: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Equiv.piFinsetUnion_left.h10.der.{u_3, u_4} : ∀ {ι : Type u_4} [inst : DecidableEq ι] (α : ι → Type u_3) {s t : Finset ι},
      @Disjoint (Finset ι) (@Finset.instPartialOrder ι) (@Finset.instOrderBot ι) s t →
        ∀
          {f :
            (i : ↥s) →
              α
                (@Subtype.val ι
                  (fun (x : ι) =>
                    @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s x)
                  i)}
          {g :
            (i : ↥t) →
              α
                (@Subtype.val ι
                  (fun (x : ι) =>
                    @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) t x)
                  i)}
          {i : ι},
          @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s i →
            @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι))
              (@Max.max (Finset ι) (@Finset.instMax ι inst) s t) i := by
  (intros; simp_all; done)
theorem HypCheckProof.Equiv.piFinsetUnion_left.h10.{u_3, u_4} : ∀ {ι : Type u_4} [inst : DecidableEq ι] (α : ι → Type u_3) {s t : Finset ι}
      (h : @Disjoint (Finset ι) (@Finset.instPartialOrder ι) (@Finset.instOrderBot ι) s t)
      {f :
        (i : ↥s) →
          α
            (@Subtype.val ι
              (fun (x : ι) =>
                @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s x)
              i)}
      {g :
        (i : ↥t) →
          α
            (@Subtype.val ι
              (fun (x : ι) =>
                @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) t x)
              i)}
      {i : ι} (hi : @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s i),
      @Eq
        (α
          (@Subtype.val ι
            (fun (x : ι) =>
              @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι))
                (@Max.max (Finset ι) (@Finset.instMax ι inst) s t) x)
            (@Subtype.mk ι
              (fun (x : ι) =>
                @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι))
                  (@Max.max (Finset ι) (@Finset.instMax ι inst) s t) x)
              i (@HypCheckProof.Equiv.piFinsetUnion_left.h10.der ι inst α s t h f g i hi))))
        (@DFunLike.coe
          (Equiv
            (Prod
              ((i : ↥s) →
                α
                  (@Subtype.val ι
                    (fun (x : ι) =>
                      @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s x)
                    i))
              ((i : ↥t) →
                α
                  (@Subtype.val ι
                    (fun (x : ι) =>
                      @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) t x)
                    i)))
            ((i : ↥(@Max.max (Finset ι) (@Finset.instMax ι inst) s t)) →
              α
                (@Subtype.val ι
                  (fun (x : ι) =>
                    @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι))
                      (@Max.max (Finset ι) (@Finset.instMax ι inst) s t) x)
                  i)))
          (Prod
            ((i : ↥s) →
              α
                (@Subtype.val ι
                  (fun (x : ι) =>
                    @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s x)
                  i))
            ((i : ↥t) →
              α
                (@Subtype.val ι
                  (fun (x : ι) =>
                    @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) t x)
                  i)))
          (fun
              (x :
                Prod
                  ((i : ↥s) →
                    α
                      (@Subtype.val ι
                        (fun (x : ι) =>
                          @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s x)
                        i))
                  ((i : ↥t) →
                    α
                      (@Subtype.val ι
                        (fun (x : ι) =>
                          @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) t x)
                        i))) =>
            (i : ↥(@Max.max (Finset ι) (@Finset.instMax ι inst) s t)) →
              α
                (@Subtype.val ι
                  (fun (x : ι) =>
                    @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι))
                      (@Max.max (Finset ι) (@Finset.instMax ι inst) s t) x)
                  i))
          (@EquivLike.toFunLike
            (Equiv
              (Prod
                ((i : ↥s) →
                  α
                    (@Subtype.val ι
                      (fun (x : ι) =>
                        @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s x)
                      i))
                ((i : ↥t) →
                  α
                    (@Subtype.val ι
                      (fun (x : ι) =>
                        @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) t x)
                      i)))
              ((i : ↥(@Max.max (Finset ι) (@Finset.instMax ι inst) s t)) →
                α
                  (@Subtype.val ι
                    (fun (x : ι) =>
                      @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι))
                        (@Max.max (Finset ι) (@Finset.instMax ι inst) s t) x)
                    i)))
            (Prod
              ((i : ↥s) →
                α
                  (@Subtype.val ι
                    (fun (x : ι) =>
                      @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s x)
                    i))
              ((i : ↥t) →
                α
                  (@Subtype.val ι
                    (fun (x : ι) =>
                      @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) t x)
                    i)))
            ((i : ↥(@Max.max (Finset ι) (@Finset.instMax ι inst) s t)) →
              α
                (@Subtype.val ι
                  (fun (x : ι) =>
                    @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι))
                      (@Max.max (Finset ι) (@Finset.instMax ι inst) s t) x)
                  i))
            (@Equiv.instEquivLike
              (Prod
                ((i : ↥s) →
                  α
                    (@Subtype.val ι
                      (fun (x : ι) =>
                        @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s x)
                      i))
                ((i : ↥t) →
                  α
                    (@Subtype.val ι
                      (fun (x : ι) =>
                        @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) t x)
                      i)))
              ((i : ↥(@Max.max (Finset ι) (@Finset.instMax ι inst) s t)) →
                α
                  (@Subtype.val ι
                    (fun (x : ι) =>
                      @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι))
                        (@Max.max (Finset ι) (@Finset.instMax ι inst) s t) x)
                    i))))
          (@Equiv.piFinsetUnion ι inst α s t h)
          (@Prod.mk
            ((i : ↥s) →
              α
                (@Subtype.val ι
                  (fun (x : ι) =>
                    @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s x)
                  i))
            ((i : ↥t) →
              α
                (@Subtype.val ι
                  (fun (x : ι) =>
                    @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) t x)
                  i))
            f g)
          (@Subtype.mk ι
            (fun (x : ι) =>
              @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι))
                (@Max.max (Finset ι) (@Finset.instMax ι inst) s t) x)
            i (@HypCheckProof.Equiv.piFinsetUnion_left.h10.der ι inst α s t h f g i hi)))
        (f
          (@Subtype.mk ι
            (fun (x : ι) => @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) s x)
            i hi)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9
  exact @Equiv.piFinsetUnion_left hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 (@HypCheckProof.Equiv.piFinsetUnion_left.h10.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9)

-- perm_of_prod_eq_prod, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.perm_of_prod_eq_prod.h7 : ¬∀ {M : Type} [inst : CommMonoidWithZero M] [inst_1 : IsCancelMulZero M] [inst_2 : Subsingleton Mˣ] {l₁ l₂ : List M},
        l₁.prod = l₂.prod → (∀ p ∈ l₂, Prime p) → l₁.Perm l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instCommMonoidWithZero) _ _ ([1]) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- perm_of_prod_eq_prod, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.perm_of_prod_eq_prod.h8 : ¬∀ {M : Type} [inst : CommMonoidWithZero M] [inst_1 : IsCancelMulZero M] [inst_2 : Subsingleton Mˣ] {l₁ l₂ : List M},
        l₁.prod = l₂.prod → (∀ p ∈ l₁, Prime p) → l₁.Perm l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instCommMonoidWithZero) _ _ ([]) ([1]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Rat.div_int_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.div_int_inj.h4 : Not
      (∀ {a b c d : Int},
        @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) d →
          a.natAbs.Coprime b.natAbs →
            c.natAbs.Coprime d.natAbs →
              @Eq Rat
                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast a)
                    (@Int.cast Rat Rat.instIntCast b))
                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast c)
                    (@Int.cast Rat Rat.instIntCast d)) →
                And (@Eq Int a c) (@Eq Int b d)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (by
  decide) (by
  decide) (by
  decide) (by
  decide +kernel)) (by
  decide +kernel)

-- Rat.div_int_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.div_int_inj.h5 : Not
      (∀ {a b c d : Int},
        @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) b →
          a.natAbs.Coprime b.natAbs →
            c.natAbs.Coprime d.natAbs →
              @Eq Rat
                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast a)
                    (@Int.cast Rat Rat.instIntCast b))
                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast c)
                    (@Int.cast Rat Rat.instIntCast d)) →
                And (@Eq Int a c) (@Eq Int b d)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (by
  decide) (by
  decide) (by
  decide) (by
  decide +kernel)) (by
  decide +kernel)

-- Rat.div_int_inj, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.div_int_inj.h6 : Not
      (∀ {a b c d : Int},
        @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) b →
          @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) d →
            c.natAbs.Coprime d.natAbs →
              @Eq Rat
                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast a)
                    (@Int.cast Rat Rat.instIntCast b))
                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast c)
                    (@Int.cast Rat Rat.instIntCast d)) →
                And (@Eq Int a c) (@Eq Int b d)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (by
  decide) (by
  decide) (by
  decide) (by
  decide +kernel)) (by
  decide +kernel)

-- Rat.div_int_inj, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.div_int_inj.h7 : Not
      (∀ {a b c d : Int},
        @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) b →
          @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) d →
            a.natAbs.Coprime b.natAbs →
              @Eq Rat
                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast a)
                    (@Int.cast Rat Rat.instIntCast b))
                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast c)
                    (@Int.cast Rat Rat.instIntCast d)) →
                And (@Eq Int a c) (@Eq Int b d)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))) (by
  decide) (by
  decide) (by
  decide) (by
  decide +kernel)) (by
  decide +kernel)

-- Rat.div_int_inj, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.div_int_inj.h8 : ¬∀ {a b c d : ℤ}, 0 < b → 0 < d → a.natAbs.Coprime b.natAbs → c.natAbs.Coprime d.natAbs → a = c ∧ b = d := fun hc_h => absurd (@hc_h (0) (1) (1) (1) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Ordnode.size_balanceR, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.size_balanceR.h6 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α},
        l.Balanced →
          r.Balanced →
            r.Sized →
              ((∃ (l' : ℕ), Ordnode.Raised l.size l' ∧ Ordnode.BalancedSz l' r.size) ∨
                  ∃ (r' : ℕ), Ordnode.Raised r' r.size ∧ Ordnode.BalancedSz l.size r') →
                (l.balanceR x r).size = l.size + r.size + 1 := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.node 1 Ordnode.nil 0 Ordnode.nil) (by
  decide) (by
  decide) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Ordnode.size_balanceR, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.size_balanceR.h7 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α},
        l.Balanced →
          r.Balanced →
            l.Sized →
              ((∃ (l' : ℕ), Ordnode.Raised l.size l' ∧ Ordnode.BalancedSz l' r.size) ∨
                  ∃ (r' : ℕ), Ordnode.Raised r' r.size ∧ Ordnode.BalancedSz l.size r') →
                (l.balanceR x r).size = l.size + r.size + 1 := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  decide) (by
  decide) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Function.Semiconj.bijOn_image, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Semiconj.bijOn_image.h7 : ¬∀ {α β : Type} {fa : α → α} {fb : β → β} {f : α → β} {s t : Set α},
        Set.BijOn fa s t → Set.InjOn f t → Set.BijOn fb (f '' s) (f '' t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp) (by
  simp)) (by
  simp)

-- Finsupp.nonTorsionWeight_of, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.nonTorsionWeight_of.h8 : ¬∀ {σ M : Type} (R : Type) [inst : Semiring R] (w : σ → M) [inst_1 : AddCommMonoid M] [inst_2 : Module R M]
        [inst_3 : IsDomain R], (∀ (i : σ), w i ≠ 0) → Finsupp.NonTorsionWeight R w := fun hc_h => absurd (@hc_h (ℕ) (Bool) (ℕ) (Nat.instSemiring) (fun _ => true : ℕ → Bool) (CommRing.toCommSemiring.toAddCommMonoid) (AddCommMonoid.toNatModule) _ (by
  simp)) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_zero_of_smul_eq_zero (r := (2 : ℕ)) (s := (0 : ℕ))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

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

-- List.map_erase, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map_erase.h7 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : LawfulBEq α] [inst_2 : BEq β] [inst_3 : LawfulBEq β] {f : α → β} {a : α}
        (l : List α), List.map f (l.erase a) = (List.map f l).erase (f a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instBEqOfDecidableEq) _ (instBEqOfDecidableEq) _ (fun _ => 0 : ℕ → ℕ) (0) ([1])) (by
  decide +kernel)

-- Finset.isPWO_support_smulAntidiagonal, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.isPWO_support_smulAntidiagonal.h5 : ¬∀ {G P : Type} [inst : SMul G P] [inst_1 : PartialOrder G] [inst_2 : PartialOrder P] {s : Set G} {t : Set P},
        s.IsPWO → t.IsPWO → IsOrderedCancelSMul G P := fun hc_h => absurd (@hc_h (ℕ) (Bool) (NSMul.toSMul) (Nat.instPartialOrder) (Bool.instPartialOrder) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedSMul.smul_le_smul_right (1 : ℕ) (2 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.mem_antidiagonal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_antidiagonal.h3 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO} {a : α}
        {x : α × α}, IsOrderedCancelAddMonoid α := fun hc_h => absurd (@hc_h (Bool) (CommRing.toCommSemiring.toAddCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (Bool.false) ((Bool.false, Bool.false))) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedAddMonoid.add_le_add_left (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.mem_addAntidiagonal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_addAntidiagonal.h3 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO} {a : α}
        {x : α × α}, IsOrderedCancelAddMonoid α := fun hc_h => absurd (@hc_h (Bool) (CommRing.toCommSemiring.toAddCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (Bool.false) ((Bool.false, Bool.false))) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedAddMonoid.add_le_add_left (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.mem_mulAntidiagonal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_mulAntidiagonal.h3 : ¬∀ {α : Type} [inst : CommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO} {a : α}
        {x : α × α}, IsOrderedCancelMonoid α := fun hc_h => absurd (@hc_h (Bool) (BooleanRing.toCommRing.toCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (Bool.false) ((Bool.false, Bool.false))) (by
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

-- Int.zpow_lt_iff_lt_clog, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.zpow_lt_iff_lt_clog.h6 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ} {x : ℤ} {r : R}, 0 < r → (↑b ^ x < r ↔ x < Int.clog b r) := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Int.zpow_lt_iff_lt_clog, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.zpow_lt_iff_lt_clog.h9 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ}, 1 < b → ∀ {x : ℤ} {r : R}, ↑b ^ x < r ↔ x < Int.clog b r := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (2) (by
  decide) (-1) (0)) (by
  decide +kernel)

-- List.Perm.kunion, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.kunion.h9 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {l₁ l₂ l₃ l₄ : List (Sigma β)},
        l₃.NodupKeys → l₁.Perm l₂ → (l₁.kunion l₃).Perm (l₂.kunion l₄) := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) ([]) ([]) ([]) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)]) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- Int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul.h8 : ¬∀ {p : ℕ}, Nat.Prime p → ∀ {m n : ℤ} {k l : ℕ}, ↑(p ^ k) ∣ m → ↑(p ^ l) ∣ n → ↑(p ^ (k + 1)) ∣ m ∨ ↑(p ^ (l + 1)) ∣ n := fun hc_h => absurd (@hc_h (2) (by
  decide) (1) (1) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.SortedGT.getElem_gt_getElem_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.getElem_gt_getElem_of_lt.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α] ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, j < i → l[i] < l[j] := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) ([0, 1]) (Nat.instPreorder) (1) (0) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- List.SortedGT.getElem_gt_getElem_of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.getElem_gt_getElem_of_lt.h6 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedGT → ∀ ⦃i j : ℕ⦄ ⦃hj : j < l.length⦄, j < i → i < l.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) (Nat.instPreorder) (by
  decide) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.SortedGT.getElem_gt_getElem_of_lt, hypothesis 7: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.SortedGT.getElem_gt_getElem_of_lt.h7.der.{u_1} : ∀ {α : Type u_1} {l : List α} [inst : Preorder α], l.SortedGT → ∀ ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄, j < i → j < l.length := by
  (intros; lia)
theorem HypCheckProof.List.SortedGT.getElem_gt_getElem_of_lt.h7.{u_1} : ∀ {α : Type u_1} {l : List α} [inst : Preorder α] (a : l.SortedGT) ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄ (a_1 : j < i),
      l[i] < l[j] := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7
  exact @List.SortedGT.getElem_gt_getElem_of_lt hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.List.SortedGT.getElem_gt_getElem_of_lt.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7) hc_x7

-- List.SortedGT.getElem_gt_getElem_of_lt, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.getElem_gt_getElem_of_lt.h8 : ¬∀ {α : Type} {l : List α} [inst : Preorder α],
        l.SortedGT → ∀ ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, l[i] < l[j] := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) ([0]) (Nat.instPreorder) hc_k0 (0) (0) hc_k1 hc_k2) (by
  decide +kernel)

-- List.SortedGE.getElem_ge_getElem_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGE.getElem_ge_getElem_of_le.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α] ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, j ≤ i → l[i] ≤ l[j] := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) ([0, 1]) (Nat.instPreorder) (1) (0) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- List.SortedGE.getElem_ge_getElem_of_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGE.getElem_ge_getElem_of_le.h6 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedGE → ∀ ⦃i j : ℕ⦄ ⦃hj : j < l.length⦄, j ≤ i → i < l.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) (Nat.instPreorder) (by
  decide) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.SortedGE.getElem_ge_getElem_of_le, hypothesis 7: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.SortedGE.getElem_ge_getElem_of_le.h7.der.{u_1} : ∀ {α : Type u_1} {l : List α} [inst : Preorder α], l.SortedGE → ∀ ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄, j ≤ i → j < l.length := by
  (intros; lia)
theorem HypCheckProof.List.SortedGE.getElem_ge_getElem_of_le.h7.{u_1} : ∀ {α : Type u_1} {l : List α} [inst : Preorder α] (a : l.SortedGE) ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄ (a_1 : j ≤ i),
      l[i] ≤ l[j] := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7
  exact @List.SortedGE.getElem_ge_getElem_of_le hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.List.SortedGE.getElem_ge_getElem_of_le.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7) hc_x7

-- List.SortedGE.getElem_ge_getElem_of_le, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGE.getElem_ge_getElem_of_le.h8 : ¬∀ {α : Type} {l : List α} [inst : Preorder α],
        l.SortedGE → ∀ ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, l[i] ≤ l[j] := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) ([1, 0]) (Nat.instPreorder) hc_k0 (0) (1) hc_k1 hc_k2) (by
  decide +kernel)

-- Set.SurjOn.mono, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.mono.h9 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β}, s₁ ⊆ s₂ → t₁ ⊆ t₂ → Set.SurjOn f s₂ t₁ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  rfl) (by
  rfl)) (by
  simp)

-- Set.BijOn.prodMap, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.prodMap.h10 : ¬∀ {α₁ α₂ β₁ β₂ : Type} {s₁ : Set α₁} {s₂ : Set α₂} {t₁ : Set β₁} {t₂ : Set β₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂},
        Set.BijOn f₂ s₂ t₂ → Set.BijOn (fun (x : α₁ × α₂) => (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.BijOn.prodMap, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.prodMap.h11 : ¬∀ {α₁ α₂ β₁ β₂ : Type} {s₁ : Set α₁} {s₂ : Set α₂} {t₁ : Set β₁} {t₂ : Set β₂} {f₁ : α₁ → β₁} {f₂ : α₂ → β₂},
        Set.BijOn f₁ s₁ t₁ → Set.BijOn (fun (x : α₁ × α₂) => (f₁ x.1, f₂ x.2)) (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- List.prev_ne_cons_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_ne_cons_cons.h6 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (x y z : α), x ≠ y → x ≠ z → x ∈ y :: z :: l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (1) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.prev_ne_cons_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_ne_cons_cons.h7 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (x y z : α), x ∈ y :: z :: l → x ≠ z → x ≠ y := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.prev_ne_cons_cons, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_ne_cons_cons.h8 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (x y z : α) (h : x ∈ y :: z :: l) (hy : x ≠ y),
        (y :: z :: l).prev x h =
          (z :: l).prev x
            ((fun {α : Type} (l : List α) (x y z : α) (h : x ∈ y :: z :: l) (hy : x ≠ y) =>
                Eq.mpr (id List.mem_cons._simp_1)
                  (Eq.mp
                    (Eq.trans List.mem_cons._simp_1
                      (Eq.trans (congr (congrArg Or (eq_false hy)) List.mem_cons._simp_1) (false_or (x = z ∨ x ∈ l))))
                    h))
              l x y z h hy) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (instDecidableEqNat) ([]) (0) (1) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- Set.InjOn.eq_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.eq_iff.h6 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {x y : α}, x ∈ s → y ∈ s → (f x = f y ↔ x = y) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n % 2 = 0}) (fun _ => 0 : ℕ → ℕ) (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.InjOn.eq_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.eq_iff.h7 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {x y : α}, Set.InjOn f s → y ∈ s → (f x = f y ↔ x = y) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (1) (0) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- Set.InjOn.eq_iff, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.eq_iff.h8 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {x y : α}, Set.InjOn f s → x ∈ s → (f x = f y ↔ x = y) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (0) (1) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- Set.InjOn.ne_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.ne_iff.h6 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {x y : α}, x ∈ s → y ∈ s → (f x ≠ f y ↔ x ≠ y) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n % 2 = 0}) (fun _ => 0 : ℕ → ℕ) (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.InjOn.ne_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.ne_iff.h7 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {x y : α}, Set.InjOn f s → y ∈ s → (f x ≠ f y ↔ x ≠ y) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (1) (0) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- Set.InjOn.ne_iff, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.ne_iff.h8 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {x y : α}, Set.InjOn f s → x ∈ s → (f x ≠ f y ↔ x ≠ y) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (0) (1) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Sized.node3R, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.node3R.h6 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {m : Ordnode α} {y : α} {r : Ordnode α},
        m.Sized → r.Sized → (l.node3R x m y r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.nil) (0) (Ordnode.nil) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Sized.node3R, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.node3R.h7 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {m : Ordnode α} {y : α} {r : Ordnode α},
        l.Sized → r.Sized → (l.node3R x m y r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.nil) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Sized.node3R, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.node3R.h8 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {m : Ordnode α} {y : α} {r : Ordnode α},
        l.Sized → m.Sized → (l.node3R x m y r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Sized.node4L, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.node4L.h6 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {m : Ordnode α} {y : α} {r : Ordnode α},
        m.Sized → r.Sized → (l.node4L x m y r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.nil) (0) (Ordnode.nil) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Sized.node4L, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.node4L.h7 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {m : Ordnode α} {y : α} {r : Ordnode α},
        l.Sized → r.Sized → (l.node4L x m y r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil)) (0) (Ordnode.nil) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Sized.node4L, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.node4L.h8 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {m : Ordnode α} {y : α} {r : Ordnode α},
        l.Sized → m.Sized → (l.node4L x m y r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Sized.node3L, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.node3L.h6 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {m : Ordnode α} {y : α} {r : Ordnode α},
        m.Sized → r.Sized → (l.node3L x m y r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.nil) (0) (Ordnode.nil) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Sized.node3L, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.node3L.h7 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {m : Ordnode α} {y : α} {r : Ordnode α},
        l.Sized → r.Sized → (l.node3L x m y r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.nil) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Sized.node3L, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.node3L.h8 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {m : Ordnode α} {y : α} {r : Ordnode α},
        l.Sized → m.Sized → (l.node3L x m y r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Set.InjOn.mem_image_iff, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.mem_image_iff.h8 : ¬∀ {α β : Type} {s s₁ : Set α} {f : α → β} {x : α}, Set.InjOn f s → s₁ ⊆ s → (f x ∈ f '' s₁ ↔ x ∈ s₁) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (1) (by
  simp) (by
  rfl)) (by
  simp)

-- Nat.Prime.dvd_mul_of_dvd_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_mul_of_dvd_ne.h3 : ¬∀ {p1 p2 n : ℕ}, Nat.Prime p1 → Nat.Prime p2 → p1 ∣ n → p2 ∣ n → p1 * p2 ∣ n := fun hc_h => absurd (@hc_h (2) (2) (2) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_mul_of_dvd_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_mul_of_dvd_ne.h6 : ¬∀ {p1 p2 n : ℕ}, p1 ≠ p2 → Nat.Prime p1 → Nat.Prime p2 → p2 ∣ n → p1 * p2 ∣ n := fun hc_h => absurd (@hc_h (3) (2) (2) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_mul_of_dvd_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_mul_of_dvd_ne.h7 : ¬∀ {p1 p2 n : ℕ}, p1 ≠ p2 → Nat.Prime p1 → Nat.Prime p2 → p1 ∣ n → p1 * p2 ∣ n := fun hc_h => absurd (@hc_h (2) (3) (2) (by
  decide) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.sublist_of_subperm_of_pairwise, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sublist_of_subperm_of_pairwise.h5 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Std.Antisymm r] {l₁ l₂ : List α},
        List.Pairwise r l₁ → List.Pairwise r l₂ → l₁.Sublist l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ ([0]) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Finsupp.NonTorsionWeight.eq_zero_of_smul_eq_zero, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finsupp.NonTorsionWeight.eq_zero_of_smul_eq_zero.h7.inst : ¬1 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finsupp.NonTorsionWeight.eq_zero_of_smul_eq_zero.h7.prem0 : 1 • (fun (x : ℕ) => 0) 0 = 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Finsupp.NonTorsionWeight.eq_zero_of_smul_eq_zero.h7 : ¬∀ {σ M R : Type} {inst : Semiring R} {inst_1 : AddCommMonoid M} {inst_2 : Module R M} {w : σ → M} {r : R} {s : σ},
        r • w s = 0 → r = 0 := fun hc_h => HypCheckProof.Finsupp.NonTorsionWeight.eq_zero_of_smul_eq_zero.h7.inst (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instSemiring) (Nat.instAddCommMonoid) (Semiring.toModule) (fun (x : ℕ) => 0) (1) (0) HypCheckProof.Finsupp.NonTorsionWeight.eq_zero_of_smul_eq_zero.h7.prem0)

-- Finsupp.NonTorsionWeight.eq_zero_of_smul_eq_zero, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finsupp.NonTorsionWeight.eq_zero_of_smul_eq_zero.h10.inst : ¬1 = 0 := by
  decide +kernel
theorem HypCheckProof.Finsupp.NonTorsionWeight.eq_zero_of_smul_eq_zero.h10 : ¬∀ {σ M R : Type} {inst : Semiring R} {inst_1 : AddCommMonoid M} {inst_2 : Module R M} {w : σ → M}
        [self : Finsupp.NonTorsionWeight R w] {r : R} {s : σ}, r = 0 := fun hc_h => HypCheckProof.Finsupp.NonTorsionWeight.eq_zero_of_smul_eq_zero.h10.inst (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instSemiring) (Nat.instAddCommMonoid) (Semiring.toModule) (fun (n : ℕ) => n + 1) (@Finsupp.NonTorsionWeight.mk (Nat) (Nat) (Nat) (Nat.instSemiring) (Nat.instAddCommMonoid) (@Semiring.toModule Nat Nat.instSemiring) (fun (n : Nat) =>
      @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by (try dsimp only);   (intros; simp_all; done))) (1) (0))

-- Matrix.map_one, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Matrix.map_one.h9.inst : Not
      (@Eq (Matrix Bool Bool Bool)
        (@Matrix.map Bool Bool Nat Bool
          (@OfNat.ofNat (Matrix Bool Bool Nat) (nat_lit 1)
            (@One.toOfNat1 (Matrix Bool Bool Nat)
              (@Matrix.one Bool Nat instDecidableEqBool (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instOne)))
          fun (x : Nat) => Bool.true)
        (@OfNat.ofNat (Matrix Bool Bool Bool) (nat_lit 1)
          (@One.toOfNat1 (Matrix Bool Bool Bool)
            (@Matrix.one Bool Bool instDecidableEqBool instZeroBool_mathlib instOneBool_mathlib)))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Matrix.map_one.h9.prem0 : @Eq Bool ((fun (x : Nat) => Bool.true) (@OfNat.ofNat Nat (nat_lit 1) (@One.toOfNat1 Nat Nat.instOne)))
      (@OfNat.ofNat Bool (nat_lit 1) (@One.toOfNat1 Bool instOneBool_mathlib)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Matrix.map_one.h9 : Not
      (∀ {n α β : Type} [inst : DecidableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β] [inst_4 : One β]
        (f : α → β),
        @Eq β (f (@OfNat.ofNat α (nat_lit 1) (@One.toOfNat1 α inst_2)))
            (@OfNat.ofNat β (nat_lit 1) (@One.toOfNat1 β inst_4)) →
          @Eq (Matrix n n β)
            (@Matrix.map n n α β
              (@OfNat.ofNat (Matrix n n α) (nat_lit 1) (@One.toOfNat1 (Matrix n n α) (@Matrix.one n α inst inst_1 inst_2)))
              f)
            (@OfNat.ofNat (Matrix n n β) (nat_lit 1) (@One.toOfNat1 (Matrix n n β) (@Matrix.one n β inst inst_3 inst_4)))) := fun hc_h => HypCheckProof.Matrix.map_one.h9.inst (@hc_h (Bool) (Nat) (Bool) (instDecidableEqBool) (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (Nat.instOne) (instZeroBool_mathlib) (instOneBool_mathlib) (fun (x : Nat) => Bool.true) HypCheckProof.Matrix.map_one.h9.prem0)

-- Matrix.map_one, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.map_one.h10 : Not
      (∀ {n α β : Type} [inst : DecidableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β] [inst_4 : One β]
        (f : α → β),
        @Eq β (f (@OfNat.ofNat α (nat_lit 0) (@Zero.toOfNat0 α inst_1)))
            (@OfNat.ofNat β (nat_lit 0) (@Zero.toOfNat0 β inst_3)) →
          @Eq (Matrix n n β)
            (@Matrix.map n n α β
              (@OfNat.ofNat (Matrix n n α) (nat_lit 1) (@One.toOfNat1 (Matrix n n α) (@Matrix.one n α inst inst_1 inst_2)))
              f)
            (@OfNat.ofNat (Matrix n n β) (nat_lit 1) (@One.toOfNat1 (Matrix n n β) (@Matrix.one n β inst inst_3 inst_4)))) := fun hc_h => absurd (@hc_h (Bool) (Nat) (Nat) (instDecidableEqBool) (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (Nat.instOne) (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (Nat.instOne) (fun _ => 0 : Nat → Nat) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Ordnode.balanceL_eq_balance, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.balanceL_eq_balance.h5 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α},
        l.Sized →
          (l.size = 0 → r.size ≤ 1) →
            (1 ≤ l.size → 1 ≤ r.size → r.size ≤ Ordnode.delta * l.size) → l.balanceL x r = l.balance x r := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  (repeat' constructor) <;> done) (by
  decide) (by
  decide)) (by
  nofun)

-- Ordnode.balance_eq_balance', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.balance_eq_balance'.h6 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α},
        l.Balanced → r.Balanced → r.Sized → l.balance x r = l.balance' x r := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.nil) (by
  decide) (by
  decide) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.balance_eq_balance', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.balance_eq_balance'.h7 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α},
        l.Balanced → r.Balanced → l.Sized → l.balance x r = l.balance' x r := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  decide) (by
  decide) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Nat.one_le_ofNat, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.one_le_ofNat.h7 : ¬∀ {α : Type} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α] [inst_3 : ZeroLEOneClass α]
        [inst : CharZero α] {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddMonoidWithOne) (Nat.instPartialOrder) _ _ _ (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Int.div_lt_div_iff_of_dvd_of_pos_of_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_div_iff_of_dvd_of_pos_of_neg.h4 : ¬∀ {a b c d : ℤ}, d < 0 → b ∣ a → d ∣ c → (a / b < c / d ↔ c * b < d * a) := fun hc_h => absurd (@hc_h (0) (0) (-1) (-1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_lt_div_iff_of_dvd_of_pos_of_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_div_iff_of_dvd_of_pos_of_neg.h5 : ¬∀ {a b c d : ℤ}, 0 < b → b ∣ a → d ∣ c → (a / b < c / d ↔ c * b < d * a) := fun hc_h => absurd (@hc_h (0) (1) (1) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.mergeSort_eq_self, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mergeSort_eq_self.h7 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] [inst_1 : Std.Total r] [inst_2 : IsTrans α r]
        [inst_3 : Std.Antisymm r] {l : List α}, (l.mergeSort fun (x1 x2 : α) => Decidable.decide (r x1 x2)) = l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (Nat.decLe) _ _ _ ([1, 0])) (by
  simp)

-- Int.div_le_div_iff_of_dvd_of_neg_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_le_div_iff_of_dvd_of_neg_of_pos.h4 : ¬∀ {a b c d : ℤ}, 0 < d → b ∣ a → d ∣ c → (a / b ≤ c / d ↔ c * b ≤ d * a) := fun hc_h => absurd (@hc_h (0) (0) (-1) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_le_div_iff_of_dvd_of_neg_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_le_div_iff_of_dvd_of_neg_of_pos.h5 : ¬∀ {a b c d : ℤ}, b < 0 → b ∣ a → d ∣ c → (a / b ≤ c / d ↔ c * b ≤ d * a) := fun hc_h => absurd (@hc_h (-1) (-1) (0) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.get_insertIdx_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.get_insertIdx_of_lt.h5 : ¬∀ {α : Type} (l : List α) (x : α) (n k : ℕ) (hk : k < l.length)
        (hk' : autoParam (k < (l.insertIdx n x).length) List.get_insertIdx_of_lt._auto_1),
        (l.insertIdx n x).get (⟨k, hk'⟩ : Fin (l.insertIdx n x).length) = l.get (⟨k, hk⟩ : Fin l.length) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) ([0]) (1) (0) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- List.get_insertIdx_of_lt, hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.get_insertIdx_of_lt.h6.der.{u} : ∀ {α : Type u} (l : List α) (x : α) (n k : ℕ),
      k < n → autoParam (k < (l.insertIdx n x).length) List.get_insertIdx_of_lt._auto_1 → k < l.length := by
  (intros; grind)
theorem HypCheckProof.List.get_insertIdx_of_lt.h6.{u} : ∀ {α : Type u} (l : List α) (x : α) (n k : ℕ) (hn : k < n)
      (hk' : autoParam (k < (l.insertIdx n x).length) List.get_insertIdx_of_lt._auto_1),
      (l.insertIdx n x).get (⟨k, hk'⟩ : Fin (l.insertIdx n x).length) =
        l.get (⟨k, HypCheckProof.List.get_insertIdx_of_lt.h6.der l x n k hn hk'⟩ : Fin l.length) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @List.get_insertIdx_of_lt hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.List.get_insertIdx_of_lt.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6) hc_x6

-- List.get_insertIdx_of_lt, hypothesis 7: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.get_insertIdx_of_lt.h7.der.{u} : ∀ {α : Type u} (l : List α) (x : α) (n k : ℕ), k < n → k < l.length → k < (l.insertIdx n x).length := by
  (intros; grind)
theorem HypCheckProof.List.get_insertIdx_of_lt.h7.{u} : ∀ {α : Type u} (l : List α) (x : α) (n k : ℕ) (hn : k < n) (hk : k < l.length),
      (l.insertIdx n x).get
          (⟨k, HypCheckProof.List.get_insertIdx_of_lt.h7.der l x n k hn hk⟩ : Fin (l.insertIdx n x).length) =
        l.get (⟨k, hk⟩ : Fin l.length) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @List.get_insertIdx_of_lt hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.List.get_insertIdx_of_lt.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6)

-- List.SortedLT.getElem_le_getElem_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.getElem_le_getElem_iff.h3 : ¬∀ {α : Type} {l : List α} [inst : LinearOrder α] {i j : ℕ} {hi : i < l.length} {hj : j < l.length}, l[i] ≤ l[j] ↔ i ≤ j := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) ([1, 0]) (Nat.instLinearOrder) (0) (1) hc_k0 hc_k1) (by
  decide +kernel)

-- List.SortedLT.getElem_le_getElem_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.getElem_le_getElem_iff.h6 : ¬∀ {α : Type} {l : List α} [inst : LinearOrder α], l.SortedLT → ∀ {i j : ℕ} {hj : j < l.length}, i < l.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) (Nat.instLinearOrder) (by
  decide) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.SortedLT.getElem_le_getElem_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.getElem_le_getElem_iff.h7 : ¬∀ {α : Type} {l : List α} [inst : LinearOrder α], l.SortedLT → ∀ {i j : ℕ} {hi : i < l.length}, j < l.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) (Nat.instLinearOrder) (by
  decide) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.SortedGT.getElem_lt_getElem_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.getElem_lt_getElem_iff.h3 : ¬∀ {α : Type} {l : List α} [inst : LinearOrder α] {i j : ℕ} {hi : i < l.length} {hj : j < l.length}, l[i] < l[j] ↔ j < i := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) ([0, 1]) (Nat.instLinearOrder) (0) (1) hc_k0 hc_k1) (by
  decide +kernel)

-- List.SortedGT.getElem_lt_getElem_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.getElem_lt_getElem_iff.h6 : ¬∀ {α : Type} {l : List α} [inst : LinearOrder α], l.SortedGT → ∀ {i j : ℕ} {hj : j < l.length}, i < l.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) (Nat.instLinearOrder) (by
  decide) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.SortedGT.getElem_lt_getElem_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.getElem_lt_getElem_iff.h7 : ¬∀ {α : Type} {l : List α} [inst : LinearOrder α], l.SortedGT → ∀ {i j : ℕ} {hi : i < l.length}, j < l.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) (Nat.instLinearOrder) (by
  decide) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.orderedInsert, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.orderedInsert.h3 : ¬∀ {α : Type} {r : α → α → Prop} [inst : DecidableRel r] [inst_1 : IsTrans α r] (a : α) (l : List α),
        List.Pairwise r l → List.Pairwise r (List.orderedInsert r a l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ (0) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.orderedInsert, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.orderedInsert.h7 : ¬∀ {α : Type} {r : α → α → Prop} [inst : DecidableRel r] [inst_1 : Std.Total r] [inst_2 : IsTrans α r] (a : α)
        (l : List α), List.Pairwise r (List.orderedInsert r a l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (Nat.decLe) _ _ (0) ([1, 0])) (by
  decide +kernel)

-- image_subtype_univ_ssubset_image_univ, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.image_subtype_univ_ssubset_image_univ.h6.inst : ¬Finset.image (fun (i : { a : Bool // (fun (n : ℕ) => n = 0) ((fun (x : Bool) => 0) a) }) => (fun (x : Bool) => 0) ↑i)
          Finset.univ ⊂
        Finset.image (fun (x : Bool) => 0) Finset.univ := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.image_subtype_univ_ssubset_image_univ.h6.prem0 : ¬(fun (n : ℕ) => n = 0) 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.image_subtype_univ_ssubset_image_univ.h6 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : DecidableEq β] (k : β) (b : α → β) (p : β → Prop)
        [inst_2 : DecidablePred p],
        ¬p k → Finset.image (fun (i : { a : α // p (b a) }) => b ↑i) Finset.univ ⊂ Finset.image b Finset.univ := fun hc_h => HypCheckProof.image_subtype_univ_ssubset_image_univ.h6.inst (@hc_h (Bool) (ℕ) (Bool.fintype) (instDecidableEqNat) (1) (fun (x : Bool) => 0) (fun (n : ℕ) => n = 0) (fun (a : ℕ) => instDecidableEqNat a 0) HypCheckProof.image_subtype_univ_ssubset_image_univ.h6.prem0)

-- image_subtype_univ_ssubset_image_univ, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.image_subtype_univ_ssubset_image_univ.h9 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : DecidableEq β] (k : β) (b : α → β),
        k ∈ Finset.image b Finset.univ →
          ∀ (p : β → Prop) [inst_2 : DecidablePred p],
            Finset.image (fun (i : { a : α // p (b a) }) => b ↑i) Finset.univ ⊂ Finset.image b Finset.univ := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (instDecidableEqNat) (0) (fun _ => 0 : Bool → ℕ) (by
  decide) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0)) (by
  decide +kernel)

-- Set.nontrivial_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_of_lt.h5 : ¬∀ {α : Type} {s : Set α} [inst : Preorder α] {x y : α}, y ∈ s → x < y → s.Nontrivial := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) (Bool.instPartialOrder.toPreorder) (Bool.false) (Bool.true) (by
  decide) (by
  decide)) (by
  simp)

-- Set.nontrivial_of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_of_lt.h6 : ¬∀ {α : Type} {s : Set α} [inst : Preorder α] {x y : α}, x ∈ s → x < y → s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (Nat.instPreorder) (0) (1) (by
  decide) (by
  decide)) (by
  simp)

-- Set.nontrivial_of_lt, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_of_lt.h7 : ¬∀ {α : Type} {s : Set α} [inst : Preorder α] {x y : α}, x ∈ s → y ∈ s → s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (Nat.instPreorder) (0) (0) (by
  decide) (by
  decide)) (by
  simp)

-- Nat.ModEq.cancel_right_div_gcd', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.cancel_right_div_gcd'.h5 : ¬∀ {m a b c d : ℕ}, c ≡ d [MOD m] → a * c ≡ b * d [MOD m] → a ≡ b [MOD m / m.gcd c] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.cancel_right_div_gcd', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.cancel_right_div_gcd'.h6 : ¬∀ {m a b c d : ℕ}, 0 < m → a * c ≡ b * d [MOD m] → a ≡ b [MOD m / m.gcd c] := fun hc_h => absurd (@hc_h (2) (0) (1) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.cancel_right_div_gcd', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.cancel_right_div_gcd'.h7 : ¬∀ {m a b c d : ℕ}, 0 < m → c ≡ d [MOD m] → a ≡ b [MOD m / m.gcd c] := fun hc_h => absurd (@hc_h (2) (0) (1) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.ncard_le_ncard_of_injOn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_le_ncard_of_injOn.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} (f : α → β),
        Set.InjOn f s → autoParam t.Finite Set.ncard_le_ncard_of_injOn._auto_1 → s.ncard ≤ t.ncard := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ) (by
  simp) (by
  simp)) (by
  simp)

-- Set.ncard_le_ncard_of_injOn, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_le_ncard_of_injOn.h7 : ¬∀ {α β : Type} {s : Set α} {t : Set β} (f : α → β), (∀ a ∈ s, f a ∈ t) → Set.InjOn f s → s.ncard ≤ t.ncard := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | True}) (fun n => n + 1 : ℕ → ℕ) (by
  simp) (by
  simp)) (by
  simp)

-- Set.MapsTo.prodMk, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.prodMk.h8 : ¬∀ {α β₁ β₂ : Type} {s : Set α} {t₁ : Set β₁} {t₂ : Set β₂} {f₁ : α → β₁} {f₂ : α → β₂},
        Set.MapsTo f₂ s t₂ → Set.MapsTo (fun (x : α) => (f₁ x, f₂ x)) s (t₁ ×ˢ t₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.MapsTo.prodMk, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.prodMk.h9 : ¬∀ {α β₁ β₂ : Type} {s : Set α} {t₁ : Set β₁} {t₂ : Set β₂} {f₁ : α → β₁} {f₂ : α → β₂},
        Set.MapsTo f₁ s t₁ → Set.MapsTo (fun (x : α) => (f₁ x, f₂ x)) s (t₁ ×ˢ t₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Equiv.Finset.union_symm_right, hypothesis 7: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Equiv.Finset.union_symm_right.h7.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α}, Disjoint s t → ∀ {i : α}, i ∈ t → i ∈ s ∪ t := by
  (intros; simp_all; done)
theorem HypCheckProof.Equiv.Finset.union_symm_right.h7.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} (h : Disjoint s t) {i : α} (hi : i ∈ t),
      (Equiv.Finset.union s t h).symm (⟨i, HypCheckProof.Equiv.Finset.union_symm_right.h7.der h hi⟩ : ↥(s ∪ t)) =
        Sum.inr (⟨i, hi⟩ : ↥t) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Equiv.Finset.union_symm_right hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.Equiv.Finset.union_symm_right.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6)

-- Equiv.Finset.union_symm_left, hypothesis 7: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Equiv.Finset.union_symm_left.h7.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α}, Disjoint s t → ∀ {i : α}, i ∈ s → i ∈ s ∪ t := by
  (intros; simp_all; done)
theorem HypCheckProof.Equiv.Finset.union_symm_left.h7.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} (h : Disjoint s t) {i : α} (hi : i ∈ s),
      (Equiv.Finset.union s t h).symm (⟨i, HypCheckProof.Equiv.Finset.union_symm_left.h7.der h hi⟩ : ↥(s ∪ t)) =
        Sum.inl (⟨i, hi⟩ : ↥s) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Equiv.Finset.union_symm_left hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.Equiv.Finset.union_symm_left.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6)

-- Finset.isPWO_support_mulAntidiagonal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.isPWO_support_mulAntidiagonal.h3 : ¬∀ {α : Type} [inst : CommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO},
        IsOrderedCancelMonoid α := fun hc_h => absurd (@hc_h (Bool) (BooleanRing.toCommRing.toCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp)) (by
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

-- Finset.support_addAntidiagonal_subset_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.support_addAntidiagonal_subset_add.h3 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO},
        IsOrderedCancelAddMonoid α := fun hc_h => absurd (@hc_h (Bool) (CommRing.toCommSemiring.toAddCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedAddMonoid.add_le_add_left (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.isPWO_support_antidiagonal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.isPWO_support_antidiagonal.h3 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO},
        IsOrderedCancelAddMonoid α := fun hc_h => absurd (@hc_h (Bool) (CommRing.toCommSemiring.toAddCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toIsOrderedAddMonoid.add_le_add_left (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENat.iSup_add_iSup_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.iSup_add_iSup_le.h7 : ¬∀ {ι κ : Type} {f : ι → ℕ∞} {a : ℕ∞} [inst : Nonempty ι] [inst : Nonempty κ] {g : κ → ℕ∞}, iSup f + iSup g ≤ a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => 0) (0) _ _ (fun (a : ℕ) => 1)) (by
  simp)

-- Function.Injective.sumElim, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.sumElim.h7 : ¬∀ {α β γ : Type} {f : α → γ} {g : β → γ},
        Function.Injective f → Function.Injective g → Function.Injective (Sum.elim f g) := fun hc_h => absurd (@hc_h (Bool) (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.append_overlap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.append_overlap.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l₁ l₂ l₃ : List α},
        List.IsChain R (l₂ ++ l₃) → l₂ ≠ [] → List.IsChain R (l₁ ++ l₂ ++ l₃) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) ([0]) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.append_overlap, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.append_overlap.h6 : ¬∀ {α : Type} {R : α → α → Prop} {l₁ l₂ l₃ : List α},
        List.IsChain R (l₁ ++ l₂) → l₂ ≠ [] → List.IsChain R (l₁ ++ l₂ ++ l₃) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([0]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.append_overlap, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.append_overlap.h7 : ¬∀ {α : Type} {R : α → α → Prop} {l₁ l₂ l₃ : List α},
        List.IsChain R (l₁ ++ l₂) → List.IsChain R (l₂ ++ l₃) → List.IsChain R (l₁ ++ l₂ ++ l₃) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) ([]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- AList.mem_lookup_union_middle, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.AList.mem_lookup_union_middle.h8 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {b : β a} {s₁ s₂ s₃ : AList β},
        a ∉ s₂ → b ∈ AList.lookup a (s₁ ∪ s₂ ∪ s₃) := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) (0) (∅) (∅) (∅) (by
  decide)) (by
  decide +kernel)

-- Sum.LiftRel.exists_of_isLeft_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sum.LiftRel.exists_of_isLeft_right.h8 : ¬∀ {α β γ δ : Type} {r : α → γ → Prop} {s : β → δ → Prop} {x : α ⊕ β} {y : γ ⊕ δ},
        y.isLeft = Bool.true → ∃ (a : α) (c : γ), r a c ∧ x = Sum.inl a ∧ y = Sum.inl c := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (Sum.inl 0) (Sum.inl 0) (by
  decide)) (by
  simp)

-- Set.bijOn_of_subsingleton', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.bijOn_of_subsingleton'.h7 : ¬∀ {α β : Type} {s : Set α} {t : Set β} [inst : Subsingleton α] [inst : Subsingleton β] (f : α → β), Set.BijOn f s t := fun hc_h => absurd (@hc_h (Unit) (Unit) (∅) (⊤) _ _ (fun (a : Unit) => PUnit.unit)) (by
  simp)

-- Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion.h7 : ¬∀ {α ι : Type} {f : ι → Set α} {s t : Set ι}, (s ∪ t).PairwiseDisjoint f → (∀ i ∈ s, (f i).Nonempty) → s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (by
  simp)) (by
  simp)

-- List.IsPrefix.idxOf_eq_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.idxOf_eq_of_mem.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] {a : α}, a ∈ l₁ → List.idxOf a l₁ = List.idxOf a l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([1]) (instBEqOfDecidableEq) _ (0) (by
  decide)) (by
  decide +kernel)

-- List.IsPrefix.idxOf_eq_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.idxOf_eq_of_mem.h7 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α],
        l₁ <+: l₂ → ∀ {a : α}, List.idxOf a l₁ = List.idxOf a l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (instBEqOfDecidableEq) _ (by
  decide) (1)) (by
  decide +kernel)

-- Set.SurjOn.of_comp, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.of_comp.h8 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ}, Set.MapsTo f s t → Set.SurjOn g t p := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.SurjOn.of_comp, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.of_comp.h9 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ}, Set.SurjOn (g ∘ f) s p → Set.SurjOn g t p := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.false}) (fun n => n + 1 : ℕ → ℕ) (fun n => n % 2 == 0 : ℕ → Bool) (by
  simp)) (by
  simp)

-- Finsupp.instCanonicallyOrderedAddOfAddLeftMono, hypothesis 7: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finsupp.instCanonicallyOrderedAddOfAddLeftMono.h7.gneg.{u_1, u_3} : ∀ {ι : Type u_1} {α : Type u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [inst_2 : CanonicallyOrderedAdd α]
      [inst_3 : Sub α] [inst_4 : OrderedSub α], ¬AddLeftMono α → CanonicallyOrderedAdd (ι →₀ α) := by
  (intros; infer_instance)
theorem HypCheckProof.Finsupp.instCanonicallyOrderedAddOfAddLeftMono.h7.{u_1, u_3} : ∀ {ι : Type u_1} {α : Type u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [inst_2 : CanonicallyOrderedAdd α]
      [inst_3 : Sub α] [inst_4 : OrderedSub α], CanonicallyOrderedAdd (ι →₀ α) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact Classical.byCases (fun hc_h => @Finsupp.instCanonicallyOrderedAddOfAddLeftMono hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_h) (fun hc_hn => @HypCheckProof.Finsupp.instCanonicallyOrderedAddOfAddLeftMono.h7.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_hn)
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finsupp.instCanonicallyOrderedAddOfAddLeftMono.h7.derivable.{u_1, u_3} : ∀ {ι : Type u_1} {α : Type u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [inst_2 : CanonicallyOrderedAdd α]
      [inst_3 : Sub α] [inst_4 : OrderedSub α], AddLeftMono α := by
  (intros; infer_instance)

-- Set.EqOn.comp_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.comp_right.h8 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {f : α → β} {g₁ g₂ : β → γ}, Set.MapsTo f s t → Set.EqOn (g₁ ∘ f) (g₂ ∘ f) s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.MemUnion.elim, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MemUnion.elim.h5 : ¬∀ {α : Type} {x : α} {a b : Set α} {P : Prop}, (x ∈ a → P) → (x ∈ b → P) → P := fun hc_h => absurd (@hc_h (ℕ) (1) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (False) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.MemUnion.elim, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MemUnion.elim.h6 : ¬∀ {α : Type} {x : α} {a b : Set α} {P : Prop}, x ∈ a ∪ b → (x ∈ b → P) → P := fun hc_h => absurd (@hc_h (ℕ) (0) ({n : ℕ | n = 0}) ({x : ℕ | False}) (False) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.MemUnion.elim, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MemUnion.elim.h7 : ¬∀ {α : Type} {x : α} {a b : Set α} {P : Prop}, x ∈ a ∪ b → (x ∈ a → P) → P := fun hc_h => absurd (@hc_h (ℕ) (0) ({x : ℕ | False}) ({n : ℕ | n = 0}) (False) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.rel_get_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_get_of_le.h2 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α}, List.Pairwise R l → ∀ {a b : Fin l.length}, a ≤ b → R (l.get a) (l.get b) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (by
  decide) (0) (0) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.rel_get_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_get_of_le.h4 : ¬∀ {α : Type} {R : α → α → Prop} [inst : Std.Refl R] {l : List α} {a b : Fin l.length}, a ≤ b → R (l.get a) (l.get b) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) _ ([1, 0]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.rel_get_of_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_get_of_le.h7 : ¬∀ {α : Type} {R : α → α → Prop} [inst : Std.Refl R] {l : List α},
        List.Pairwise R l → ∀ {a b : Fin l.length}, R (l.get a) (l.get b) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) _ ([0, 1]) (by
  decide) (1) (0)) (by
  decide +kernel)

-- Nat.choose_lt_pow_div, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_lt_pow_div.h6 : Not
      (∀ {α : Type} [inst : Semifield α] [inst_1 : LinearOrder α]
        [inst_2 :
          @IsStrictOrderedRing α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))
            (@SemilatticeInf.toPartialOrder α
              (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))]
        {n k : Nat},
        @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k →
          @LT.lt α
            (@Preorder.toLT α
              (@PartialOrder.toPreorder α
                (@SemilatticeInf.toPartialOrder α
                  (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
            (@Nat.cast α
              (@AddMonoidWithOne.toNatCast α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α
                    (@Semiring.toNonAssocSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))
              (n.choose k))
            (@HDiv.hDiv α α α
              (@instHDiv α
                (@DivInvMonoid.toDiv α
                  (@GroupWithZero.toDivInvMonoid α
                    (@DivisionSemiring.toGroupWithZero α (@Semifield.toDivisionSemiring α inst)))))
              (@HPow.hPow α Nat α
                (@instHPow α Nat
                  (@NPow.toPow α
                    (@Monoid.toNPow α
                      (@Semiring.toMonoid α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))
                (@Nat.cast α
                  (@AddMonoidWithOne.toNatCast α
                    (@AddCommMonoidWithOne.toAddMonoidWithOne α
                      (@NonAssocSemiring.toAddCommMonoidWithOne α
                        (@Semiring.toNonAssocSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))
                  n)
                k)
              (@Nat.cast α
                (@AddMonoidWithOne.toNatCast α
                  (@AddCommMonoidWithOne.toAddMonoidWithOne α
                    (@NonAssocSemiring.toAddCommMonoidWithOne α
                      (@Semiring.toNonAssocSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))
                k.factorial))) := fun hc_h => absurd (@hc_h (Rat) (@Field.toSemifield Rat Rat.instField) (Rat.linearOrder) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Nat.choose_lt_pow_div, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_lt_pow_div.h7 : Not
      (∀ {α : Type} [inst : Semifield α] [inst_1 : LinearOrder α]
        [inst_2 :
          @IsStrictOrderedRing α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))
            (@SemilatticeInf.toPartialOrder α
              (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))]
        {n k : Nat},
        @Ne Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @LT.lt α
            (@Preorder.toLT α
              (@PartialOrder.toPreorder α
                (@SemilatticeInf.toPartialOrder α
                  (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
            (@Nat.cast α
              (@AddMonoidWithOne.toNatCast α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α
                    (@Semiring.toNonAssocSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))
              (n.choose k))
            (@HDiv.hDiv α α α
              (@instHDiv α
                (@DivInvMonoid.toDiv α
                  (@GroupWithZero.toDivInvMonoid α
                    (@DivisionSemiring.toGroupWithZero α (@Semifield.toDivisionSemiring α inst)))))
              (@HPow.hPow α Nat α
                (@instHPow α Nat
                  (@NPow.toPow α
                    (@Monoid.toNPow α
                      (@Semiring.toMonoid α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))
                (@Nat.cast α
                  (@AddMonoidWithOne.toNatCast α
                    (@AddCommMonoidWithOne.toAddMonoidWithOne α
                      (@NonAssocSemiring.toAddCommMonoidWithOne α
                        (@Semiring.toNonAssocSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))
                  n)
                k)
              (@Nat.cast α
                (@AddMonoidWithOne.toNatCast α
                  (@AddCommMonoidWithOne.toAddMonoidWithOne α
                    (@NonAssocSemiring.toAddCommMonoidWithOne α
                      (@Semiring.toNonAssocSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))
                k.factorial))) := fun hc_h => absurd (@hc_h (Rat) (@Field.toSemifield Rat Rat.instField) (Rat.linearOrder) _ (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_choose_of_lt_three_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose_of_lt_three_mul.h3 : ¬∀ {p n k : ℕ}, p ≤ k → p ≤ n - k → n < 3 * p → (n.choose k).factorization p = 0 := fun hc_h => absurd (@hc_h (2) (4) (2) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_choose_of_lt_three_mul, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose_of_lt_three_mul.h4 : ¬∀ {p n k : ℕ}, p ≠ 2 → p ≤ n - k → n < 3 * p → (n.choose k).factorization p = 0 := fun hc_h => absurd (@hc_h (3) (6) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_choose_of_lt_three_mul, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose_of_lt_three_mul.h5 : ¬∀ {p n k : ℕ}, p ≠ 2 → p ≤ k → n < 3 * p → (n.choose k).factorization p = 0 := fun hc_h => absurd (@hc_h (3) (6) (4) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_choose_of_lt_three_mul, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose_of_lt_three_mul.h6 : ¬∀ {p n k : ℕ}, p ≠ 2 → p ≤ k → p ≤ n - k → (n.choose k).factorization p = 0 := fun hc_h => absurd (@hc_h (3) (9) (3) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Finsupp.support_single_disjoint, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.support_single_disjoint.h5 : ¬∀ {α M : Type} [inst : Zero M] {b b' : M},
        b' ≠ 0 → ∀ {i j : α}, Disjoint (fun₀ | i => b).support (fun₀ | j => b').support ↔ i ≠ j := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (0) (1) (by
  decide) (0) (0)) (by
  simp)

-- Finsupp.support_single_disjoint, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.support_single_disjoint.h6 : ¬∀ {α M : Type} [inst : Zero M] {b b' : M},
        b ≠ 0 → ∀ {i j : α}, Disjoint (fun₀ | i => b).support (fun₀ | j => b').support ↔ i ≠ j := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (1) (0) (by
  decide) (0) (0)) (by
  simp)

-- Function.eq_of_sigmaMk_comp, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.eq_of_sigmaMk_comp.h8 : ¬∀ {α : Type} {β : α → Type} {γ : Type} [inst : Nonempty γ] {a b : α} {f : γ → β a} {g : γ → β b}, a = b ∧ f ≍ g := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (ℕ) _ (0) (1) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Finsupp.comapDomain_single_of_notMem_range, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.comapDomain_single_of_notMem_range.h6 : ¬∀ {α β M : Type} [inst : Zero M] {f : α → β} {b : β} (m : M) (hf : Set.InjOn f (f ⁻¹' ↑(fun₀ | b => m).support)),
        Finsupp.comapDomain f (fun₀ | b => m) hf = 0 := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (fun n => n + 1 : ℕ → ℕ) (1) (1) hc_k0) (by
  simp)

-- List.append_cons_inj_of_notMem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.append_cons_inj_of_notMem.h7 : ¬∀ {α : Type} {x₁ x₂ z₁ z₂ : List α} {a₁ a₂ : α},
        a₂ ∉ z₁ → (x₁ ++ a₁ :: z₁ = x₂ ++ a₂ :: z₂ ↔ x₁ = x₂ ∧ a₁ = a₂ ∧ z₁ = z₂) := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) ([]) ([0]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- List.append_cons_inj_of_notMem, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.append_cons_inj_of_notMem.h8 : ¬∀ {α : Type} {x₁ x₂ z₁ z₂ : List α} {a₁ a₂ : α},
        a₂ ∉ x₁ → (x₁ ++ a₁ :: z₁ = x₂ ++ a₂ :: z₂ ↔ x₁ = x₂ ∧ a₁ = a₂ ∧ z₁ = z₂) := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) ([0]) ([]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Function.Semiconj.surjOn_image, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Semiconj.surjOn_image.h7 : ¬∀ {α β : Type} {fa : α → α} {fb : β → β} {f : α → β} {s t : Set α}, Set.SurjOn fa s t → Set.SurjOn fb (f '' s) (f '' t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- List.isChain_cons_map_of_isChain_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isChain_cons_map_of_isChain_cons.h6 : ¬∀ {α β : Type} {R : α → α → Prop} {a : α} {S : β → β → Prop} (f : α → β) {l : List α},
        List.IsChain R (a :: l) → List.IsChain S (f a :: List.map f l) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (0) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.isChain_cons_map_of_isChain_cons, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isChain_cons_map_of_isChain_cons.h8 : ¬∀ {α β : Type} {R : α → α → Prop} {a : α} {S : β → β → Prop} (f : α → β),
        (∀ (a b : α), R a b → S (f a) (f b)) → ∀ {l : List α}, List.IsChain S (f a :: List.map f l) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ) (by
  simp) ([0])) (by
  decide +kernel)

-- Rat.isInt_intFloor_ofIsRat_neg, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.isInt_intFloor_ofIsRat_neg.h8 : Not
      (∀ {α : Type} [inst : Field α] [inst_1 : LinearOrder α]
        [inst_2 :
          @IsStrictOrderedRing α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α (@Field.toSemifield α inst)))
            (@SemilatticeInf.toPartialOrder α
              (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))]
        [inst_3 : @FloorRing α (@DivisionRing.toRing α (@Field.toDivisionRing α inst)) inst_1] (r : α) (n d : Nat),
        @Mathlib.Meta.NormNum.IsInt Int Int.instRing
          (@Int.floor α (@DivisionRing.toRing α (@Field.toDivisionRing α inst)) inst_1 inst_3 r)
          (Int.negOfNat
            (@Neg.neg Int Int.instNegInt
                (@HDiv.hDiv Int Int Int (@instHDiv Int Int.instDiv)
                  (@Neg.neg Int Int.instNegInt (@Nat.cast Int instNatCastInt n)) (@Nat.cast Int instNatCastInt d))).toNat)) := fun hc_h => absurd (@hc_h (Rat) (Rat.instField) (Rat.linearOrder) _ (Rat.instFloorRing) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  nofun)

-- Rat.isNat_intFloor_ofIsNNRat, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.isNat_intFloor_ofIsNNRat.h8 : ¬∀ {α : Type} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStrictOrderedRing α] [inst_3 : FloorRing α] (r : α)
        (n d : ℕ), Mathlib.Meta.NormNum.IsNat ⌊r⌋ (n / d) := fun hc_h => absurd (@hc_h (ℚ) (Rat.instField) (Rat.linearOrder) _ (Rat.instFloorRing) (1) (0) (0)) (by
  nofun)

-- Fin.heq_fun₂_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.heq_fun₂_iff.h5 : ¬∀ {α : Type} {k l k' l' : ℕ}, k' = l' → ∀ {f : Fin k → Fin k' → α} {g : Fin l → Fin l' → α}, k = l := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (fun (a a_1 : Fin 0) => 0) (fun (a : Fin 1) (a_1 : Fin 0) => 0)) (by
  decide +kernel)

-- Fin.heq_fun₂_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.heq_fun₂_iff.h6 : ¬∀ {α : Type} {k l k' l' : ℕ}, k = l → ∀ {f : Fin k → Fin k' → α} {g : Fin l → Fin l' → α}, k' = l' := fun hc_h => absurd (@hc_h (ℕ) (0) (0) (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (fun (a a_1 : Fin 0) => 0) (fun (a : Fin 0) (a_1 : Fin 1) => 0)) (by
  decide +kernel)

-- Fintype.card_compl_eq_card_compl, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_compl_eq_card_compl.h8 : ¬∀ {α : Type} [inst : Finite α] (p q : α → Prop) [inst : Fintype { x : α // p x }] [inst : Fintype { x : α // ¬p x }]
        [inst_1 : Fintype { x : α // q x }] [inst_2 : Fintype { x : α // ¬q x }],
        Fintype.card { x : α // ¬p x } = Fintype.card { x : α // ¬q x } := fun hc_h => absurd (@hc_h (Bool) _ (fun b => b = true : Bool → Prop) (fun _ => False : Bool → Prop) (Fintype.subtypeEq Bool.true) (Subtype.fintype fun (x : Bool) => ¬(fun (b : Bool) => b = Bool.true) x) (Subtype.fintype fun (x : Bool) => False) (Subtype.fintype fun (x : Bool) => ¬(fun (x : Bool) => False) x)) (by
  decide +kernel)

-- Nat.Prime.dvd_choose, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose.h4 : ¬∀ {p a b : ℕ}, Nat.Prime p → b - a < p → p ≤ b → p ∣ b.choose a := fun hc_h => absurd (@hc_h (2) (2) (2) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_choose, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose.h5 : ¬∀ {p a b : ℕ}, Nat.Prime p → a < p → p ≤ b → p ∣ b.choose a := fun hc_h => absurd (@hc_h (2) (0) (2) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_choose, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose.h6 : ¬∀ {p a b : ℕ}, Nat.Prime p → a < p → b - a < p → p ∣ b.choose a := fun hc_h => absurd (@hc_h (2) (0) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Equiv.ofRightInverseOfCardLE_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofRightInverseOfCardLE_apply.h4 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] (f : α → β) (g : β → α),
        Function.RightInverse g f → ∀ (a : α), Fintype.card α ≤ Fintype.card β := fun hc_h => absurd (@hc_h (Bool) (Unit) (Bool.fintype) (PUnit.fintype) (fun (a : Bool) => PUnit.unit) (fun (a : Unit) => Bool.false) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- Equiv.ofRightInverseOfCardLE_apply, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofRightInverseOfCardLE_apply.h7 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β],
        Fintype.card α ≤ Fintype.card β → ∀ (f : α → β) (g : β → α) (a : α), Function.RightInverse g f := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype) (by
  decide) (not : Bool → Bool) (fun _ => true : Bool → Bool) (Bool.false)) (by
  decide +kernel)

-- Equiv.ofRightInverseOfCardLE_symm_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofRightInverseOfCardLE_symm_apply.h4 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] (f : α → β) (g : β → α),
        Function.RightInverse g f → ∀ (a : β), Fintype.card α ≤ Fintype.card β := fun hc_h => absurd (@hc_h (Bool) (Unit) (Bool.fintype) (PUnit.fintype) (fun (a : Bool) => PUnit.unit) (fun (a : Unit) => Bool.false) (by
  decide) (PUnit.unit)) (by
  decide +kernel)

-- Equiv.ofRightInverseOfCardLE_symm_apply, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofRightInverseOfCardLE_symm_apply.h7 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β],
        Fintype.card α ≤ Fintype.card β → ∀ (f : α → β) (g : β → α) (a : β), Function.RightInverse g f := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype) (by
  decide) (not : Bool → Bool) (fun _ => true : Bool → Bool) (Bool.false)) (by
  decide +kernel)

-- Nat.chineseRemainder'_lt_lcm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.chineseRemainder'_lt_lcm.h4 : ¬∀ {m n a b : ℕ}, n ≠ 0 → m ≠ 0 → a ≡ b [MOD n.gcd m] := fun hc_h => absurd (@hc_h (2) (2) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.chineseRemainder'_lt_lcm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.chineseRemainder'_lt_lcm.h5 : ¬∀ {m n a b : ℕ} (h : a ≡ b [MOD n.gcd m]), m ≠ 0 → ↑(Nat.chineseRemainder' h) < n.lcm m := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (1) (0) (0) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- Nat.chineseRemainder'_lt_lcm, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.chineseRemainder'_lt_lcm.h6 : ¬∀ {m n a b : ℕ} (h : a ≡ b [MOD n.gcd m]), n ≠ 0 → ↑(Nat.chineseRemainder' h) < n.lcm m := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (0) (1) (0) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- Set.Finite.exists_injOn_of_encard_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.exists_injOn_of_encard_le.h6 : ¬∀ {α β : Type} [inst : Nonempty β] {s : Set α} {t : Set β}, s.Finite → ∃ (f : α → β), s ⊆ f ⁻¹' t ∧ Set.InjOn f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _ ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Set.le_ncard_of_inj_on_range, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.le_ncard_of_inj_on_range.h4.inst : ¬2 ≤ {n : ℕ | n = 0}.ncard := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.le_ncard_of_inj_on_range.h4.prem0 : ∀ i < 2, ∀ j < 2, (fun (n : ℕ) => n + 1) i = (fun (n : ℕ) => n + 1) j → i = j := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.le_ncard_of_inj_on_range.h4.prem1 : autoParam {n : ℕ | n = 0}.Finite Set.le_ncard_of_inj_on_range._auto_1 := by
  simp
theorem HypCheckProof.Set.le_ncard_of_inj_on_range.h4 : ¬∀ {α : Type} {s : Set α} {n : ℕ} (f : ℕ → α),
        (∀ i < n, ∀ j < n, f i = f j → i = j) → autoParam s.Finite Set.le_ncard_of_inj_on_range._auto_1 → n ≤ s.ncard := fun hc_h => HypCheckProof.Set.le_ncard_of_inj_on_range.h4.inst (@hc_h (ℕ) ({n : ℕ | n = 0}) (2) (fun (n : ℕ) => n + 1) HypCheckProof.Set.le_ncard_of_inj_on_range.h4.prem0 HypCheckProof.Set.le_ncard_of_inj_on_range.h4.prem1)

-- Set.le_ncard_of_inj_on_range, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.le_ncard_of_inj_on_range.h5.inst : ¬2 ≤ {n : ℕ | n = 0}.ncard := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.le_ncard_of_inj_on_range.h5.prem0 : ∀ i < 2, (fun (x : ℕ) => 0) i ∈ {n : ℕ | n = 0} := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.le_ncard_of_inj_on_range.h5.prem1 : autoParam {n : ℕ | n = 0}.Finite Set.le_ncard_of_inj_on_range._auto_1 := by
  simp
theorem HypCheckProof.Set.le_ncard_of_inj_on_range.h5 : ¬∀ {α : Type} {s : Set α} {n : ℕ} (f : ℕ → α),
        (∀ i < n, f i ∈ s) → autoParam s.Finite Set.le_ncard_of_inj_on_range._auto_1 → n ≤ s.ncard := fun hc_h => HypCheckProof.Set.le_ncard_of_inj_on_range.h5.inst (@hc_h (ℕ) ({n : ℕ | n = 0}) (2) (fun (x : ℕ) => 0) HypCheckProof.Set.le_ncard_of_inj_on_range.h5.prem0 HypCheckProof.Set.le_ncard_of_inj_on_range.h5.prem1)

-- Set.le_ncard_of_inj_on_range, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.le_ncard_of_inj_on_range.h6.inst : ¬1 ≤ {x : ℕ | True}.ncard := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.le_ncard_of_inj_on_range.h6.prem0 : ∀ i < 1, (fun (n : ℕ) => n + 1) i ∈ {x : ℕ | True} := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.le_ncard_of_inj_on_range.h6.prem1 : ∀ i < 1, ∀ j < 1, (fun (n : ℕ) => n + 1) i = (fun (n : ℕ) => n + 1) j → i = j := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.le_ncard_of_inj_on_range.h6 : ¬∀ {α : Type} {s : Set α} {n : ℕ} (f : ℕ → α), (∀ i < n, f i ∈ s) → (∀ i < n, ∀ j < n, f i = f j → i = j) → n ≤ s.ncard := fun hc_h => HypCheckProof.Set.le_ncard_of_inj_on_range.h6.inst (@hc_h (ℕ) ({x : ℕ | True}) (1) (fun (n : ℕ) => n + 1) HypCheckProof.Set.le_ncard_of_inj_on_range.h6.prem0 HypCheckProof.Set.le_ncard_of_inj_on_range.h6.prem1)

-- List.mem_ext, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_ext.h6 : ¬∀ {α : Type} {β : α → Type} {l₀ l₁ : List (Sigma β)}, l₀.Nodup → l₁.Nodup → l₀.Perm l₁ := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ([]) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.count_eq_one_of_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.count_eq_one_of_mem.h2 : ¬∀ {α : Type} [inst : BEq α] {a : α} {l : List α}, l.Nodup → a ∈ l → List.count a l = 1 := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) (0) ([0, 1]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.count_eq_one_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.count_eq_one_of_mem.h6 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {a : α} {l : List α}, l.Nodup → List.count a l = 1 := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ (0) ([]) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.rel_getLast_of_rel_getLast_getLast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_getLast_of_rel_getLast_getLast.h4 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α} (ha : a ∈ l),
        R (l.getLast (List.ne_nil_of_mem ha)) (l.getLast (List.ne_nil_of_mem ha)) → R a (l.getLast (List.ne_nil_of_mem ha)) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) ([0, 1]) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- List.Pairwise.rel_getLast_of_rel_getLast_getLast, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_getLast_of_rel_getLast_getLast.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α}, List.Pairwise R l → a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (0) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.rel_getLast_of_rel_getLast_getLast, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_getLast_of_rel_getLast_getLast.h6 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α},
        List.Pairwise R l → ∀ (ha : a ∈ l), R a (l.getLast (List.ne_nil_of_mem ha)) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- Set.Pairwise.insert_of_notMem, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Set.Pairwise.insert_of_notMem.h4.gneg.{u_1} : ∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a : α},
      ¬a ∉ s → s.Pairwise r → (∀ b ∈ s, r a b ∧ r b a) → (Insert.insert a s).Pairwise r := by
  (intros; simp_all; done)
theorem HypCheckProof.Set.Pairwise.insert_of_notMem.h4.{u_1} : ∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a : α},
      s.Pairwise r → (∀ b ∈ s, r a b ∧ r b a) → (Insert.insert a s).Pairwise r := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x5 hc_x6
  exact Classical.byCases (fun hc_h => @Set.Pairwise.insert_of_notMem hc_x0 hc_x1 hc_x2 hc_x3 hc_h hc_x5 hc_x6) (fun hc_hn => @HypCheckProof.Set.Pairwise.insert_of_notMem.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn hc_x5 hc_x6)

-- List.Perm.eq_of_sortedGE, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.eq_of_sortedGE.h6 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁.SortedGE → l₂.SortedGE → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.log_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_mono.h4 : ¬∀ {b c m n : ℕ}, c ≤ b → m ≤ n → Nat.log b m ≤ Nat.log c n := fun hc_h => absurd (@hc_h (2) (0) (2) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.log_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_mono.h5 : ¬∀ {b c m n : ℕ}, 1 < c → m ≤ n → Nat.log b m ≤ Nat.log c n := fun hc_h => absurd (@hc_h (2) (3) (2) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.log_mono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_mono.h6 : ¬∀ {b c m n : ℕ}, 1 < c → c ≤ b → Nat.log b m ≤ Nat.log c n := fun hc_h => absurd (@hc_h (2) (2) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.clog_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_mono.h4 : ¬∀ {b c m n : ℕ}, c ≤ b → m ≤ n → Nat.clog b m ≤ Nat.clog c n := fun hc_h => absurd (@hc_h (2) (0) (2) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.clog_mono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_mono.h6 : ¬∀ {b c m n : ℕ}, 1 < c → c ≤ b → Nat.clog b m ≤ Nat.clog c n := fun hc_h => absurd (@hc_h (2) (2) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- ENat.add_lt_add_of_lt_of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.add_lt_add_of_lt_of_le.h5 : ¬∀ {a b c d : ℕ∞}, c ≠ ⊤ → c ≤ d → a + c < b + d := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- ENat.add_lt_add_of_lt_of_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.add_lt_add_of_lt_of_le.h6 : ¬∀ {a b c d : ℕ∞}, c ≠ ⊤ → a < b → a + c < b + d := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Choose.choose_modEq_prod_range_choose, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.choose_modEq_prod_range_choose.h6 : ¬∀ {n k p : ℕ} [inst : Fact (Nat.Prime p)] {a : ℕ},
        n < p ^ a → ↑(n.choose k) ≡ ∏ i ∈ Finset.range a, ↑((n / p ^ i % p).choose (k / p ^ i % p)) [ZMOD ↑p] := fun hc_h => absurd (@hc_h (0) (1) (2) _ (0) (by
  decide)) (by
  decide +kernel)

-- IsUnit.natCast_factorial_of_isNilpotent, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsUnit.natCast_factorial_of_isNilpotent.h4 : Not
      (∀ {A : Type} [inst : CommRing A] {n p : Nat} [inst_1 : Fact (Nat.Prime p)],
        @LT.lt Nat instLTNat n p →
          @IsUnit A (@Semiring.toMonoid A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
            (@Nat.cast A
              (@AddMonoidWithOne.toNatCast A
                (@AddGroupWithOne.toAddMonoidWithOne A (@Ring.toAddGroupWithOne A (@CommRing.toRing A inst))))
              n.factorial)) := fun hc_h => absurd (@hc_h (Bool) (@BooleanRing.toCommRing Bool instBooleanRingBool) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) _ (by
  decide)) (by
  decide +kernel)

-- List.perm_of_nodup_nodup_toFinset_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.perm_of_nodup_nodup_toFinset_eq.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l l' : List α}, l'.Nodup → l.toFinset = l'.toFinset → l.Perm l' := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0, 0]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.perm_of_nodup_nodup_toFinset_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.perm_of_nodup_nodup_toFinset_eq.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {l l' : List α}, l.Nodup → l.toFinset = l'.toFinset → l.Perm l' := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([0, 0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.perm_of_nodup_nodup_toFinset_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.perm_of_nodup_nodup_toFinset_eq.h6 : ¬∀ {α : Type} [inst : DecidableEq α] {l l' : List α}, l.Nodup → l'.Nodup → l.Perm l' := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Perm.eq_of_sortedLE, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.eq_of_sortedLE.h6 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁.SortedLE → l₂.SortedLE → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Perm.eq_reverse_of_sortedLE_of_sortedGE, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.eq_reverse_of_sortedLE_of_sortedGE.h4 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁.SortedLE → l₂.SortedGE → l₁ = l₂.reverse := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.sublist_of_subperm_of_sortedLE, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sublist_of_subperm_of_sortedLE.h4 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁.SortedLE → l₂.SortedLE → l₁.Sublist l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0]) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.chineseRemainder_lt_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.chineseRemainder_lt_mul.h2 : ¬∀ {m n : ℕ} (a b : ℕ), n ≠ 0 → m ≠ 0 → n.Coprime m := fun hc_h => absurd (@hc_h (2) (2) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.chineseRemainder_lt_mul, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.chineseRemainder_lt_mul.h5 : ¬∀ {m n : ℕ} (co : n.Coprime m) (a b : ℕ), m ≠ 0 → ↑(Nat.chineseRemainder co a b) < n * m := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (1) (0) hc_k0 (0) (0) hc_k1) (by
  decide +kernel)

-- Nat.chineseRemainder_lt_mul, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.chineseRemainder_lt_mul.h6 : ¬∀ {m n : ℕ} (co : n.Coprime m) (a b : ℕ), n ≠ 0 → ↑(Nat.chineseRemainder co a b) < n * m := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (0) (1) hc_k0 (0) (0) hc_k1) (by
  decide +kernel)

-- Ordnode.Valid'.node4L_lemma₅, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.node4L_lemma₅.h6 : ¬∀ {a b c d : ℕ}, 3 * (b + c + 1 + d) ≤ 16 * a + 9 → 2 * d ≤ b + c + 1 → c + d + 1 ≤ 3 * (a + b + 1) := fun hc_h => absurd (@hc_h (1) (0) (4) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Valid'.node4L_lemma₁, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.node4L_lemma₁.h4 : ¬∀ {a b c d : ℕ}, b + c + 1 ≤ 3 * d → b ≤ 3 * c → b < 3 * a + 1 := fun hc_h => absurd (@hc_h (0) (1) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Valid'.node4L_lemma₁, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.node4L_lemma₁.h5 : ¬∀ {a b c d : ℕ}, 3 * (b + c + 1 + d) ≤ 16 * a + 9 → b ≤ 3 * c → b < 3 * a + 1 := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Valid'.node4L_lemma₁, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.node4L_lemma₁.h6 : ¬∀ {a b c d : ℕ}, 3 * (b + c + 1 + d) ≤ 16 * a + 9 → b + c + 1 ≤ 3 * d → b < 3 * a + 1 := fun hc_h => absurd (@hc_h (0) (1) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.emultiplicity_choose, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.emultiplicity_choose.h4 : ¬∀ {p n k b : ℕ},
        k ≤ n →
          Nat.log p n < b → emultiplicity p (n.choose k) = ↑{i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}.card := fun hc_h => absurd (@hc_h (1) (0) (0) (1) (by
  decide) (by
  decide)) (by
  norm_num)

-- Set.Finite.toFinset_sdiff, hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Set.Finite.toFinset_sdiff.h6.der.{u} : ∀ {α : Type u} {s t : Set α} [inst : DecidableEq α], s.Finite → t.Finite → (s \ t).Finite := by
  (intros; simp_all; done)
theorem HypCheckProof.Set.Finite.toFinset_sdiff.h6.{u} : ∀ {α : Type u} {s t : Set α} [inst : DecidableEq α] (hs : s.Finite) (ht : t.Finite),
      (HypCheckProof.Set.Finite.toFinset_sdiff.h6.der hs ht).toFinset = hs.toFinset \ ht.toFinset := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Set.Finite.toFinset_sdiff hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Set.Finite.toFinset_sdiff.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Nat.ModEq.sub_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.sub_left.h4 : ¬∀ {n a b c : ℕ}, c ≤ a → b ≡ c [MOD n] → a - b ≡ a - c [MOD n] := fun hc_h => absurd (@hc_h (2) (1) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.sub_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.sub_left.h5 : ¬∀ {n a b c : ℕ}, b ≤ a → b ≡ c [MOD n] → a - b ≡ a - c [MOD n] := fun hc_h => absurd (@hc_h (2) (1) (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.sub_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.sub_left.h6 : ¬∀ {n a b c : ℕ}, b ≤ a → c ≤ a → a - b ≡ a - c [MOD n] := fun hc_h => absurd (@hc_h (0) (1) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.InjOn.injective_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.injective_iff.h7 : ¬∀ {α β γ : Type} {f : α → β} {g : β → γ} (s : Set β),
        Set.InjOn g s → (Function.Injective (g ∘ f) ↔ Function.Injective f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0}) (by
  simp)) (by
  decide +kernel)

-- Set.EqOn.trans, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.trans.h6 : ¬∀ {α β : Type} {s : Set α} {f₁ f₂ f₃ : α → β}, Set.EqOn f₂ f₃ s → Set.EqOn f₁ f₃ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.EqOn.trans, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.trans.h7 : ¬∀ {α β : Type} {s : Set α} {f₁ f₂ f₃ : α → β}, Set.EqOn f₁ f₂ s → Set.EqOn f₁ f₃ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.LeftInvOn.eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.LeftInvOn.eq.h5 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {f' : β → α} {x : α}, x ∈ s → f' (f x) = x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- List.isChain_map_of_isChain, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isChain_map_of_isChain.h5 : ¬∀ {α β : Type} {R : α → α → Prop} {S : β → β → Prop} (f : α → β) {l : List α},
        List.IsChain R l → List.IsChain S (List.map f l) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (fun _ => 0 : ℕ → ℕ) ([0, 1]) (by
  decide)) (by
  decide +kernel)

-- List.isChain_map_of_isChain, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isChain_map_of_isChain.h7 : ¬∀ {α β : Type} {R : α → α → Prop} {S : β → β → Prop} (f : α → β),
        (∀ (a b : α), R a b → S (f a) (f b)) → ∀ {l : List α}, List.IsChain S (List.map f l) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ) (by
  simp) ([1, 0])) (by
  decide +kernel)

-- Set.image2_right_comm, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_right_comm.h13 : ¬∀ {α β γ δ δ' ε : Type} {s : Set α} {t : Set β} {u : Set γ} {f : δ → γ → ε} {g : α → β → δ} {f' : α → γ → δ'}
        {g' : δ' → β → ε}, Set.image2 f (Set.image2 g s t) u = Set.image2 g' (Set.image2 f' s u) t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (Bool) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun a b => a - b : ℕ → ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun a b => a < b : ℕ → ℕ → Bool) (fun (a : Bool) (n : ℕ) => n + 1)) (by
  (simp <;> omega))

-- Set.image_image2_distrib, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_image2_distrib.h13 : ¬∀ {α α' β β' γ δ : Type} {f : α → β → γ} {s : Set α} {t : Set β} {g : γ → δ} {f' : α' → β' → δ} {g₁ : α → α'}
        {g₂ : β → β'}, g '' Set.image2 f s t = Set.image2 f' (g₁ '' s) (g₂ '' t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun a b => a + b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.Nonempty.image2, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.image2.h6 : ¬∀ {α β γ : Type} {f : α → β → γ} {s : Set α} {t : Set β}, t.Nonempty → (Set.image2 f s t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.Nonempty.image2, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.image2.h7 : ¬∀ {α β γ : Type} {f : α → β → γ} {s : Set α} {t : Set β}, s.Nonempty → (Set.image2 f s t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- List.isChain_of_isChain_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isChain_of_isChain_map.h5 : ¬∀ {α β : Type} {R : α → α → Prop} {S : β → β → Prop} (f : α → β) {l : List α},
        List.IsChain S (List.map f l) → List.IsChain R l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ) ([0, 1]) (by
  decide)) (by
  decide +kernel)

-- List.isChain_of_isChain_map, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isChain_of_isChain_map.h7 : ¬∀ {α β : Type} {R : α → α → Prop} {S : β → β → Prop} (f : α → β),
        (∀ (a b : α), S (f a) (f b) → R a b) → ∀ {l : List α}, List.IsChain R l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ) (by
  simp) ([1, 0])) (by
  decide +kernel)

-- Set.image_image2_antidistrib, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_image2_antidistrib.h13 : ¬∀ {α α' β β' γ δ : Type} {f : α → β → γ} {s : Set α} {t : Set β} {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'}
        {g₂ : α → α'}, g '' Set.image2 f s t = Set.image2 f' (g₁ '' t) (g₂ '' s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun a b => a + b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.LeftInvOn.mapsTo, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.LeftInvOn.mapsTo.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} {f' : β → α}, Set.SurjOn f s t → Set.MapsTo f' t s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Fintype.card_lt_of_injective_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_lt_of_injective_of_notMem.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] (f : α → β) {b : β},
        b ∉ Set.range f → Fintype.card α < Fintype.card β := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype) (fun _ => true : Bool → Bool) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Fintype.card_lt_of_injective_of_notMem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_lt_of_injective_of_notMem.h7 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] (f : α → β),
        Function.Injective f → ∀ {b : β}, Fintype.card α < Fintype.card β := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype) (not : Bool → Bool) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- Fintype.existsUnique_notMem_image_of_injective_of_card_eq_add_one, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.existsUnique_notMem_image_of_injective_of_card_eq_add_one.h7 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : DecidableEq β] (f : α → β),
        Function.Injective f → ∃! x : β, x ∉ Finset.image f Finset.univ := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype) (instDecidableEqBool) (not : Bool → Bool) (by
  decide)) (by
  simp)

-- List.cons_sublist_orderedInsert, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.cons_sublist_orderedInsert.h6.inst : ¬[0, 1].Sublist (List.orderedInsert (fun (a b : ℕ) => a < b) 0 []) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.cons_sublist_orderedInsert.h6.prem0 : ∀ a' ∈ [1], (fun (a b : ℕ) => a < b) 0 a' := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.cons_sublist_orderedInsert.h6 : ¬∀ {α : Type} {r : α → α → Prop} [inst : DecidableRel r] {l c : List α} {a : α},
        (∀ a' ∈ c, r a a') → (a :: c).Sublist (List.orderedInsert r a l) := fun hc_h => HypCheckProof.List.cons_sublist_orderedInsert.h6.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (Nat.decLt) ([]) ([1]) (0) HypCheckProof.List.cons_sublist_orderedInsert.h6.prem0)

-- List.cons_sublist_orderedInsert, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_sublist_orderedInsert.h7 : ¬∀ {α : Type} {r : α → α → Prop} [inst : DecidableRel r] {l c : List α} {a : α},
        c.Sublist l → (a :: c).Sublist (List.orderedInsert r a l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) ([0]) ([0]) (1) (by
  decide)) (by
  decide +kernel)

-- Set.BijOn.symm, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.symm.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} {g : β → α}, Set.BijOn f s t → Set.BijOn g t s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.BijOn.congr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.congr.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f₁ f₂ : α → β}, Set.EqOn f₁ f₂ s → Set.BijOn f₂ s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.BijOn.congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.congr.h7 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f₁ f₂ : α → β}, Set.BijOn f₁ s t → Set.BijOn f₂ s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Function.LeftInverse.rightInverse_of_card_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.rightInverse_of_card_le.h6 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] {f : α → β} {g : β → α},
        Fintype.card α ≤ Fintype.card β → Function.RightInverse f g := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype) (not : Bool → Bool) (fun _ => true : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Function.LeftInverse.rightInverse_of_card_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.rightInverse_of_card_le.h7 : ¬∀ {α β : Type} [inst : Fintype α] [inst : Fintype β] {f : α → β} {g : β → α},
        Function.LeftInverse f g → Function.RightInverse f g := fun hc_h => absurd (@hc_h (Bool) (Unit) (Bool.fintype) (PUnit.fintype) (fun (a : Bool) => PUnit.unit) (fun (a : Unit) => Bool.false) (by
  decide)) (by
  decide +kernel)

-- Set.prod_mono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.prod_mono.h6 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {t₁ t₂ : Set β}, t₁ ⊆ t₂ → s₁ ×ˢ t₁ ⊆ s₂ ×ˢ t₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Set.prod_mono, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.prod_mono.h7 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {t₁ t₂ : Set β}, s₁ ⊆ s₂ → s₁ ×ˢ t₁ ⊆ s₂ ×ˢ t₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  rfl)) (by
  simp)

-- List.next_cons_cons_eq', hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.next_cons_cons_eq'.h6.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y z : α), x = y → x ∈ y :: z :: l := by
  (intros; simp_all; done)
theorem HypCheckProof.List.next_cons_cons_eq'.h6.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y z : α) (hx : x = y),
      (y :: z :: l).next x (HypCheckProof.List.next_cons_cons_eq'.h6.der l x y z hx) = z := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @List.next_cons_cons_eq' hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.List.next_cons_cons_eq'.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6) hc_x6

-- List.next_cons_cons_eq', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_cons_cons_eq'.h7 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (x y z : α) (h : x ∈ y :: z :: l), (y :: z :: l).next x h = z := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (instDecidableEqNat) ([]) (0) (1) (0) hc_k0) (by
  decide +kernel)

-- Nat.findGreatest_mono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.findGreatest_mono.h6 : ¬∀ {m : ℕ} {P Q : ℕ → Prop} [inst : DecidablePred P] {n : ℕ} [inst_1 : DecidablePred Q],
        m ≤ n → Nat.findGreatest P m ≤ Nat.findGreatest Q n := fun hc_h => absurd (@hc_h (1) (fun _ => True : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableTrue) (1) (fun (a : ℕ) => instDecidableEqNat a 0) (by
  decide)) (by
  decide +kernel)

-- Nat.findGreatest_mono, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.findGreatest_mono.h7 : ¬∀ {m : ℕ} {P Q : ℕ → Prop} [inst : DecidablePred P] {n : ℕ} [inst_1 : DecidablePred Q],
        (∀ (n : ℕ), P n → Q n) → Nat.findGreatest P m ≤ Nat.findGreatest Q n := fun hc_h => absurd (@hc_h (2) (fun n => n % 2 = 0 : ℕ → Prop) (fun n => n % 2 = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat (a % 2) 0) (0) (fun (a : ℕ) => instDecidableEqNat (a % 2) 0) (by
  simp)) (by
  decide +kernel)

-- Function.monotone_of_rightInverse, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.monotone_of_rightInverse.h6 : ¬∀ {α β : Type} [inst : PartialOrder α] [inst_1 : LinearOrder β] {φ : β → α} {ψ : α → β},
        Function.RightInverse ψ φ → Monotone ψ := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.instPartialOrder) (Bool.linearOrder) (not : Bool → Bool) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Function.monotone_of_rightInverse, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.monotone_of_rightInverse.h7 : ¬∀ {α β : Type} [inst : PartialOrder α] [inst_1 : LinearOrder β] {φ : β → α} {ψ : α → β}, Monotone φ → Monotone ψ := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.instPartialOrder) (Bool.linearOrder) (fun _ => true : Bool → Bool) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Int.clog_of_left_le_one, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.clog_of_left_le_one.h6 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ} (r : R), Int.clog b r = 0 := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (2) (1 / 2)) (by
  decide +kernel)

-- Set.mem_biUnion, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.mem_biUnion.h6.inst : 0 ∉ ⋃ x ∈ {x : ℕ | False}, (fun (a : ℕ) => {n : ℕ | n = 0}) x := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.mem_biUnion.h6.prem0 : 0 ∈ (fun (a : ℕ) => {n : ℕ | n = 0}) 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.mem_biUnion.h6 : ¬∀ {α β : Type} {s : Set α} {t : α → Set β} {x : α} {y : β}, y ∈ t x → y ∈ ⋃ x ∈ s, t x := fun hc_h => HypCheckProof.Set.mem_biUnion.h6.inst (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) (fun (a : ℕ) => {n : ℕ | n = 0}) (0) (0) HypCheckProof.Set.mem_biUnion.h6.prem0)

-- Set.mem_biUnion, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_biUnion.h7 : ¬∀ {α β : Type} {s : Set α} {t : α → Set β} {x : α} {y : β}, x ∈ s → y ∈ ⋃ x ∈ s, t x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) (0) (1) (by
  decide)) (by
  simp)

-- Set.biUnion_mono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.biUnion_mono.h6 : ¬∀ {α β : Type} {s s' : Set α} {t t' : α → Set β}, (∀ x ∈ s, t x ⊆ t' x) → ⋃ x ∈ s', t x ⊆ ⋃ x ∈ s, t' x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.biUnion_mono, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.biUnion_mono.h7 : ¬∀ {α β : Type} {s s' : Set α} {t t' : α → Set β}, s' ⊆ s → ⋃ x ∈ s', t x ⊆ ⋃ x ∈ s, t' x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun (a : ℕ) => {x : ℕ | False}) (by
  rfl)) (by
  simp)

-- List.Perm.foldr_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.foldr_eq.h6 : ¬∀ {α β : Type} {f : α → β → β} {l₁ l₂ : List α} [lcomm : LeftCommutative f] (b : β),
        List.foldr f b l₁ = List.foldr f b l₂ := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun (a : ℕ) => Bool.not) ([]) ([0]) (@LeftCommutative.mk (Nat) (Bool) (fun (a : Nat) => Bool.not) (by (try dsimp only);   (intros; simp_all; done))) (Bool.false)) (by
  decide +kernel)

-- List.not_maximum_lt_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_maximum_lt_of_mem.h6 : ¬∀ {α : Type} [inst : Preorder α] [inst_1 : DecidableLT α] {l : List α} {a m : α}, l.maximum = ↑m → ¬m < a := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Nat.decLt) ([0]) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.not_maximum_lt_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_maximum_lt_of_mem.h7 : ¬∀ {α : Type} [inst : Preorder α] [inst_1 : DecidableLT α] {l : List α} {a m : α}, a ∈ l → ¬m < a := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Nat.decLt) ([1]) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Set.MapsTo.mono_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.mono_right.h6 : ¬∀ {α β : Type} {s : Set α} {t₁ t₂ : Set β} {f : α → β}, t₁ ⊆ t₂ → Set.MapsTo f s t₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  rfl)) (by
  simp)

-- Set.MapsTo.mono_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.mono_right.h7 : ¬∀ {α β : Type} {s : Set α} {t₁ t₂ : Set β} {f : α → β}, Set.MapsTo f s t₁ → Set.MapsTo f s t₂ := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (fun n => n % 2 == 0 : ℕ → Bool) (by
  simp)) (by
  simp)

-- List.forall_mem_inter_of_forall_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forall_mem_inter_of_forall_left.h4 : ¬∀ {α : Type} {l₁ : List α} {p : α → Prop} [inst : DecidableEq α] (l₂ : List α), ∀ x ∈ l₁ ∩ l₂, p x := fun hc_h => absurd (@hc_h (Bool) ([Bool.false]) (fun b => b = true : Bool → Prop) (instDecidableEqBool) ([Bool.false]) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- List.forall_mem_inter_of_forall_left, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.forall_mem_inter_of_forall_left.h7.inst : ¬(fun (n : ℕ) => n = 0) 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.forall_mem_inter_of_forall_left.h7.prem0 : ∀ x ∈ [], (fun (n : ℕ) => n = 0) x := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.forall_mem_inter_of_forall_left.h7 : ¬∀ {α : Type} {l₁ : List α} {p : α → Prop} [inst : DecidableEq α], (∀ x ∈ l₁, p x) → ∀ (l₂ : List α) (x : α), p x := fun hc_h => HypCheckProof.List.forall_mem_inter_of_forall_left.h7.inst (@hc_h (ℕ) ([]) (fun (n : ℕ) => n = 0) (instDecidableEqNat) HypCheckProof.List.forall_mem_inter_of_forall_left.h7.prem0 ([]) (1))

-- Int.lt_zpow_succ_log_self, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.lt_zpow_succ_log_self.h6 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ} (r : R), r < ↑b ^ (Int.log b r + 1) := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (0) (0)) (by
  decide +kernel)

-- List.Perm.dropSlice_inter, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.dropSlice_inter.h6 : ¬∀ {α : Type} [inst : DecidableEq α] {xs ys : List α} (n m : ℕ),
        ys.Nodup → (List.dropSlice n m xs).Perm (ys ∩ List.dropSlice n m xs) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Int.clog_zpow, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.clog_zpow.h6 : Not
      (∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R]
        [inst_2 :
          @FloorSemiring R (@CommSemiring.toSemiring R (@Semifield.toCommSemiring R inst))
            (@SemilatticeInf.toPartialOrder R
              (@Lattice.toSemilatticeInf R (@DistribLattice.toLattice R (@instDistribLatticeOfLinearOrder R inst_1))))]
        [inst_3 :
          @IsStrictOrderedRing R (@CommSemiring.toSemiring R (@Semifield.toCommSemiring R inst))
            (@SemilatticeInf.toPartialOrder R
              (@Lattice.toSemilatticeInf R (@DistribLattice.toLattice R (@instDistribLatticeOfLinearOrder R inst_1))))]
        {b : Nat} (z : Int),
        @Eq Int
          (@Int.clog R inst inst_1 inst_2 b
            (@HPow.hPow R Int R
              (@instHPow R Int
                (@ZPow.toPow R
                  (@DivInvMonoid.toZPow R
                    (@GroupWithZero.toDivInvMonoid R
                      (@DivisionSemiring.toGroupWithZero R (@Semifield.toDivisionSemiring R inst))))))
              (@Nat.cast R
                (@AddMonoidWithOne.toNatCast R
                  (@AddCommMonoidWithOne.toAddMonoidWithOne R
                    (@NonAssocSemiring.toAddCommMonoidWithOne R
                      (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@Semifield.toCommSemiring R inst))))))
                b)
              z))
          z) := fun hc_h => absurd (@hc_h (Rat) (@Field.toSemifield Rat Rat.instField) (Rat.linearOrder) (@FloorRing.toFloorSemiring Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  decide +kernel)

-- Function.Injective.sumMap, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.sumMap.h6 : ¬∀ {α α' β β' : Type} {f : α → β} {g : α' → β'}, Function.Injective g → Function.Injective (Sum.map f g) := fun hc_h => absurd (@hc_h (ℕ) (Bool) (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  simp)

-- Function.Injective.sumMap, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.sumMap.h7 : ¬∀ {α α' β β' : Type} {f : α → β} {g : α' → β'}, Function.Injective f → Function.Injective (Sum.map f g) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  decide)) (by
  simp)

-- Set.infs_subset, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infs_subset.h6 : Not
      (∀ {α : Type} [inst : SemilatticeInf α] {s₁ s₂ t₁ t₂ : Set α},
        @LE.le (Set α) (@Set.instLE α) t₁ t₂ →
          @LE.le (Set α) (@Set.instLE α) (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s₁ t₁)
            (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s₂ t₂)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (x : Nat) => False) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  rfl)) (by
  simp)

-- Set.infs_subset, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infs_subset.h7 : Not
      (∀ {α : Type} [inst : SemilatticeInf α] {s₁ s₂ t₁ t₂ : Set α},
        @LE.le (Set α) (@Set.instLE α) s₁ s₂ →
          @LE.le (Set α) (@Set.instLE α) (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s₁ t₁)
            (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s₂ t₂)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (x : Nat) => False) (by
  rfl)) (by
  simp)

-- List.mem_dlookup, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_dlookup.h7 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {b : β a} {l : List (Sigma β)},
        l.NodupKeys → b ∈ List.dlookup a l := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) (0) ([]) (by
  simp)) (by
  decide +kernel)

-- Finsupp.mapRange_injective, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.mapRange_injective.h6 : ¬∀ {α : Type} {M N : Type} [inst : Zero M] [inst_1 : Zero N] (e : M → N), Function.Injective e → e 0 = 0 := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Bool) (instZeroBool_mathlib) (instZeroBool_mathlib) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Finsupp.mapRange_bijective, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.mapRange_bijective.h6 : ¬∀ {α : Type} {M N : Type} [inst : Zero M] [inst_1 : Zero N] (e : M → N), Function.Bijective e → e 0 = 0 := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Bool) (instZeroBool_mathlib) (instZeroBool_mathlib) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Part.mod_mem_mod, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.mod_mem_mod.h6 : ¬∀ {α : Type} [inst : Mod α] (a b : Part α) (ma mb : α), mb ∈ b → ma % mb ∈ a % b := fun hc_h => absurd (@hc_h (ℕ) (Nat.instMod) (0) (0) (1) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.mod_mem_mod, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.mod_mem_mod.h7 : ¬∀ {α : Type} [inst : Mod α] (a b : Part α) (ma mb : α), ma ∈ a → ma % mb ∈ a % b := fun hc_h => absurd (@hc_h (ℕ) (Nat.instMod) (0) (⊥) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Option.map_map₂_antidistrib, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.map_map₂_antidistrib.h13 : ¬∀ {α β γ δ : Type} {f : α → β → γ} {a : Option α} {b : Option β} {α' β' : Type} {g : γ → δ} {f' : β' → α' → δ}
        {g₁ : β → β'} {g₂ : α → α'}, Option.map g (Option.map₂ f a b) = Option.map₂ f' (Option.map g₁ b) (Option.map g₂ a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (Option.some 0) (Option.some 0) (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Option.map_map₂_distrib, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.map_map₂_distrib.h13 : ¬∀ {α β γ δ : Type} {f : α → β → γ} {a : Option α} {b : Option β} {α' β' : Type} {g : γ → δ} {f' : α' → β' → δ}
        {g₁ : α → α'} {g₂ : β → β'}, Option.map g (Option.map₂ f a b) = Option.map₂ f' (Option.map g₁ a) (Option.map g₂ b) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (Option.some 0) (Option.some 0) (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Function.Injective.prodMap, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.prodMap.h6 : ¬∀ {α β γ δ : Type} {f : α → γ} {g : β → δ}, Function.Injective g → Function.Injective (Prod.map f g) := fun hc_h => absurd (@hc_h (ℕ) (Bool) (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  simp)

-- Function.Injective.prodMap, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.prodMap.h7 : ¬∀ {α β γ δ : Type} {f : α → γ} {g : β → δ}, Function.Injective f → Function.Injective (Prod.map f g) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  decide)) (by
  simp)

-- List.map_permutationsAux2', hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map_permutationsAux2'.h12 : ¬∀ {α β α' β' : Type} (g : α → α') (g' : β → β') (t : α) (ts ys : List α) (r : List β) (f : List α → β)
        (f' : List α' → β'),
        List.map g' (List.permutationsAux2 t ts r ys f).2 =
          (List.permutationsAux2 (g t) (List.map g ts) (List.map g' r) (List.map g ys) f').2 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (0) ([]) ([0]) ([]) (fun (a : List ℕ) => 0) (fun (a : List ℕ) => 0)) (by
  decide +kernel)

-- Nat.ModEq.add_left_cancel, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.add_left_cancel.h5 : ¬∀ {n a b c d : ℕ}, a + c ≡ b + d [MOD n] → c ≡ d [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.add_left_cancel, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.add_left_cancel.h6 : ¬∀ {n a b c d : ℕ}, a ≡ b [MOD n] → c ≡ d [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Set.exists_max_image, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_max_image.h6 : ¬∀ {α β : Type} [inst : LinearOrder β] (s : Set α) (f : α → β), s.Finite → ∃ a ∈ s, ∀ b ∈ s, f b ≤ f a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Nat.Prime.emultiplicity_choose_prime_pow_add_emultiplicity, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.emultiplicity_choose_prime_pow_add_emultiplicity.h3 : ¬∀ {p n k : ℕ}, k ≤ p ^ n → k ≠ 0 → emultiplicity p ((p ^ n).choose k) + emultiplicity p k = ↑n := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide) (by
  decide)) (by
  simp)

-- Nat.Prime.emultiplicity_choose_prime_pow_add_emultiplicity, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.emultiplicity_choose_prime_pow_add_emultiplicity.h5 : ¬∀ {p n k : ℕ}, Nat.Prime p → k ≤ p ^ n → emultiplicity p ((p ^ n).choose k) + emultiplicity p k = ↑n := fun hc_h => absurd (@hc_h (2) (0) (0) (by
  decide) (by
  decide)) (by
  simp)

-- List.idxOf_inj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_inj.h2 : ¬∀ {α : Type} [inst : BEq α] {l : List α} {x y : α}, x ∈ l → (List.idxOf x l = List.idxOf y l ↔ x = y) := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) ([0]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.idxOf_inj, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_inj.h6 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l : List α} {x y : α}, List.idxOf x l = List.idxOf y l ↔ x = y := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ ([]) (0) (1)) (by
  decide +kernel)

-- List.getLast_congr, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.getLast_congr.h3.der.{u} : ∀ {α : Type u} {l₁ l₂ : List α}, l₂ ≠ [] → l₁ = l₂ → l₁ ≠ [] := by
  (intros; lia)
theorem HypCheckProof.List.getLast_congr.h3.{u} : ∀ {α : Type u} {l₁ l₂ : List α} (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂),
      l₁.getLast (HypCheckProof.List.getLast_congr.h3.der h₂ h₃) = l₂.getLast h₂ := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @List.getLast_congr hc_x0 hc_x1 hc_x2 (@HypCheckProof.List.getLast_congr.h3.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4) hc_x3 hc_x4

-- List.getLast_congr, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.getLast_congr.h4.der.{u} : ∀ {α : Type u} {l₁ l₂ : List α}, l₁ ≠ [] → l₁ = l₂ → l₂ ≠ [] := by
  (intros; lia)
theorem HypCheckProof.List.getLast_congr.h4.{u} : ∀ {α : Type u} {l₁ l₂ : List α} (h₁ : l₁ ≠ []) (h₃ : l₁ = l₂),
      l₁.getLast h₁ = l₂.getLast (HypCheckProof.List.getLast_congr.h4.der h₁ h₃) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @List.getLast_congr hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.List.getLast_congr.h4.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4) hc_x4

-- List.getLast_congr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getLast_congr.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []), l₁.getLast h₁ = l₂.getLast h₂ := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) ([0]) ([1]) hc_k0 hc_k1) (by
  decide +kernel)

-- List.foldl_hom₂, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldl_hom₂.h11 : ¬∀ {ι α β γ : Type} (l : List ι) (f : α → β → γ) (op₁ : α → ι → α) (op₂ : β → ι → β) (op₃ : γ → ι → γ) (a : α) (b : β),
        List.foldl op₃ (f a b) l = f (List.foldl op₁ a l) (List.foldl op₂ b l) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Bool) ([0]) (fun a b => a < b : ℕ → ℕ → Bool) (fun a b => a - b : ℕ → ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun (a : Bool) (n : ℕ) => n % 2 == 0) (0) (0)) (by
  decide +kernel)

-- Set.iUnion_congr_Prop, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iUnion_congr_Prop.h5 : ¬∀ {α : Type} {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α}, p ↔ q := fun hc_h => absurd (@hc_h (ℕ) (True) (False) (fun (a : True) => {n : ℕ | n = 0}) (fun (a : False) => {n : ℕ | n = 0})) (by
  decide +kernel)

-- Set.iUnion_congr_Prop, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iUnion_congr_Prop.h6 : ¬∀ {α : Type} {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α}, (p ↔ q) → Set.iUnion f₁ = Set.iUnion f₂ := fun hc_h => absurd (@hc_h (ℕ) (True) (True) (fun (a : True) => {n : ℕ | n = 0}) (fun (a : True) => {x : ℕ | False}) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- List.idxOf_cons_ne, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_cons_ne.h2 : ¬∀ {α : Type} [inst : BEq α] {a b : α} (l : List α), b ≠ a → List.idxOf a (b :: l) = (List.idxOf a l).succ := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) (0) (1) ([]) (by
  decide)) (by
  decide +kernel)

-- List.idxOf_cons_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_cons_ne.h6 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {a b : α} (l : List α),
        List.idxOf a (b :: l) = (List.idxOf a l).succ := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ (0) (0) ([])) (by
  decide +kernel)

-- Finite.ciInf_mono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finite.ciInf_mono.h6 : ¬∀ {α ι : Type} [inst : Finite ι] [inst : ConditionallyCompleteLattice α] {f g : ι → α}, iInf f ≤ iInf g := fun hc_h => absurd (@hc_h (Bool) (Bool) _ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toConditionallyCompleteLattice) (fun _ => true : Bool → Bool) (not : Bool → Bool)) (by
  simp)

-- Set.encard_le_encard_of_injOn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_le_encard_of_injOn.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.InjOn f s → s.encard ≤ t.encard := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- List.disjoint_map, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.disjoint_map.h6 : ¬∀ {α β : Type} {f : α → β} {s t : List α}, Function.Injective f → (List.map f s).Disjoint (List.map f t) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) ([Bool.false]) ([Bool.false]) (by
  decide)) (by
  simp)

-- List.forall_mem_of_forall_mem_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forall_mem_of_forall_mem_cons.h4 : ¬∀ {α : Type} {p : α → Prop} {a : α} {l : List α}, ∀ x ∈ l, p x := fun hc_h => absurd (@hc_h (Bool) (fun b => b = true : Bool → Prop) (Bool.false) ([Bool.false]) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- List.forall_mem_of_forall_mem_cons, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.forall_mem_of_forall_mem_cons.h6.inst : ¬(fun (n : ℕ) => n = 0) 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.forall_mem_of_forall_mem_cons.h6.prem0 : ∀ x ∈ [0], (fun (n : ℕ) => n = 0) x := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.forall_mem_of_forall_mem_cons.h6 : ¬∀ {α : Type} {p : α → Prop} {a : α} {l : List α}, (∀ x ∈ a :: l, p x) → ∀ (x : α), p x := fun hc_h => HypCheckProof.List.forall_mem_of_forall_mem_cons.h6.inst (@hc_h (ℕ) (fun (n : ℕ) => n = 0) (0) ([]) HypCheckProof.List.forall_mem_of_forall_mem_cons.h6.prem0 (1))

-- mem_of_mem_permsOfList, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.mem_of_mem_permsOfList.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {l : List α} {f : Equiv.Perm α} {x : α},
        @Ne α
            (@DFunLike.coe (Equiv.Perm α) α (fun (x : α) => α)
              (@EquivLike.toFunLike (Equiv.Perm α) α α (@Equiv.instEquivLike α α)) f x)
            x →
          @Membership.mem α (List α) (@List.instMembership α) l x) := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) (@List.nil Bool) (@Equiv.mk Bool Bool Bool.not Bool.not
      (@of_decide_eq_true (autoParam (@Function.LeftInverse Bool Bool Bool.not Bool.not) Equiv.left_inv._autoParam)
        (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not)
        (@id
          (@Eq Bool
            (@Decidable.decide (autoParam (@Function.LeftInverse Bool Bool Bool.not Bool.not) Equiv.left_inv._autoParam)
              (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true (autoParam (@Function.RightInverse Bool Bool Bool.not Bool.not) Equiv.right_inv._autoParam)
        (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not)
        (@id
          (@Eq Bool
            (@Decidable.decide (autoParam (@Function.RightInverse Bool Bool Bool.not Bool.not) Equiv.right_inv._autoParam)
              (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- mem_of_mem_permsOfList, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.mem_of_mem_permsOfList.h6 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {f : Equiv.Perm α}, f ∈ permsOfList l → ∀ {x : α}, x ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (1) (by
  (repeat' constructor) <;> done) (0)) (by
  decide +kernel)

-- List.IsPrefix.mem_iff_idxOf_lt_length, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.mem_iff_idxOf_lt_length.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α], l₁ <+: l₂ → ∀ (a : α), a ∈ l₁ ↔ List.idxOf a l₂ < l₁.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([0]) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) (by
  decide) (1)) (by
  decide +kernel)

-- List.IsPrefix.mem_iff_idxOf_lt_length, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.mem_iff_idxOf_lt_length.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] (a : α), a ∈ l₁ ↔ List.idxOf a l₂ < l₁.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (instBEqOfDecidableEq) _ (1)) (by
  decide +kernel)

-- List.IsPrefix.idxOf_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.idxOf_le.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] (a : α), List.idxOf a l₁ ≤ List.idxOf a l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (instBEqOfDecidableEq) _ (1)) (by
  decide +kernel)

-- List.getElem_set_of_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_set_of_ne.h4 : ¬∀ {α : Type} {l : List α} {i j : ℕ} (a : α) (hj : j < (l.set i a).length),
        GetElem.getElem (l.set i a) j hj = GetElem.getElem l j (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) ([0]) (0) (0) (1) hc_k0) (by
  decide +kernel)

-- List.getElem_set_of_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_set_of_ne.h6 : ¬∀ {α : Type} {l : List α} {i j : ℕ}, i ≠ j → ∀ (a : α), j < (l.set i a).length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (1) (by
  decide) (0)) (by
  decide +kernel)

-- List.idxOf_append_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_append_of_mem.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] {a : α}, a ∈ l₁ → List.idxOf a (l₁ ++ l₂) = List.idxOf a l₁ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([0]) (⟨fun a b => a != b⟩ : BEq ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- List.idxOf_append_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_append_of_mem.h6 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] {a : α}, List.idxOf a (l₁ ++ l₂) = List.idxOf a l₁ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (instBEqOfDecidableEq) _ (1)) (by
  decide +kernel)

-- Fin.pred_succAbove_pred, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.pred_succAbove_pred.h3 : ¬∀ {n : ℕ} {a : Fin (n + 2)} {b : Fin (n + 1)}, b ≠ 0 → a ≠ 0 := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.pred_succAbove_pred, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.pred_succAbove_pred.h4 : ¬∀ {n : ℕ} {a : Fin (n + 2)} {b : Fin (n + 1)}, a ≠ 0 → b ≠ 0 := fun hc_h => absurd (@hc_h (0) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- List.Sublist.of_cons_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.of_cons_of_ne.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} {a b : α}, (a :: l₁).Sublist (b :: l₂) → (a :: l₁).Sublist l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- List.Sublist.of_cons_of_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.of_cons_of_ne.h6 : ¬∀ {α : Type} {l₁ l₂ : List α} {a b : α}, a ≠ b → (a :: l₁).Sublist l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- not_injective_dotProduct_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_injective_dotProduct_right.h4 : ¬∀ {m α : Type} [inst : Fintype m] [inst_1 : CommRing α] [inst_2 : Nontrivial α] (a : m → α),
        ¬Function.Injective fun (x : m → α) => x ⬝ᵥ a := fun hc_h => absurd (@hc_h (Unit) (Bool) (PUnit.fintype) (BooleanRing.toCommRing) _ (fun (a : Unit) => Bool.true)) (by
  decide +kernel)

-- not_injective_dotProduct_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_injective_dotProduct_right.h5 : ¬∀ {m α : Type} [inst : Fintype m] [inst_1 : CommRing α] [inst_2 : Nontrivial m] (a : m → α),
        ¬Function.Injective fun (x : m → α) => x ⬝ᵥ a := fun hc_h => absurd (@hc_h (Bool) (Unit) (Bool.fintype) (PUnit.commRing) _ (fun (a : Bool) => PUnit.unit)) (by
  decide +kernel)

-- Fin.succAbove_ne_zero, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.succAbove_ne_zero.h4.gneg : ∀ {n : ℕ} [inst : NeZero n] {a : Fin (n + 1)} {b : Fin n}, ¬a ≠ 0 → b ≠ 0 → a.succAbove b ≠ 0 := by
  (intros; simp_all; done)
theorem HypCheckProof.Fin.succAbove_ne_zero.h4 : ∀ {n : ℕ} [inst : NeZero n] {a : Fin (n + 1)} {b : Fin n}, b ≠ 0 → a.succAbove b ≠ 0 := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x5
  exact Classical.byCases (fun hc_h => @Fin.succAbove_ne_zero hc_x0 hc_x1 hc_x2 hc_x3 hc_h hc_x5) (fun hc_hn => @HypCheckProof.Fin.succAbove_ne_zero.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn hc_x5)

-- Fin.succAbove_ne_zero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_ne_zero.h5 : ¬∀ {n : ℕ} [inst : NeZero n] {a : Fin (n + 1)} {b : Fin n}, a ≠ 0 → a.succAbove b ≠ 0 := fun hc_h => absurd (@hc_h (1) _ ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- Set.SurjOn.mapsTo_compl, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.mapsTo_compl.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Function.Injective f → Set.MapsTo f sᶜ tᶜ := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({b : Bool | b = Bool.true}) ({n : ℕ | n = 0}) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  simp)

-- Set.SurjOn.mapsTo_compl, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.mapsTo_compl.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.SurjOn f s t → Set.MapsTo f sᶜ tᶜ := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({b : Bool | b = Bool.true}) ({n : ℕ | n = 0}) (fun _ => 0 : Bool → ℕ) (by
  simp)) (by
  simp)

-- Finite.ciSup_mono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finite.ciSup_mono.h6 : ¬∀ {α ι : Type} [inst : Finite ι] [inst : ConditionallyCompleteLattice α] {f g : ι → α}, iSup f ≤ iSup g := fun hc_h => absurd (@hc_h (ℕ) (Fin 2) _ (Nat.instConditionallyCompleteLinearOrderBot.toConditionallyCompleteLattice) (fun (a : Fin 2) => 1) (fun (a : Fin 2) => 0)) (by
  simp)

-- Set.SurjOn.comap_nonempty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.comap_nonempty.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, t.Nonempty → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.restrict₂_comp_restrict₂, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.restrict₂_comp_restrict₂.h5 : ¬∀ {α : Type} {π : α → Type} {s t u : Set α}, t ⊆ u → s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.restrict₂_comp_restrict₂, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.restrict₂_comp_restrict₂.h6 : ¬∀ {α : Type} {π : α → Type} {s t u : Set α}, s ⊆ t → t ⊆ u := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  rfl)) (by
  simp)

-- List.get_insertIdx_add_succ, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.get_insertIdx_add_succ.h5 : ¬∀ {α : Type} (l : List α) (x : α) (n k : ℕ), n + k < l.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (0) (0)) (by
  decide +kernel)

-- List.get_insertIdx_add_succ, hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.get_insertIdx_add_succ.h6.der.{u} : ∀ {α : Type u} (l : List α) (x : α) (n k : ℕ), n + k < l.length → n + k + 1 < (l.insertIdx n x).length := by
  (intros; grind)
theorem HypCheckProof.List.get_insertIdx_add_succ.h6.{u} : ∀ {α : Type u} (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length),
      (l.insertIdx n x).get
          (⟨n + k + 1, HypCheckProof.List.get_insertIdx_add_succ.h6.der l x n k hk'⟩ : Fin (l.insertIdx n x).length) =
        l.get (⟨n + k, hk'⟩ : Fin l.length) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @List.get_insertIdx_add_succ hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.List.get_insertIdx_add_succ.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Function.invFunOn_apply_eq, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Function.invFunOn_apply_eq.h5.der.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {a : α},
      @Membership.mem α (Set α) (@Set.instMembership α) s a → Nonempty α := by
  (intros; solve_by_elim)
theorem HypCheckProof.Function.invFunOn_apply_eq.h5.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {a : α}
      (h : @Membership.mem α (Set α) (@Set.instMembership α) s a),
      @Eq β (f (@Function.invFunOn α β (@HypCheckProof.Function.invFunOn_apply_eq.h5.der α β s f a h) f s (f a))) (f a) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Function.invFunOn_apply_eq hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Function.invFunOn_apply_eq.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x5

-- Set.image2_image_left_anticomm, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_image_left_anticomm.h11 : ¬∀ {α α' β γ δ : Type} {s : Set α} {t : Set β} {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ},
        Set.image2 f (g '' s) t = g' '' Set.image2 f' t s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Fintype.card_lt_of_injective_not_surjective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_lt_of_injective_not_surjective.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] (f : α → β),
        ¬Function.Surjective f → Fintype.card α < Fintype.card β := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype) (fun _ => true : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Fintype.card_lt_of_injective_not_surjective, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_lt_of_injective_not_surjective.h6 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] (f : α → β),
        Function.Injective f → Fintype.card α < Fintype.card β := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- EReal.le_add_of_forall_gt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.le_add_of_forall_gt.h5 : ¬∀ {a b c : EReal}, a ≠ ⊥ ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ ⊥ → c ≤ a + b := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide) (by
  decide)) (by
  simp)

-- Set.preimage_subset_of_surjOn, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.preimage_subset_of_surjOn.h6 : ¬∀ {α β : Type} {f : α → β} {s : Set α} {t : Set β}, Function.Injective f → f ⁻¹' t ⊆ s := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) ({b : Bool | b = Bool.true}) ({n : ℕ | n = 0}) (by
  decide)) (by
  simp)

-- Nat.one_div_le_one_div, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.one_div_le_one_div.h6 : Not
      (∀ {α : Type} [inst : Semifield α] [inst_1 : LinearOrder α]
        [inst_2 :
          @IsStrictOrderedRing α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))
            (@SemilatticeInf.toPartialOrder α
              (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))]
        {n m : Nat},
        @LE.le α
          (@Preorder.toLE α
            (@PartialOrder.toPreorder α
              (@SemilatticeInf.toPartialOrder α
                (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
          (@HDiv.hDiv α α α
            (@instHDiv α
              (@DivInvMonoid.toDiv α
                (@GroupWithZero.toDivInvMonoid α
                  (@DivisionSemiring.toGroupWithZero α (@Semifield.toDivisionSemiring α inst)))))
            (@OfNat.ofNat α (nat_lit 1)
              (@One.toOfNat1 α
                (@AddMonoidWithOne.toOne α
                  (@AddCommMonoidWithOne.toAddMonoidWithOne α
                    (@NonAssocSemiring.toAddCommMonoidWithOne α
                      (@Semiring.toNonAssocSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))))
            (@HAdd.hAdd α α α
              (@instHAdd α
                (@Distrib.toAdd α
                  (@instDistribOfSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst)))))
              (@Nat.cast α
                (@AddMonoidWithOne.toNatCast α
                  (@AddCommMonoidWithOne.toAddMonoidWithOne α
                    (@NonAssocSemiring.toAddCommMonoidWithOne α
                      (@Semiring.toNonAssocSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))
                m)
              (@OfNat.ofNat α (nat_lit 1)
                (@One.toOfNat1 α
                  (@AddMonoidWithOne.toOne α
                    (@AddCommMonoidWithOne.toAddMonoidWithOne α
                      (@NonAssocSemiring.toAddCommMonoidWithOne α
                        (@Semiring.toNonAssocSemiring α
                          (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))))))
          (@HDiv.hDiv α α α
            (@instHDiv α
              (@DivInvMonoid.toDiv α
                (@GroupWithZero.toDivInvMonoid α
                  (@DivisionSemiring.toGroupWithZero α (@Semifield.toDivisionSemiring α inst)))))
            (@OfNat.ofNat α (nat_lit 1)
              (@One.toOfNat1 α
                (@AddMonoidWithOne.toOne α
                  (@AddCommMonoidWithOne.toAddMonoidWithOne α
                    (@NonAssocSemiring.toAddCommMonoidWithOne α
                      (@Semiring.toNonAssocSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))))
            (@HAdd.hAdd α α α
              (@instHAdd α
                (@Distrib.toAdd α
                  (@instDistribOfSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst)))))
              (@Nat.cast α
                (@AddMonoidWithOne.toNatCast α
                  (@AddCommMonoidWithOne.toAddMonoidWithOne α
                    (@NonAssocSemiring.toAddCommMonoidWithOne α
                      (@Semiring.toNonAssocSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))
                n)
              (@OfNat.ofNat α (nat_lit 1)
                (@One.toOfNat1 α
                  (@AddMonoidWithOne.toOne α
                    (@AddCommMonoidWithOne.toAddMonoidWithOne α
                      (@NonAssocSemiring.toAddCommMonoidWithOne α
                        (@Semiring.toNonAssocSemiring α
                          (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))))))) := fun hc_h => absurd (@hc_h (Rat) (@Field.toSemifield Rat Rat.instField) (Rat.linearOrder) _ (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- EReal.div_mul_div_cancel, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_mul_div_cancel.h5 : ¬∀ {a b c : EReal}, b ≠ ⊥ → b ≠ ⊤ → a / b * (b / c) = a / c := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.le_mul_of_forall_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.le_mul_of_forall_lt.h5 : ¬∀ {a b c : EReal}, 0 < a ∨ b ≠ ⊤ → a ≠ ⊤ ∨ 0 < b → c ≤ a * b := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  simp) (by
  decide)) (by
  simp)

-- List.Perm.eraseIdx_of_getElem?_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.eraseIdx_of_getElem?_eq.h6 : ¬∀ {α : Type} {l₁ l₂ : List α} {m n : ℕ}, l₁[m]? = l₂[n]? → (l₁.eraseIdx m).Perm (l₂.eraseIdx n) := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Function.invFunOn_mem, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Function.invFunOn_mem.h5.der.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {b : β},
      (∃ (a : α), And (@Membership.mem α (Set α) (@Set.instMembership α) s a) (@Eq β (f a) b)) → Nonempty α := by
  (intros; tauto)
theorem HypCheckProof.Function.invFunOn_mem.h5.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {b : β}
      (h : ∃ (a : α), And (@Membership.mem α (Set α) (@Set.instMembership α) s a) (@Eq β (f a) b)),
      @Membership.mem α (Set α) (@Set.instMembership α) s
        (@Function.invFunOn α β (@HypCheckProof.Function.invFunOn_mem.h5.der α β s f b h) f s b) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Function.invFunOn_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Function.invFunOn_mem.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x5

-- Function.invFunOn_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.invFunOn_mem.h6 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {b : β} [inst : Nonempty α], Function.invFunOn f s b ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ) (0) _) (by
  decide +kernel)

-- Set.pairwise_iff_exists_forall, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.pairwise_iff_exists_forall.h6 : ¬∀ {α ι : Type} [inst : Nonempty ι] (s : Set α) (f : α → ι) {r : ι → ι → Prop},
        s.Pairwise (Function.onFun r f) ↔ ∃ (z : ι), ∀ x ∈ s, r (f x) z := fun hc_h => absurd (@hc_h (ℕ) (Bool) _ ({n : ℕ | n = 0}) (fun n => n % 2 == 0 : ℕ → Bool) (fun _ _ => False : Bool → Bool → Prop)) (by
  simp)

-- Matrix.single_apply_of_ne, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.single_apply_of_ne.h11 : ¬∀ {m n α : Type} [inst : DecidableEq m] [inst_1 : DecidableEq n] [inst_2 : Zero α] (i : m) (j : n) (c : α) (i' : m)
        (j' : n), Matrix.single i j c i' j' = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (instDecidableEqNat) (instDecidableEqNat) (Nat.instMulZeroClass.toZero) (0) (0) (1) (0) (0)) (by
  decide +kernel)

-- List.Nodup.mem_diff_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.mem_diff_iff.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} {a : α} [inst : BEq α], l₁.Nodup → (a ∈ l₁.diff l₂ ↔ a ∈ l₁ ∧ a ∉ l₂) := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([1]) (0) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) (by
  decide)) (by
  decide +kernel)

-- Nat.minSqFac_le_of_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.minSqFac_le_of_dvd.h2 : ¬∀ {n d m : ℕ}, 2 ≤ m → m * m ∣ n → d ≤ m := fun hc_h => absurd (@hc_h (0) (3) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.minSqFac_le_of_dvd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.minSqFac_le_of_dvd.h4 : ¬∀ {n d : ℕ}, n.minSqFac = Option.some d → ∀ {m : ℕ}, m * m ∣ n → d ≤ m := fun hc_h => absurd (@hc_h (0) (2) (by
  decide) (0) (by
  decide)) (by
  decide +kernel)

-- Set.ncard_union_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_union_lt.h5 : ¬∀ {α : Type} {s t : Set α},
        autoParam s.Finite Set.ncard_union_lt._auto_1 →
          autoParam t.Finite Set.ncard_union_lt._auto_3 → (s ∪ t).ncard < s.ncard + t.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (by
  simp)) (by
  simp)

-- Set.image_image2_distrib_right, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_image2_distrib_right.h11 : ¬∀ {α β β' γ δ : Type} {f : α → β → γ} {s : Set α} {t : Set β} {g : γ → δ} {f' : α → β' → δ} {g' : β → β'},
        g '' Set.image2 f s t = Set.image2 f' s (g' '' t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Set.nonempty_inter_of_le_ncard_add_ncard, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nonempty_inter_of_le_ncard_add_ncard.h3 : ¬∀ {α : Type} {s t : Set α}, Nat.card α ≤ s.ncard + t.ncard → s ∪ t ≠ Set.univ → (s ∩ t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (by
  simp)) (by
  simp)

-- Set.nonempty_inter_of_le_ncard_add_ncard, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nonempty_inter_of_le_ncard_add_ncard.h4 : ¬∀ {α : Type} {s t : Set α} [inst : Finite α], s ∪ t ≠ Set.univ → (s ∩ t).Nonempty := fun hc_h => absurd (@hc_h (Bool) ({x : Bool | False}) ({x : Bool | False}) _ (by
  grind)) (by
  simp)

-- Set.nonempty_inter_of_le_ncard_add_ncard, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nonempty_inter_of_le_ncard_add_ncard.h5 : ¬∀ {α : Type} {s t : Set α} [inst : Finite α], Nat.card α ≤ s.ncard + t.ncard → (s ∩ t).Nonempty := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) _ (by
  simp)) (by
  simp)

-- Set.InjOn.preimage_image_inter, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.preimage_image_inter.h6 : ¬∀ {α β : Type} {s s₁ : Set α} {f : α → β}, Set.InjOn f s → f ⁻¹' f '' s₁ ∩ s = s₁ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- List.prev_getLast_cons', hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.prev_getLast_cons'.h5.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y : α), x = y → x ∈ y :: l := by
  (intros; simp_all; done)
theorem HypCheckProof.List.prev_getLast_cons'.h5.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y : α) (hx : x = y),
      (y :: l).prev x (HypCheckProof.List.prev_getLast_cons'.h5.der l x y hx) = (y :: l).getLast (List.cons_ne_nil y l) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @List.prev_getLast_cons' hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.List.prev_getLast_cons'.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x5

-- List.prev_getLast_cons', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_getLast_cons'.h6 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (x y : α) (hxy : x ∈ y :: l),
        (y :: l).prev x hxy = (y :: l).getLast (List.cons_ne_nil y l) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (instDecidableEqNat) ([0]) (0) (1) hc_k0) (by
  decide +kernel)

-- Nat.log.go_spec, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log.go_spec.h4 : ¬∀ {b n fuel : ℕ},
        1 < b →
          n < b ^ fuel →
            (Nat.log.go n b fuel).1 = n / b ^ (Nat.log.go n b fuel).2 ∧
              b ^ (Nat.log.go n b fuel).2 ≤ n ∧ n < b ^ ((Nat.log.go n b fuel).2 + 1) := fun hc_h => absurd (@hc_h (2) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.log.go_spec, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log.go_spec.h5 : ¬∀ {b n fuel : ℕ},
        1 < b →
          n ≠ 0 →
            (Nat.log.go n b fuel).1 = n / b ^ (Nat.log.go n b fuel).2 ∧
              b ^ (Nat.log.go n b fuel).2 ≤ n ∧ n < b ^ ((Nat.log.go n b fuel).2 + 1) := fun hc_h => absurd (@hc_h (2) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Finset.fold_empty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_empty.h3 : ¬∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {f : α → β} {b : β}, Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.fold_empty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_empty.h4 : ¬∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β}, Std.Associative op := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.false)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fintype.card_lt_of_surjective_not_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_lt_of_surjective_not_injective.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] (f : α → β),
        ¬Function.Injective f → Fintype.card β < Fintype.card α := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype) (fun _ => true : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Fintype.card_lt_of_surjective_not_injective, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_lt_of_surjective_not_injective.h6 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] (f : α → β),
        Function.Surjective f → Fintype.card β < Fintype.card α := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- List.Perm.take_inter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.take_inter.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {xs ys : List α} (n : ℕ), ys.Nodup → (List.take n xs).Perm (ys ∩ List.take n xs) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([]) (1) (by
  decide)) (by
  decide +kernel)

-- Set.SurjOn.bijOn_subset, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.bijOn_subset.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} [inst : Nonempty α], Set.BijOn f (Function.invFunOn f s '' t) t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) _) (by
  simp)

-- List.Pairwise.rel_get_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_get_of_lt.h3 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a b : Fin l.length}, a < b → R (l.get a) (l.get b) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.rel_get_of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_get_of_lt.h6 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α}, List.Pairwise R l → ∀ {a b : Fin l.length}, R (l.get a) (l.get b) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (by
  decide) (0) (0)) (by
  decide +kernel)

-- Function.invFunOn_apply_mem, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Function.invFunOn_apply_mem.h5.der.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {a : α},
      @Membership.mem α (Set α) (@Set.instMembership α) s a → Nonempty α := by
  (intros; solve_by_elim)
theorem HypCheckProof.Function.invFunOn_apply_mem.h5.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {a : α}
      (h : @Membership.mem α (Set α) (@Set.instMembership α) s a),
      @Membership.mem α (Set α) (@Set.instMembership α) s
        (@Function.invFunOn α β (@HypCheckProof.Function.invFunOn_apply_mem.h5.der α β s f a h) f s (f a)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Function.invFunOn_apply_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Function.invFunOn_apply_mem.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x5

-- Function.invFunOn_apply_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.invFunOn_apply_mem.h6 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {a : α} [inst : Nonempty α], Function.invFunOn f s (f a) ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ) (0) _) (by
  decide +kernel)

-- AddCommGroup.ModEq.intCast, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.AddCommGroup.ModEq.intCast.h6 : Not
      (∀ {G : Type} [inst : AddCommGroupWithOne G]
        [inst_1 : @CharZero G (@AddGroupWithOne.toAddMonoidWithOne G (@AddCommGroupWithOne.toAddGroupWithOne G inst))]
        {a b z : Int},
        @AddCommGroup.ModEq G (@AddCommMonoidWithOne.toAddCommMonoid G (@AddCommGroupWithOne.toAddCommMonoidWithOne G inst))
          (@Int.cast G (@AddGroupWithOne.toIntCast G (@AddCommGroupWithOne.toAddGroupWithOne G inst)) z)
          (@Int.cast G (@AddGroupWithOne.toIntCast G (@AddCommGroupWithOne.toAddGroupWithOne G inst)) a)
          (@Int.cast G (@AddGroupWithOne.toIntCast G (@AddCommGroupWithOne.toAddGroupWithOne G inst)) b)) := fun hc_h => absurd (@hc_h (Int) (@NonAssocRing.toAddCommGroupWithOne Int
      (@NonAssocCommRing.toNonAssocRing Int (@CommRing.toNonAssocCommRing Int Int.instCommRing))) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  simp)

-- Set.forall_of_forall_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.forall_of_forall_insert.h4 : ¬∀ {α : Type} {P : α → Prop} {a : α} {s : Set α}, ∀ x ∈ s, P x := fun hc_h => absurd (@hc_h (ℕ) (fun _ => False : ℕ → Prop) (0) ({n : ℕ | n = 0}) (0) (by
  decide)) (by
  decide +kernel)

-- Set.forall_of_forall_insert, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.forall_of_forall_insert.h6 : ¬∀ {α : Type} {P : α → Prop} {a : α} {s : Set α}, (∀ x ∈ Insert.insert a s, P x) → ∀ (x : α), P x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (0) ({n : ℕ | n = 0}) (by
  simp) (1)) (by
  decide +kernel)

-- List.IsChain.rel_head?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.rel_head?.h4 : ¬∀ {α : Type} {R : α → α → Prop} {x : α} {l : List α} ⦃y : α⦄, y ∈ l.head? → R x y := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) ([0]) (0) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.rel_head?, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.rel_head?.h6 : ¬∀ {α : Type} {R : α → α → Prop} {x : α} {l : List α}, List.IsChain R (x :: l) → ∀ ⦃y : α⦄, R x y := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) ([]) (by
  decide) (0)) (by
  decide +kernel)

-- List.IsChain.imp_head, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.imp_head.h4 : ¬∀ {α : Type} {R : α → α → Prop} {x y : α} {l : List α}, List.IsChain R (x :: l) → List.IsChain R (y :: l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (1) ([1]) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.imp_head, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.imp_head.h6 : ¬∀ {α : Type} {R : α → α → Prop} {x y : α}, (∀ {z : α}, R x z → R y z) → ∀ {l : List α}, List.IsChain R (y :: l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0) (by
  simp) ([0])) (by
  decide +kernel)

-- Set.MapsTo.surjOn_compl, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.surjOn_compl.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Function.Surjective f → Set.SurjOn f sᶜ tᶜ := fun hc_h => absurd (@hc_h (Bool) (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (not : Bool → Bool) (by
  decide)) (by
  simp)

-- Set.MapsTo.surjOn_compl, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.surjOn_compl.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.MapsTo f s t → Set.SurjOn f sᶜ tᶜ := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.true}) (fun _ => true : ℕ → Bool) (by
  simp)) (by
  simp)

-- List.head!_le_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.head!_le_of_lt.h5 : ¬∀ {α : Type} [inst : Preorder α] [inst_1 : Inhabited α] (l l' : List α), l' ≠ [] → l'.head! ≤ l.head! := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (instInhabitedNat) ([]) ([1]) (by
  decide)) (by
  decide +kernel)

-- Sigma.subtype_ext, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sigma.subtype_ext.h5 : Not
      (∀ {α β : Type} {p : α → β → Prop} {x₀ x₁ : @Sigma α fun (a : α) => @Subtype β (p a)},
        @Eq β
            (@Subtype.val β (p (@Sigma.fst α (fun (a : α) => @Subtype β (p a)) x₀))
              (@Sigma.snd α (fun (a : α) => @Subtype β (p a)) x₀))
            (@Subtype.val β (p (@Sigma.fst α (fun (a : α) => @Subtype β (p a)) x₁))
              (@Sigma.snd α (fun (a : α) => @Subtype β (p a)) x₁)) →
          @Eq (@Sigma α fun (a : α) => @Subtype β (p a)) x₀ x₁) := fun hc_h => absurd (@hc_h (Nat) (Bool) (fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true) (@Sigma.mk Nat (fun (a : Nat) => @Subtype Bool ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true) a))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Subtype.mk Bool
        ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        Bool.true
        (@of_decide_eq_true
          ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            Bool.true)
          (instDecidableEqBool Bool.true Bool.true)
          (@id
            (@Eq Bool
              (@Decidable.decide
                ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true)
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) Bool.true)
                (instDecidableEqBool Bool.true Bool.true))
              Bool.true)
            (@Eq.refl Bool Bool.true))))) (@Sigma.mk Nat (fun (a : Nat) => @Subtype Bool ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true) a))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@Subtype.mk Bool
        ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        Bool.true
        (@of_decide_eq_true
          ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            Bool.true)
          (instDecidableEqBool Bool.true Bool.true)
          (@id
            (@Eq Bool
              (@Decidable.decide
                ((fun (a : Nat) (b : Bool) => @Eq Bool b Bool.true)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Bool.true)
                (instDecidableEqBool Bool.true Bool.true))
              Bool.true)
            (@Eq.refl Bool Bool.true))))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Finset.map_disjUnion, hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finset.map_disjUnion.h6.der.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {f : α ↪ β} (s₁ s₂ : Finset α),
      Disjoint s₁ s₂ → Disjoint (Finset.map f s₁) (Finset.map f s₂) := by
  (intros; simp_all; done)
theorem HypCheckProof.Finset.map_disjUnion.h6.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {f : α ↪ β} (s₁ s₂ : Finset α) (h : Disjoint s₁ s₂),
      Finset.map f (s₁.disjUnion s₂ h) =
        (Finset.map f s₁).disjUnion (Finset.map f s₂) (HypCheckProof.Finset.map_disjUnion.h6.der s₁ s₂ h) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Finset.map_disjUnion hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Finset.map_disjUnion.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Int.not_prime_of_int_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.not_prime_of_int_mul.h3 : ¬∀ {a b : ℤ} {c : ℕ}, b.natAbs ≠ 1 → a * b = ↑c → ¬Nat.Prime c := fun hc_h => absurd (@hc_h (1) (2) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.not_prime_of_int_mul, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.not_prime_of_int_mul.h4 : ¬∀ {a b : ℤ} {c : ℕ}, a.natAbs ≠ 1 → a * b = ↑c → ¬Nat.Prime c := fun hc_h => absurd (@hc_h (2) (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.not_prime_of_int_mul, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.not_prime_of_int_mul.h5 : ¬∀ {a b : ℤ} {c : ℕ}, a.natAbs ≠ 1 → b.natAbs ≠ 1 → ¬Nat.Prime c := fun hc_h => absurd (@hc_h (0) (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Interleaves.mono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Interleaves.mono.h3 : ¬∀ {α : Type} {r s : α → α → Prop} (l₁ l₂ : List α), List.Interleaves r l₁ l₂ → List.Interleaves s l₁ l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) ([0]) (by
  simp)) (by
  simp)

-- List.Interleaves.mono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Interleaves.mono.h6 : ¬∀ {α : Type} {r s : α → α → Prop}, (∀ ⦃a b : α⦄, r a b → s a b) → ∀ (l₁ l₂ : List α), List.Interleaves s l₁ l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (by
  simp) ([0]) ([])) (by
  simp)

-- Set.SurjOn.mapsTo_invFunOn, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.mapsTo_invFunOn.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} [inst : Nonempty α], Set.MapsTo (Function.invFunOn f s) t s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) _) (by
  simp)

-- List.Shortlex.of_cons, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Shortlex.of_cons.h2 : ¬∀ {α : Type} {r : α → α → Prop} {a : α} {s t : List α}, List.Shortlex r (a :: s) (a :: t) → List.Shortlex r s t := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (0) ([]) ([]) (by
  simp)) (by
  simp)

-- List.Shortlex.of_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Shortlex.of_cons.h6 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Std.Irrefl r] {a : α} {s t : List α}, List.Shortlex r s t := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ (0) ([]) ([])) (by
  simp)

-- List.splitBy_flatten, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitBy_flatten.h3.inst : ¬List.splitBy (fun (a b : ℕ) => Decidable.decide (a < b)) [[]].flatten = [[]] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitBy_flatten.h3.prem0 : ∀ m ∈ [[]], List.IsChain (fun (x y : ℕ) => (fun (a b : ℕ) => Decidable.decide (a < b)) x y = Bool.true) m := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitBy_flatten.h3.prem1 : List.IsChain
      (fun (a b : List ℕ) =>
        ∃ (ha : a ≠ []) (hb : b ≠ []), (fun (a b : ℕ) => Decidable.decide (a < b)) (a.getLast ha) (b.head hb) = Bool.false)
      [[]] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.splitBy_flatten.h3 : ¬∀ {α : Type} {r : α → α → Bool} {l : List (List α)},
        (∀ m ∈ l, List.IsChain (fun (x y : α) => r x y = Bool.true) m) →
          List.IsChain (fun (a b : List α) => ∃ (ha : a ≠ []) (hb : b ≠ []), r (a.getLast ha) (b.head hb) = Bool.false) l →
            List.splitBy r l.flatten = l := fun hc_h => HypCheckProof.List.splitBy_flatten.h3.inst (@hc_h (ℕ) (fun (a b : ℕ) => Decidable.decide (a < b)) ([[]]) HypCheckProof.List.splitBy_flatten.h3.prem0 HypCheckProof.List.splitBy_flatten.h3.prem1)

-- List.splitBy_flatten, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitBy_flatten.h5.inst : ¬List.splitBy (fun (a b : ℕ) => Decidable.decide (a < b)) [[0], [1]].flatten = [[0], [1]] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitBy_flatten.h5.prem0 : [] ∉ [[0], [1]] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitBy_flatten.h5.prem1 : ∀ m ∈ [[0], [1]], List.IsChain (fun (x y : ℕ) => (fun (a b : ℕ) => Decidable.decide (a < b)) x y = Bool.true) m := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.splitBy_flatten.h5 : ¬∀ {α : Type} {r : α → α → Bool} {l : List (List α)},
        [] ∉ l → (∀ m ∈ l, List.IsChain (fun (x y : α) => r x y = Bool.true) m) → List.splitBy r l.flatten = l := fun hc_h => HypCheckProof.List.splitBy_flatten.h5.inst (@hc_h (ℕ) (fun (a b : ℕ) => Decidable.decide (a < b)) ([[0], [1]]) HypCheckProof.List.splitBy_flatten.h5.prem0 HypCheckProof.List.splitBy_flatten.h5.prem1)

-- Nat.Prime.coprime_descFactorial_of_lt_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.coprime_descFactorial_of_lt_of_le.h3 : ¬∀ {p n k : ℕ}, n < p → k ≤ n → p.Coprime (n.descFactorial k) := fun hc_h => absurd (@hc_h (4) (2) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.coprime_descFactorial_of_lt_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.coprime_descFactorial_of_lt_of_le.h4 : ¬∀ {p n k : ℕ}, Nat.Prime p → k ≤ n → p.Coprime (n.descFactorial k) := fun hc_h => absurd (@hc_h (2) (2) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.coprime_descFactorial_of_lt_of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.coprime_descFactorial_of_lt_of_le.h5 : ¬∀ {p n k : ℕ}, Nat.Prime p → n < p → p.Coprime (n.descFactorial k) := fun hc_h => absurd (@hc_h (2) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Finset.map_disjUnion', hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finset.map_disjUnion'.h6.der.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {f : α ↪ β} (s₁ s₂ : Finset α),
      Disjoint (Finset.map f s₁) (Finset.map f s₂) → Disjoint s₁ s₂ := by
  (intros; simp_all; done)
theorem HypCheckProof.Finset.map_disjUnion'.h6.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {f : α ↪ β} (s₁ s₂ : Finset α) (h' : Disjoint (Finset.map f s₁) (Finset.map f s₂)),
      Finset.map f (s₁.disjUnion s₂ (HypCheckProof.Finset.map_disjUnion'.h6.der s₁ s₂ h')) =
        (Finset.map f s₁).disjUnion (Finset.map f s₂) h' := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Finset.map_disjUnion' hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Finset.map_disjUnion'.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Int.ModEq.add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.add.h5 : ¬∀ {n a b c d : ℤ}, c ≡ d [ZMOD n] → a + c ≡ b + d [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.add, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.add.h6 : ¬∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → a + c ≡ b + d [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.coprime_choose_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.coprime_choose_of_lt.h3 : ¬∀ {p a b : ℕ}, b < p → a ≤ b → p.Coprime (b.choose a) := fun hc_h => absurd (@hc_h (4) (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.coprime_choose_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.coprime_choose_of_lt.h4 : ¬∀ {p a b : ℕ}, Nat.Prime p → a ≤ b → p.Coprime (b.choose a) := fun hc_h => absurd (@hc_h (2) (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.coprime_choose_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.coprime_choose_of_lt.h5 : ¬∀ {p a b : ℕ}, Nat.Prime p → b < p → p.Coprime (b.choose a) := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Finsupp.zipWith_single_single, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.zipWith_single_single.h8 : ¬∀ {α M N P : Type} [inst : Zero M] [inst_1 : Zero N] [inst_2 : Zero P] (f : M → N → P) (a : α) (m : M) (n : N),
        f 0 0 = 0 := fun hc_h => absurd (@hc_h (ℕ) (Bool) (ℕ) (ℕ) (instZeroBool_mathlib) (Nat.instMulZeroClass.toZero) (Nat.instMulZeroClass.toZero) (fun (a : Bool) (n : ℕ) => n + 1) (0) (Bool.false) (0)) (by
  decide +kernel)

-- Nat.nth_ne_zero_anti, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_ne_zero_anti.h1 : ¬∀ {p : ℕ → Prop} {a b : ℕ}, a ≤ b → Nat.nth p b ≠ 0 → Nat.nth p a ≠ 0 := fun hc_h => absurd (@hc_h (fun _ => True : ℕ → Prop) (0) (1) (by
  decide) (by
  simp)) (by
  simp)

-- Nat.nth_ne_zero_anti, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.nth_ne_zero_anti.h5.inst : ¬Nat.nth (fun (x : ℕ) => False) 0 ≠ 0 := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.nth_ne_zero_anti.h5.prem0 : ¬(fun (x : ℕ) => False) 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.nth_ne_zero_anti.h5.prem1 : 0 ≤ 0 := by
  decide
theorem HypCheckProof.Nat.nth_ne_zero_anti.h5 : ¬∀ {p : ℕ → Prop}, ¬p 0 → ∀ {a b : ℕ}, a ≤ b → Nat.nth p a ≠ 0 := fun hc_h => HypCheckProof.Nat.nth_ne_zero_anti.h5.inst (@hc_h (fun (x : ℕ) => False) HypCheckProof.Nat.nth_ne_zero_anti.h5.prem0 (0) (0) HypCheckProof.Nat.nth_ne_zero_anti.h5.prem1)

-- Nat.le_of_nth_le_nth_of_lt_card, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_of_nth_le_nth_of_lt_card.h5 : ¬∀ {p : ℕ → Prop}, (Set.ofPred p).Finite → ∀ {m n : ℕ}, Nat.nth p m ≤ Nat.nth p n → m ≤ n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (by
  simp) (1) (0) (by
  simp)) (by
  decide +kernel)

-- AddCommGroup.ModEq.of_intCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.AddCommGroup.ModEq.of_intCast.h2 : Not
      (∀ {G : Type} [inst : AddCommGroupWithOne G] {a b z : Int},
        @AddCommGroup.ModEq G (@AddCommMonoidWithOne.toAddCommMonoid G (@AddCommGroupWithOne.toAddCommMonoidWithOne G inst))
            (@Int.cast G (@AddGroupWithOne.toIntCast G (@AddCommGroupWithOne.toAddGroupWithOne G inst)) z)
            (@Int.cast G (@AddGroupWithOne.toIntCast G (@AddCommGroupWithOne.toAddGroupWithOne G inst)) a)
            (@Int.cast G (@AddGroupWithOne.toIntCast G (@AddCommGroupWithOne.toAddGroupWithOne G inst)) b) →
          @AddCommGroup.ModEq Int Int.instAddCommMonoid z a b) := fun hc_h => absurd (@hc_h (Bool) (@NonAssocRing.toAddCommGroupWithOne Bool
      (@NonAssocCommRing.toNonAssocRing Bool
        (@CommRing.toNonAssocCommRing Bool (@BooleanRing.toCommRing Bool instBooleanRingBool)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (by
  rfl)) (by
  simp)

-- AddCommGroup.ModEq.of_intCast, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.AddCommGroup.ModEq.of_intCast.h6 : ¬∀ {G : Type} [inst : AddCommGroupWithOne G] [inst : CharZero G] {a b z : ℤ}, a ≡ b [PMOD z] := fun hc_h => absurd (@hc_h (ℤ) (CommRing.toNonAssocCommRing.toAddCommGroupWithOne) _ (0) (1) (0)) (by
  simp)

-- Int.ModEq.add_right_cancel, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.add_right_cancel.h5 : ¬∀ {n a b c d : ℤ}, a + c ≡ b + d [ZMOD n] → a ≡ b [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.add_right_cancel, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.add_right_cancel.h6 : ¬∀ {n a b c d : ℤ}, c ≡ d [ZMOD n] → a ≡ b [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Disjoint.of_preimage, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.of_preimage.h3 : ¬∀ {α β : Type} {f : α → β} {s t : Set β}, Disjoint (f ⁻¹' s) (f ⁻¹' t) → Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n % 2 = 0}) (by
  grind)) (by
  simp)

-- Disjoint.of_preimage, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.of_preimage.h6 : ¬∀ {α β : Type} {f : α → β}, Function.Surjective f → ∀ {s t : Set β}, Disjoint s t := fun hc_h => absurd (@hc_h (Bool) (Bool) (not : Bool → Bool) (by
  decide) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true})) (by
  simp)

-- Option.map_map₂_right_anticomm, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.map_map₂_right_anticomm.h11 : ¬∀ {α β γ δ : Type} {a : Option α} {b : Option β} {β' : Type} {f : α → β' → γ} {g : β → β'} {f' : β → α → δ}
        {g' : δ → γ}, Option.map₂ f a (Option.map g b) = Option.map g' (Option.map₂ f' b a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (Option.some 0) (Option.some 0) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Nat.prime_eq_prime_of_dvd_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prime_eq_prime_of_dvd_pow.h3 : ¬∀ {m p q : ℕ}, Nat.Prime q → p ∣ q ^ m → p = q := fun hc_h => absurd (@hc_h (0) (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.prime_eq_prime_of_dvd_pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prime_eq_prime_of_dvd_pow.h4 : ¬∀ {m p q : ℕ}, Nat.Prime p → p ∣ q ^ m → p = q := fun hc_h => absurd (@hc_h (1) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.prime_eq_prime_of_dvd_pow, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prime_eq_prime_of_dvd_pow.h5 : ¬∀ {m : ℕ} {p q : ℕ}, Nat.Prime p → Nat.Prime q → p = q := fun hc_h => absurd (@hc_h (0) (2) (3) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.idxOf_getLast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_getLast.h2 : ¬∀ {α : Type} [inst : BEq α] {l : List α} (hl : l ≠ []),
        l.getLast hl ∉ l.dropLast → List.idxOf (l.getLast hl) l = l.length - 1 := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) ([0, 1]) hc_k0 hc_k1) (by
  decide +kernel)

-- List.idxOf_getLast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_getLast.h4 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {l : List α}, l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ ([])) (by
  decide +kernel)

-- List.idxOf_getLast, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_getLast.h5 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l : List α} (hl : l ≠ []),
        List.idxOf (l.getLast hl) l = l.length - 1 := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (instBEqOfDecidableEq) _ ([0, 0]) hc_k0) (by
  decide +kernel)

-- ZMod.cast_intCast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.cast_intCast.h4 : Not
      (∀ {n : Nat} {R : Type} [inst : Ring R] {m : Nat},
        @Dvd.dvd Nat Nat.instDvd m n →
          ∀ (k : Int),
            @Eq R
              (@ZMod.cast R (@Ring.toAddGroupWithOne R inst) n
                (@Int.cast (ZMod n)
                  (@AddGroupWithOne.toIntCast (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
                  k))
              (@Int.cast R (@AddGroupWithOne.toIntCast R (@Ring.toAddGroupWithOne R inst)) k)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Bool) (@BooleanRing.toRing Bool instBooleanRingBool) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  decide +kernel)

-- Nat.eq_one_of_dvd_coprimes, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_one_of_dvd_coprimes.h3 : ¬∀ {a b k : ℕ}, k ∣ a → k ∣ b → k = 1 := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.eq_one_of_dvd_coprimes, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_one_of_dvd_coprimes.h4 : ¬∀ {a b k : ℕ}, a.Coprime b → k ∣ b → k = 1 := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.eq_one_of_dvd_coprimes, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_one_of_dvd_coprimes.h5 : ¬∀ {a b k : ℕ}, a.Coprime b → k ∣ a → k = 1 := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.idxOf_cons_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_cons_eq.h2 : ¬∀ {α : Type} [inst : BEq α] {a b : α} (l : List α), b = a → List.idxOf a (b :: l) = 0 := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a != b⟩ : BEq ℕ) (0) _ ([]) rfl) (by
  decide +kernel)

-- List.idxOf_cons_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_cons_eq.h6 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {a b : α} (l : List α), List.idxOf a (b :: l) = 0 := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ (0) (1) ([])) (by
  decide +kernel)

-- List.foldr_hom₂, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldr_hom₂.h11 : ¬∀ {ι α β γ : Type} (l : List ι) (f : α → β → γ) (op₁ : ι → α → α) (op₂ : ι → β → β) (op₃ : ι → γ → γ) (a : α) (b : β),
        List.foldr op₃ (f a b) l = f (List.foldr op₁ a l) (List.foldr op₂ b l) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) ([1]) (fun a b => a - b : ℕ → ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) (0)) (by
  decide +kernel)

-- List.mem_take_iff_idxOf_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_take_iff_idxOf_lt.h2 : ¬∀ {α : Type} [inst : BEq α] {a : α} {n : ℕ} {l : List α}, a ∈ l → (a ∈ List.take n l ↔ List.idxOf a l < n) := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a != b⟩ : BEq ℕ) (0) (1) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.mem_take_iff_idxOf_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_take_iff_idxOf_lt.h6 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {a : α} {n : ℕ} {l : List α}, a ∈ List.take n l ↔ List.idxOf a l < n := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ (0) (1) ([])) (by
  decide +kernel)

-- Nat.digits_zero_of_eq_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_zero_of_eq_zero.h1 : ¬∀ {b : ℕ} {L : List ℕ}, Nat.ofDigits b L = 0 → ∀ l ∈ L, l = 0 := fun hc_h => absurd (@hc_h (0) ([0, 1]) (by
  decide) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.digits_zero_of_eq_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_zero_of_eq_zero.h3 : ¬∀ {b : ℕ}, b ≠ 0 → ∀ {L : List ℕ}, ∀ l ∈ L, l = 0 := fun hc_h => absurd (@hc_h (1) (by
  decide) ([1]) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.digits_zero_of_eq_zero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_zero_of_eq_zero.h5 : ¬∀ {b : ℕ}, b ≠ 0 → ∀ {L : List ℕ}, Nat.ofDigits b L = 0 → ∀ (l : ℕ), l = 0 := fun hc_h => absurd (@hc_h (1) (by
  decide) ([]) (by
  decide) (1)) (by
  decide +kernel)

-- Option.map_map₂_antidistrib_right, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.map_map₂_antidistrib_right.h11 : ¬∀ {α β γ δ : Type} {f : α → β → γ} {a : Option α} {b : Option β} {α' : Type} {g : γ → δ} {f' : β → α' → δ}
        {g' : α → α'}, Option.map g (Option.map₂ f a b) = Option.map₂ f' b (Option.map g' a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (Option.some 0) (Option.some 0) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Nat.gcd_greatest, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.gcd_greatest.h3 : ¬∀ {a b d : ℕ}, d ∣ b → (∀ (e : ℕ), e ∣ a → e ∣ b → e ∣ d) → d = a.gcd b := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Nat.gcd_greatest, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.gcd_greatest.h4 : ¬∀ {a b d : ℕ}, d ∣ a → (∀ (e : ℕ), e ∣ a → e ∣ b → e ∣ d) → d = a.gcd b := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Nat.gcd_greatest, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.gcd_greatest.h5 : ¬∀ {a b d : ℕ}, d ∣ a → d ∣ b → d = a.gcd b := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.enumerate_eq_none, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.enumerate_eq_none.h5 : ¬∀ {α : Type} (sel : Set α → Option α) {s : Set α} {n₁ n₂ : ℕ}, n₁ ≤ n₂ → Set.enumerate sel s n₂ = Option.none := fun hc_h => absurd (@hc_h (ℕ) (fun (a : Set ℕ) => Option.some 0) ({n : ℕ | n = 0}) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.mul, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.mul.h5 : ¬∀ {n a b c d : ℕ}, c ≡ d [MOD n] → a * c ≡ b * d [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.mul, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.mul.h6 : ¬∀ {n a b c d : ℕ}, a ≡ b [MOD n] → a * c ≡ b * d [MOD n] := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.Ico_pow_dvd_eq_Ico_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Ico_pow_dvd_eq_Ico_of_lt.h4 : ¬∀ {n p b : ℕ}, Nat.Prime p → n < p ^ b → {i ∈ Finset.Ico 1 n | p ^ i ∣ n} = {i ∈ Finset.Ico 1 b | p ^ i ∣ n} := fun hc_h => absurd (@hc_h (0) (2) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Ico_pow_dvd_eq_Ico_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Ico_pow_dvd_eq_Ico_of_lt.h5 : ¬∀ {n p b : ℕ}, Nat.Prime p → n ≠ 0 → {i ∈ Finset.Ico 1 n | p ^ i ∣ n} = {i ∈ Finset.Ico 1 b | p ^ i ∣ n} := fun hc_h => absurd (@hc_h (2) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.add.h5 : ¬∀ {n a b c d : ℕ}, c ≡ d [MOD n] → a + c ≡ b + d [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.add, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.add.h6 : ¬∀ {n a b c d : ℕ}, a ≡ b [MOD n] → a + c ≡ b + d [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Equiv.bijOn_swap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.bijOn_swap.h5 : ¬∀ {α : Type} {s : Set α} [inst : DecidableEq α] {a b : α}, b ∈ s → Set.BijOn (⇑(Equiv.swap a b)) s s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (instDecidableEqNat) (1) (0) (by
  decide)) (by
  simp)

-- Equiv.bijOn_swap, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.bijOn_swap.h6 : ¬∀ {α : Type} {s : Set α} [inst : DecidableEq α] {a b : α}, a ∈ s → Set.BijOn (⇑(Equiv.swap a b)) s s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (instDecidableEqNat) (0) (1) (by
  decide)) (by
  simp)

-- Nat.factorization_le_factorization_of_dvd_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_le_factorization_of_dvd_right.h3 : ¬∀ {a b c : ℕ}, b ≠ 0 → c ≠ 0 → b.factorization a ≤ c.factorization a := fun hc_h => absurd (@hc_h (2) (2) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_le_factorization_of_dvd_right, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Nat.factorization_le_factorization_of_dvd_right.h4.gneg : ∀ {a b c : ℕ}, b ∣ c → ¬b ≠ 0 → c ≠ 0 → b.factorization a ≤ c.factorization a := by
  (intros; simp_all; done)
theorem HypCheckProof.Nat.factorization_le_factorization_of_dvd_right.h4 : ∀ {a b c : ℕ}, b ∣ c → c ≠ 0 → b.factorization a ≤ c.factorization a := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x5
  exact Classical.byCases (fun hc_h => @Nat.factorization_le_factorization_of_dvd_right hc_x0 hc_x1 hc_x2 hc_x3 hc_h hc_x5) (fun hc_hn => @HypCheckProof.Nat.factorization_le_factorization_of_dvd_right.h4.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_hn hc_x5)

-- Nat.factorization_le_factorization_of_dvd_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_le_factorization_of_dvd_right.h5 : ¬∀ {a b c : ℕ}, b ∣ c → b ≠ 0 → b.factorization a ≤ c.factorization a := fun hc_h => absurd (@hc_h (2) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.add_right_cancel, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.add_right_cancel.h5 : ¬∀ {n a b c d : ℕ}, a + c ≡ b + d [MOD n] → a ≡ b [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.add_right_cancel, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.add_right_cancel.h6 : ¬∀ {n a b c d : ℕ}, c ≡ d [MOD n] → a ≡ b [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_choose_prime_pow_add_factorization, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose_prime_pow_add_factorization.h3 : ¬∀ {p n k : ℕ}, k ≤ p ^ n → k ≠ 0 → ((p ^ n).choose k).factorization p + k.factorization p = n := fun hc_h => absurd (@hc_h (1) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_choose_prime_pow_add_factorization, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose_prime_pow_add_factorization.h4 : ¬∀ {p n k : ℕ}, Nat.Prime p → k ≠ 0 → ((p ^ n).choose k).factorization p + k.factorization p = n := fun hc_h => absurd (@hc_h (2) (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_choose_prime_pow_add_factorization, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose_prime_pow_add_factorization.h5 : ¬∀ {p n k : ℕ}, Nat.Prime p → k ≤ p ^ n → ((p ^ n).choose k).factorization p + k.factorization p = n := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- DFinsupp.comapDomain'_single, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.comapDomain'_single.h8 : ¬∀ {ι : Type} {β : ι → Type} {κ : Type} [inst : DecidableEq ι] [inst : DecidableEq κ] [inst : (i : ι) → Zero (β i)]
        (h : κ → ι) {h' : ι → κ} (k : κ) (x : β (h k)), Function.LeftInverse h' h := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (Bool) (instDecidableEqNat) (instDecidableEqBool) (fun (i : ℕ) => Nat.instMulZeroClass.toZero) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.false) (0)) (by
  decide +kernel)

-- FiniteInter.finiteInterClosure_insert, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FiniteInter.finiteInterClosure_insert.h3 : ¬∀ {α : Type} {S : Set (Set α)} {A : Set α},
        ∀ P ∈ FiniteInter.finiteInterClosure (Insert.insert A S), P ∈ S ∨ ∃ Q ∈ S, P = A ∩ Q := fun hc_h => absurd (@hc_h (ℕ) (∅) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Set.inter_congr_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_congr_left.h4 : ¬∀ {α : Type} {s t u : Set α}, s ∩ t ⊆ u → s ∩ t = s ∩ u := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.inter_congr_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_congr_left.h5 : ¬∀ {α : Type} {s t u : Set α}, s ∩ u ⊆ t → s ∩ t = s ∩ u := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Part.bind_defined, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.bind_defined.h4 : ¬∀ {α β : Type} {f : Part α} {g : α → Part β}, f.Dom := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (⊥) (fun (a : ℕ) => 0)) (by
  nofun)

-- Part.bind_defined, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.bind_defined.h5 : ¬∀ {α β : Type} {f : Part α} {g : α → Part β}, f.Dom → (f.bind g).Dom := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) (fun (a : ℕ) => ⊥) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.mem_unique, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.mem_unique.h4 : ¬∀ {α : Type} {a b : α} {o : Part α}, b ∈ o → a = b := fun hc_h => absurd (@hc_h (ℕ) (1) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Part.mem_unique, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.mem_unique.h5 : ¬∀ {α : Type} {a b : α} {o : Part α}, a ∈ o → a = b := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (0) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Part.mem_assert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.mem_assert.h4 : ¬∀ {α : Type} {p : Prop} {f : p → Part α} {a : α}, p := fun hc_h => absurd (@hc_h (ℕ) (False) (fun (a : False) => 0) (0)) (by
  decide +kernel)

-- Part.mem_assert, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.mem_assert.h5 : ¬∀ {α : Type} {p : Prop} {f : p → Part α} {a : α}, p → a ∈ Part.assert p f := fun hc_h => absurd (@hc_h (ℕ) (True) (fun (a : True) => 0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  nofun)

-- ENat.add_lt_add, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.add_lt_add.h4 : ¬∀ {a b c d : ℕ∞}, b < d → a + b < c + d := fun hc_h => absurd (@hc_h (1) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- ENat.add_lt_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.add_lt_add.h5 : ¬∀ {a b c d : ℕ∞}, a < c → a + b < c + d := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.cancel_left_div_gcd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.cancel_left_div_gcd.h4 : ¬∀ {m a b c : ℕ}, c * a ≡ c * b [MOD m] → a ≡ b [MOD m / m.gcd c] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.cancel_left_div_gcd, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.cancel_left_div_gcd.h5 : ¬∀ {m a b c : ℕ}, 0 < m → a ≡ b [MOD m / m.gcd c] := fun hc_h => absurd (@hc_h (2) (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.mod_lcm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mod_lcm.h4 : ¬∀ {m n a b : ℕ}, a ≡ b [MOD m] → a ≡ b [MOD n.lcm m] := fun hc_h => absurd (@hc_h (1) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.mod_lcm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mod_lcm.h5 : ¬∀ {m n a b : ℕ}, a ≡ b [MOD n] → a ≡ b [MOD n.lcm m] := fun hc_h => absurd (@hc_h (0) (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.trans.h4 : ¬∀ {n a b c : ℕ}, b ≡ c [MOD n] → a ≡ c [MOD n] := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.trans.h5 : ¬∀ {n a b c : ℕ}, a ≡ b [MOD n] → a ≡ c [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.cancel_right_of_coprime, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.cancel_right_of_coprime.h4 : ¬∀ {m a b c : ℕ}, a * c ≡ b * c [MOD m] → a ≡ b [MOD m] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.cancel_right_of_coprime, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.cancel_right_of_coprime.h5 : ¬∀ {m a b c : ℕ}, m.gcd c = 1 → a ≡ b [MOD m] := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Option.map_comm, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.map_comm.h8 : ¬∀ {α β γ δ : Type} {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (a : α),
        Option.map g₁ (Option.map f₁ (Option.some a)) = Option.map g₂ (Option.map f₂ (Option.some a)) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (0)) (by
  decide +kernel)

-- Set.iInter_eq_const, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iInter_eq_const.h5 : ¬∀ {α ι : Type} [inst : Nonempty ι] {f : ι → Set α} {s : Set α}, ⋂ (i : ι), f i = s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _ (fun (a : ℕ) => {n : ℕ | n = 0}) ({x : ℕ | True})) (by
  simp)

-- Set.encard_preimage_of_injective_subset_range, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_preimage_of_injective_subset_range.h4 : ¬∀ {α β : Type} {t : Set β} {f : α → β}, t ⊆ Set.range f → (f ⁻¹' t).encard = t.encard := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.encard_preimage_of_injective_subset_range, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_preimage_of_injective_subset_range.h5 : ¬∀ {α β : Type} {t : Set β} {f : α → β}, Function.Injective f → (f ⁻¹' t).encard = t.encard := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({x : ℕ | True}) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  simp)

-- Multiset.fold_singleton, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_singleton.h2 : ¬∀ {α : Type} (op : α → α → α) [ha : Std.Associative op] (b a : α), Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.fold_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_singleton.h3 : ¬∀ {α : Type} (op : α → α → α) [hc : Std.Commutative op] (b a : α), Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (Bool.false) (Bool.false)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.coe_fold_r, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.coe_fold_r.h2 : ¬∀ {α : Type} (op : α → α → α) [ha : Std.Associative op] (b : α) (l : List α), Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (0) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.coe_fold_r, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.coe_fold_r.h3 : ¬∀ {α : Type} (op : α → α → α) [hc : Std.Commutative op] (b : α) (l : List α), Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (Bool.false) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.coe_fold_l, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.coe_fold_l.h2 : ¬∀ {α : Type} (op : α → α → α) [ha : Std.Associative op] (b : α) (l : List α), Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (0) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.coe_fold_l, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.coe_fold_l.h3 : ¬∀ {α : Type} (op : α → α → α) [hc : Std.Commutative op] (b : α) (l : List α), Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (Bool.false) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.pairwise_pair_of_symm_of_refl, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.pairwise_pair_of_symm_of_refl.h5 : Not
      (∀ {α : Type} {r : α → α → Prop} {a b : α} [inst : @Std.Symm α r],
        Iff
          (@Set.Pairwise α
            (@Insert.insert α (Set α) (@Set.instInsert α) a (@Singleton.singleton α (Set α) (@Set.instSingletonSet α) b)) r)
          (r a b)) := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => False : Bool → Bool → Prop) (Bool.false) (Bool.false) _) (by
  simp)

-- Function.Injective.existsUnique_of_mem_range, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.existsUnique_of_mem_range.h3 : ¬∀ {α β : Type} {f : α → β} {b : β}, b ∈ Set.range f → ∃! a : α, f a = b := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ => 0 : Bool → ℕ) (0) (by
  decide)) (by
  nofun)

-- Function.Injective.existsUnique_of_mem_range, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.existsUnique_of_mem_range.h5 : ¬∀ {α β : Type} {f : α → β}, Function.Injective f → ∀ {b : β}, ∃! a : α, f a = b := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) (2)) (by
  nofun)

-- List.IsChain.imp_of_mem_tail_imp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.imp_of_mem_tail_imp.h4 : ¬∀ {α : Type} {R S : α → α → Prop} {l : List α}, List.IsChain R l → List.IsChain S l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a = b : ℕ → ℕ → Prop) ([0, 1]) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.imp_of_mem_tail_imp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.imp_of_mem_tail_imp.h5 : ¬∀ {α : Type} {R S : α → α → Prop} {l : List α}, (∀ (a b : α), a ∈ l → b ∈ l.tail → R a b → S a b) → List.IsChain S l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0]) (by
  simp)) (by
  decide +kernel)

-- Set.nontrivial_of_preimage, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_of_preimage.h5 : ¬∀ {α β : Type} {f : α → β}, Function.Injective f → ∀ (s : Set β), s.Nontrivial := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) ({n : ℕ | n = 0})) (by
  simp)

-- Subtype.coind_surjective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.coind_surjective.h4 : ¬∀ {α β : Type} {f : α → β} {p : Set β}, Set.SurjOn f Set.univ p → ∀ (a : α), f a ∈ p := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) ({n : ℕ | n = 0}) (by
  simp)) (by
  decide +kernel)

-- List.IsChain.isChain_cons, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.isChain_cons.h4.inst : ¬List.IsChain (fun (a b : ℕ) => a < b) [0, 1, 0] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.isChain_cons.h4.prem0 : ∀ (lne : [1, 0] ≠ []), (fun (a b : ℕ) => a < b) 0 ([1, 0].head lne) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.IsChain.isChain_cons.h4 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {v : α}, (∀ (lne : l ≠ []), R v (l.head lne)) → List.IsChain R (v :: l) := fun hc_h => HypCheckProof.List.IsChain.isChain_cons.h4.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) ([1, 0]) (0) HypCheckProof.List.IsChain.isChain_cons.h4.prem0)

-- List.IsChain.isChain_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.isChain_cons.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {v : α}, List.IsChain R l → List.IsChain R (v :: l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (0) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.suffix, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.suffix.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l l₁ : List α}, List.IsChain R l → List.IsChain R l₁ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([1, 0]) (by
  decide)) (by
  decide +kernel)

-- Set.range_eq_singleton, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.range_eq_singleton.h5 : ¬∀ {α ι : Type} {f : ι → α} [inst : Nonempty ι] {y : α}, Set.range f = {y} := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) _ (0)) (by
  simp)

-- Nat.abs_ofNat, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.abs_ofNat.h5 : ¬∀ {R : Type} [inst : Ring R] [inst_1 : Lattice R] [inst : IsOrderedRing R] (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℤ) (Int.instRing) (instLatticeInt) _ (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.IsRotated.trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsRotated.trans.h4 : ¬∀ {α : Type} {l l' l'' : List α}, l' ~r l'' → l ~r l'' := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.IsRotated.trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsRotated.trans.h5 : ¬∀ {α : Type} {l l' l'' : List α}, l ~r l' → l ~r l'' := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- NNRat.divNat_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNRat.divNat_inj.h4 : ¬∀ {n₁ n₂ d₁ d₂ : ℕ}, d₂ ≠ 0 → (NNRat.divNat n₁ d₁ = NNRat.divNat n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁) := fun hc_h => absurd (@hc_h (0) (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- NNRat.divNat_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNRat.divNat_inj.h5 : ¬∀ {n₁ n₂ d₁ d₂ : ℕ}, d₁ ≠ 0 → (NNRat.divNat n₁ d₁ = NNRat.divNat n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁) := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.findGreatest_is_greatest, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.findGreatest_is_greatest.h4 : ¬∀ {k : ℕ} {P : ℕ → Prop} [inst : DecidablePred P] {n : ℕ}, k ≤ n → ¬P k := fun hc_h => absurd (@hc_h (0) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.findGreatest_is_greatest, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.findGreatest_is_greatest.h5 : ¬∀ {k : ℕ} {P : ℕ → Prop} [inst : DecidablePred P] {n : ℕ}, Nat.findGreatest P n < k → ¬P k := fun hc_h => absurd (@hc_h (2) (fun n => n % 2 = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat (a % 2) 0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.le_findGreatest, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_findGreatest.h4 : ¬∀ {m : ℕ} {P : ℕ → Prop} [inst : DecidablePred P] {n : ℕ}, P m → m ≤ Nat.findGreatest P n := fun hc_h => absurd (@hc_h (2) (fun n => n % 2 = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat (a % 2) 0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Nat.le_findGreatest, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_findGreatest.h5 : ¬∀ {m : ℕ} {P : ℕ → Prop} [inst : DecidablePred P] {n : ℕ}, m ≤ n → m ≤ Nat.findGreatest P n := fun hc_h => absurd (@hc_h (1) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (1) (by
  decide)) (by
  decide +kernel)

-- Fin.val_sub_castLT_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_sub_castLT_of_le.h4 : ¬∀ {n m : ℕ} {a b : Fin m}, b ≤ a → ↑a < n := fun hc_h => absurd (@hc_h (0) (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- Fin.val_sub_castLT_of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_sub_castLT_of_le.h5 : ¬∀ {n m : ℕ} {a b : Fin m}, ↑a < n → b ≤ a := fun hc_h => absurd (@hc_h (1) (2) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Set.Nontrivial.preimage, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.preimage.h4 : ¬∀ {α β : Type} {f : α → β} {s : Set β}, Function.Surjective f → (f ⁻¹' s).Nontrivial := fun hc_h => absurd (@hc_h (Bool) (Bool) (not : Bool → Bool) ({b : Bool | b = Bool.true}) (by
  decide)) (by
  nofun)

-- List.next_prev, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_prev.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α), l.Nodup → ∀ (x : α), x ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (by
  decide) (0)) (by
  decide +kernel)

-- Function.Injective.surjective_of_finite, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.surjective_of_finite.h5 : Not (∀ {α β : Type} [inst : Finite α] {f : α → β} (e : Equiv α β), @Function.Surjective α β f) := fun hc_h => absurd (@hc_h (Bool) (Bool) _ (fun _ => true : Bool → Bool) (@Equiv.mk Bool Bool Bool.not Bool.not
      (@of_decide_eq_true (autoParam (@Function.LeftInverse Bool Bool Bool.not Bool.not) Equiv.left_inv._autoParam)
        (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not)
        (@id
          (@Eq Bool
            (@Decidable.decide (autoParam (@Function.LeftInverse Bool Bool Bool.not Bool.not) Equiv.left_inv._autoParam)
              (@Fintype.decidableLeftInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not))
            Bool.true)
          (@Eq.refl Bool Bool.true)))
      (@of_decide_eq_true (autoParam (@Function.RightInverse Bool Bool Bool.not Bool.not) Equiv.right_inv._autoParam)
        (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not)
        (@id
          (@Eq Bool
            (@Decidable.decide (autoParam (@Function.RightInverse Bool Bool Bool.not Bool.not) Equiv.right_inv._autoParam)
              (@Fintype.decidableRightInverseFintype Bool Bool instDecidableEqBool Bool.fintype Bool.not Bool.not))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- List.next_getElem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_getElem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α), l.Nodup → ∀ (i : ℕ), i < l.length := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (by
  decide) (0)) (by
  decide +kernel)

-- List.Duplicate.mono_sublist, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Duplicate.mono_sublist.h4 : ¬∀ {α : Type} {l : List α} {x : α} {l' : List α}, l.Sublist l' → List.Duplicate x l' := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) ([]) (by
  decide)) (by
  decide +kernel)

-- Int.cast_div, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.cast_div.h4 : Not
      (∀ {α : Type} [inst : DivisionRing α] {m n : Int},
        @Ne α (@Int.cast α (@AddGroupWithOne.toIntCast α (@Ring.toAddGroupWithOne α (@DivisionRing.toRing α inst))) n)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@MulZeroClass.toZero α
                  (@instMulZeroClassOfSemiring α (@Ring.toSemiring α (@DivisionRing.toRing α inst)))))) →
          @Eq α
            (@Int.cast α (@AddGroupWithOne.toIntCast α (@Ring.toAddGroupWithOne α (@DivisionRing.toRing α inst)))
              (@HDiv.hDiv Int Int Int (@instHDiv Int Int.instDiv) m n))
            (@HDiv.hDiv α α α (@instHDiv α (@DivInvMonoid.toDiv α (@DivisionRing.toDivInvMonoid α inst)))
              (@Int.cast α (@AddGroupWithOne.toIntCast α (@Ring.toAddGroupWithOne α (@DivisionRing.toRing α inst))) m)
              (@Int.cast α (@AddGroupWithOne.toIntCast α (@Ring.toAddGroupWithOne α (@DivisionRing.toRing α inst))) n))) := fun hc_h => absurd (@hc_h (Rat) (Rat.instDivisionRing) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.trans.h4 : ¬∀ {n a b c : ℤ}, b ≡ c [ZMOD n] → a ≡ c [ZMOD n] := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.trans.h5 : ¬∀ {n a b c : ℤ}, a ≡ b [ZMOD n] → a ≡ c [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.pairwise_insertionSort, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwise_insertionSort.h3 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] [inst_1 : IsTrans α r] (l : List α),
        List.Pairwise r (List.insertionSort r l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ ([0, 0])) (by
  decide +kernel)

-- List.Nodup.getEquivOfForallMemList_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.getEquivOfForallMemList_apply.h4 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α), l.Nodup → ∀ (i : Fin l.length) (x : α), x ∈ l := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) ([Bool.false]) (by
  decide) (0)) (by
  decide +kernel)

-- Set.Infinite.image, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.image.h5 : ¬∀ {α β : Type} {s : Set α} {f : α → β}, Set.InjOn f s → (f '' s).Infinite := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Nat.digits_append_zeroes_append_digits, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_append_zeroes_append_digits.h4 : ¬∀ {b k m n : ℕ},
        0 < m → b.digits n ++ List.replicate k 0 ++ b.digits m = b.digits (n + b ^ ((b.digits n).length + k) * m) := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.digits_append_zeroes_append_digits, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_append_zeroes_append_digits.h5 : ¬∀ {b k m n : ℕ},
        1 < b → b.digits n ++ List.replicate k 0 ++ b.digits m = b.digits (n + b ^ ((b.digits n).length + k) * m) := fun hc_h => absurd (@hc_h (2) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.exists_eq_pow_of_pow_eq_pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_eq_pow_of_pow_eq_pow.h4 : ¬∀ {a b m n : ℕ}, a ^ m = b ^ n → ∃ (c : ℕ), a = c ^ (n / m.gcd n) ∧ b = c ^ (m / m.gcd n) := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Nat.exists_eq_pow_of_pow_eq_pow, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_eq_pow_of_pow_eq_pow.h5 : ¬∀ {a b m n : ℕ}, m ≠ 0 ∨ n ≠ 0 → ∃ (c : ℕ), a = c ^ (n / m.gcd n) ∧ b = c ^ (m / m.gcd n) := fun hc_h => absurd (@hc_h (0) (0) (0) (1) (by
  decide)) (by
  simp)

-- Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow.h4 : ¬∀ {a b m n : ℕ}, a ^ m = b ^ n → ∃ (c : ℕ), a = c ^ n ∧ b = c ^ m := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow.h5 : ¬∀ {a b m n : ℕ}, m.Coprime n → ∃ (c : ℕ), a = c ^ n ∧ b = c ^ m := fun hc_h => absurd (@hc_h (0) (0) (0) (1) (by
  decide)) (by
  simp)

-- Nat.factorization_choose', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose'.h4 : ¬∀ {p n k b : ℕ},
        Nat.log p (n + k) < b →
          ((n + k).choose k).factorization p = {i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i}.card := fun hc_h => absurd (@hc_h (0) (0) (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_choose', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose'.h5 : ¬∀ {p n k b : ℕ},
        Nat.Prime p → ((n + k).choose k).factorization p = {i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i}.card := fun hc_h => absurd (@hc_h (2) (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Sym2.Rel.trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.Rel.trans.h4 : ¬∀ {α : Type} {x y z : α × α}, Sym2.Rel α y z → Sym2.Rel α x z := fun hc_h => absurd (@hc_h (ℕ) ((0, 1)) ((0, 0)) ((0, 0)) (by
  decide)) (by
  decide +kernel)

-- Sym2.Rel.trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.Rel.trans.h5 : ¬∀ {α : Type} {x y z : α × α}, Sym2.Rel α x y → Sym2.Rel α x z := fun hc_h => absurd (@hc_h (ℕ) ((0, 0)) ((0, 0)) ((0, 1)) (by
  decide)) (by
  decide +kernel)

-- List.mem_dropLast_of_mem_of_ne_getLastD, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_dropLast_of_mem_of_ne_getLastD.h4 : ¬∀ {α : Type} {l : List α} {a d : α}, a ≠ l.getLastD d → a ∈ l.dropLast := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.mem_dropLast_of_mem_of_ne_getLastD, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_dropLast_of_mem_of_ne_getLastD.h5 : ¬∀ {α : Type} {l : List α} {a : α} {d : α}, a ∈ l → a ∈ l.dropLast := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- List.length_erase_add_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_erase_add_one.h2 : ¬∀ {α : Type} [inst : BEq α] {a : α} {l : List α}, a ∈ l → (l.erase a).length + 1 = l.length := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a != b⟩ : BEq ℕ) (0) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.length_erase_add_one, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_erase_add_one.h5 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {a : α} {l : List α}, (l.erase a).length + 1 = l.length := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ (0) ([])) (by
  decide +kernel)

-- Nat.count_strict_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_strict_mono.h4 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {m n : ℕ}, m < n → Nat.count p m < Nat.count p n := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (1) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.count_strict_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_strict_mono.h5 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {m n : ℕ}, p m → Nat.count p m < Nat.count p n := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Set.mem_coe_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_coe_of_mem.h4 : ¬∀ {α : Type} {β : Set α} {γ : Set ↑β} {a : α}, a ∈ β := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (∅) (1)) (by
  decide +kernel)

-- Set.mem_coe_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_coe_of_mem.h5 : Not
      (∀ {α : Type} {β : Set α} {γ : Set (@Set.Elem α β)} {a : α},
        @Membership.mem α (Set α) (@Set.instMembership α) β a →
          @Membership.mem α (Set α) (@Set.instMembership α)
            (@Bind.bind Set (@Monad.toBind Set (@AlternativeMonad.toMonad Set Set.monad)) (@Set.Elem α β) α γ
              fun (a : @Set.Elem α β) =>
              @Pure.pure Set (@Applicative.toPure Set (@Monad.toApplicative Set (@AlternativeMonad.toMonad Set Set.monad)))
                α (@Subtype.val α (fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) β x) a))
            a) := fun hc_h => absurd (@hc_h (Nat) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@EmptyCollection.emptyCollection
      (Set
        (@Set.Elem Nat
          (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@Set.instEmptyCollection
        (@Set.Elem Nat
          (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  norm_num)

-- Set.Subsingleton.prod, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subsingleton.prod.h4 : ¬∀ {α β : Type} {s : Set α} {t : Set β}, t.Subsingleton → (s ×ˢ t).Subsingleton := fun hc_h => absurd (@hc_h (Bool) (Bool) ({x : Bool | True}) ({b : Bool | b = Bool.true}) (by
  decide)) (by
  decide +kernel)

-- Set.Subsingleton.prod, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subsingleton.prod.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β}, s.Subsingleton → (s ×ˢ t).Subsingleton := fun hc_h => absurd (@hc_h (Bool) (Bool) ({b : Bool | b = Bool.true}) ({x : Bool | True}) (by
  decide)) (by
  decide +kernel)

-- Set.ssubset_of_ssubset_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ssubset_of_ssubset_of_subset.h4 : ¬∀ {α : Type} {s₁ s₂ s₃ : Set α}, s₂ ⊆ s₃ → s₁ ⊂ s₃ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Set.ssubset_of_ssubset_of_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ssubset_of_ssubset_of_subset.h5 : ¬∀ {α : Type} {s₁ s₂ s₃ : Set α}, s₁ ⊂ s₂ → s₁ ⊂ s₃ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | True}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Nat.one_div_cast_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.one_div_cast_pos.h5 : Not
      (∀ {α : Type} [inst : Semifield α] [inst_1 : LinearOrder α]
        [inst_2 :
          @IsStrictOrderedRing α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))
            (@SemilatticeInf.toPartialOrder α
              (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))]
        {n : Nat},
        @LT.lt α
          (@Preorder.toLT α
            (@PartialOrder.toPreorder α
              (@SemilatticeInf.toPartialOrder α
                (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
          (@OfNat.ofNat α (nat_lit 0)
            (@Zero.toOfNat0 α
              (@MulZeroClass.toZero α
                (@instMulZeroClassOfSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))
          (@HDiv.hDiv α α α
            (@instHDiv α
              (@DivInvMonoid.toDiv α
                (@GroupWithZero.toDivInvMonoid α
                  (@DivisionSemiring.toGroupWithZero α (@Semifield.toDivisionSemiring α inst)))))
            (@OfNat.ofNat α (nat_lit 1)
              (@One.toOfNat1 α
                (@AddMonoidWithOne.toOne α
                  (@AddCommMonoidWithOne.toAddMonoidWithOne α
                    (@NonAssocSemiring.toAddCommMonoidWithOne α
                      (@Semiring.toNonAssocSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))))
            (@Nat.cast α
              (@AddMonoidWithOne.toNatCast α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α
                    (@Semiring.toNonAssocSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))
              n))) := fun hc_h => absurd (@hc_h (Rat) (@Field.toSemifield Rat Rat.instField) (Rat.linearOrder) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- List.idxOf_of_notMem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_of_notMem.h2 : ¬∀ {α : Type} [inst : BEq α] {l : List α} {a : α}, a ∉ l → List.idxOf a l = l.length := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) ([0]) (1) (by
  decide)) (by
  decide +kernel)

-- List.idxOf_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_of_notMem.h5 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l : List α} {a : α}, List.idxOf a l = l.length := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ ([0]) (0)) (by
  decide +kernel)

-- List.ext_getElem!, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.ext_getElem!.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : Inhabited α], (∀ (n : ℕ), l₁[n]! = l₂[n]!) → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (instInhabitedNat) (by
  simp)) (by
  decide +kernel)

-- List.ext_getElem!, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.ext_getElem!.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : Inhabited α], l₁.length = l₂.length → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([1]) (instInhabitedNat) (by
  decide)) (by
  decide +kernel)

-- List.Sublist.sublistForall₂, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.sublistForall₂.h4 : ¬∀ {α : Type} {Rₐ : α → α → Prop} {l₁ l₂ : List α} [inst : Std.Refl Rₐ], List.SublistForall₂ Rₐ l₁ l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ([0]) ([]) _) (by
  nofun)

-- List.Sublist.sublistForall₂, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.sublistForall₂.h5 : ¬∀ {α : Type} {Rₐ : α → α → Prop} {l₁ l₂ : List α}, l₁.Sublist l₂ → List.SublistForall₂ Rₐ l₁ l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) ([0]) (by
  decide)) (by
  nofun)

-- Function.Injective.codRestrict, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.codRestrict.h4 : ¬∀ {α ι : Type} {f : ι → α} {s : Set α}, Function.Injective f → ∀ (x : ι), f x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun b => if b then 1 else 0 : Bool → ℕ) ({n : ℕ | n = 0}) (by
  decide)) (by
  decide +kernel)

-- Function.Injective.codRestrict, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.codRestrict.h5 : ¬∀ {α ι : Type} {f : ι → α} {s : Set α} (h : ∀ (x : ι), f x ∈ s), Function.Injective (Set.codRestrict f s h) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0}) hc_k0) (by
  norm_num)

-- Function.Injective.nonempty_apply_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.nonempty_apply_iff.h3 : ¬∀ {α β : Type} {f : Set α → Set β}, f ∅ = ∅ → ∀ {s : Set α}, (f s).Nonempty ↔ s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : Set ℕ) => {x : ℕ | False}) (by
  rfl) ({n : ℕ | n = 0})) (by
  simp)

-- List.insertIdx_eraseIdx_getElem_perm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.insertIdx_eraseIdx_getElem_perm.h4 : ¬∀ {α : Type} {l : List α} {m n : ℕ}, n ≤ (l.eraseIdx m).length → m < l.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- List.insertIdx_eraseIdx_getElem_perm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.insertIdx_eraseIdx_getElem_perm.h5 : ¬∀ {α : Type} {l : List α} {m n : ℕ} (hm : m < l.length), ((l.eraseIdx m).insertIdx n l[m]).Perm l := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) ([0]) (0) (1) hc_k0) (by
  decide +kernel)

-- Set.mem_of_eq_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_of_eq_of_mem.h4 : ¬∀ {α : Type} {x y : α} {s : Set α}, y ∈ s → x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (1) (0) ({n : ℕ | n = 0}) (by
  decide)) (by
  decide +kernel)

-- Set.mem_of_eq_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_of_eq_of_mem.h5 : ¬∀ {α : Type} {x y : α} {s : Set α}, x = y → x ∈ s := fun hc_h => absurd (@hc_h (ℕ) _ (1) ({n : ℕ | n = 0}) rfl) (by
  decide +kernel)

-- List.IsChain.length_le_length_destutter_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.length_le_length_destutter_ne.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : DecidableEq α],
        List.IsChain (fun (x1 x2 : α) => x1 ≠ x2) l₁ → l₁.length ≤ (List.destutter (fun (x1 x2 : α) => x1 ≠ x2) l₂).length := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (instDecidableEqNat) (by
  decide)) (by
  decide +kernel)

-- Set.mem_sUnion_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_sUnion_of_mem.h5 : ¬∀ {α : Type} {x : α} {t : Set α} {S : Set (Set α)}, x ∈ t → x ∈ ⋃₀ S := fun hc_h => absurd (@hc_h (ℕ) (0) ({n : ℕ | n = 0}) (∅) (by
  decide)) (by
  simp)

-- Set.inter_empty_of_inter_sUnion_empty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_empty_of_inter_sUnion_empty.h4 : ¬∀ {α : Type} {s t : Set α} {S : Set (Set α)}, s ∩ ⋃₀ S = ∅ → s ∩ t = ∅ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (∅) (by
  simp)) (by
  simp)

-- Set.inter_empty_of_inter_sUnion_empty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_empty_of_inter_sUnion_empty.h5 : ¬∀ {α : Type} {s t : Set α} {S : Set (Set α)}, t ∈ S → s ∩ t = ∅ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (⊤) (by
  simp)) (by
  simp)

-- Set.subset_inter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_inter.h4 : ¬∀ {α : Type} {s t r : Set α}, r ⊆ t → r ⊆ s ∩ t := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Set.subset_inter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_inter.h5 : ¬∀ {α : Type} {s t r : Set α}, r ⊆ s → r ⊆ s ∩ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Set.mem_of_mem_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_of_mem_of_subset.h4 : ¬∀ {α : Type} {x : α} {s t : Set α}, s ⊆ t → x ∈ t := fun hc_h => absurd (@hc_h (ℕ) (1) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  decide +kernel)

-- Set.mem_of_mem_of_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_of_mem_of_subset.h5 : ¬∀ {α : Type} {x : α} {s t : Set α}, x ∈ s → x ∈ t := fun hc_h => absurd (@hc_h (ℕ) (0) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  decide)) (by
  decide +kernel)

-- List.tfae_append_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.tfae_append_of_mem.h4 : ¬∀ {a b : Prop} {l₁ l₂ : List Prop}, b ∈ l₂ → ((l₁ ++ l₂).TFAE ↔ (a ↔ b) ∧ l₁.TFAE ∧ l₂.TFAE) := fun hc_h => absurd (@hc_h (False) (True) ([]) ([True]) (by
  simp)) (by
  simp)

-- List.tfae_append_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.tfae_append_of_mem.h5 : ¬∀ {a b : Prop} {l₁ l₂ : List Prop}, a ∈ l₁ → ((l₁ ++ l₂).TFAE ↔ (a ↔ b) ∧ l₁.TFAE ∧ l₂.TFAE) := fun hc_h => absurd (@hc_h (True) (False) ([True]) ([]) (by
  simp)) (by
  simp)

-- Set.Nonempty.sups, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.sups.h4 : Not
      (∀ {α : Type} [inst : SemilatticeSup α] {s t : Set α},
        @Set.Nonempty α t → @Set.Nonempty α (@HasSups.sups (Set α) (@Set.hasSups α inst) s t)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Set.ofPred Nat fun (x : Nat) => False) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  simp)) (by
  simp)

-- Set.Nonempty.sups, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.sups.h5 : Not
      (∀ {α : Type} [inst : SemilatticeSup α] {s t : Set α},
        @Set.Nonempty α s → @Set.Nonempty α (@HasSups.sups (Set α) (@Set.hasSups α inst) s t)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (x : Nat) => False) (by
  simp)) (by
  simp)

-- Fin.lt_of_injective_of_notMem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.lt_of_injective_of_notMem.h3 : ¬∀ {m n : ℕ} (f : Fin m → Fin n) {b : Fin n}, b ∉ Set.range f → m < n := fun hc_h => absurd (@hc_h (2) (2) (fun (a : Fin 2) => (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.lt_of_injective_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.lt_of_injective_of_notMem.h5 : ¬∀ {m n : ℕ} (f : Fin m → Fin n), Function.Injective f → ∀ {b : Fin n}, m < n := fun hc_h => absurd (@hc_h (1) (1) (fun (a : Fin 1) => (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Nodup.filterMap, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.filterMap.h4 : ¬∀ {α β : Type} {l : List α} {f : α → Option β}, l.Nodup → (List.filterMap f l).Nodup := fun hc_h => absurd (@hc_h (Bool) (ℕ) ([Bool.false, Bool.true]) (fun (a : Bool) => Option.some 0) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.filterMap.h5 : ¬∀ {α β : Type} {l : List α} {f : α → Option β},
        (∀ (a a' : α), ∀ b ∈ f a, b ∈ f a' → a = a') → (List.filterMap f l).Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0, 0]) (some : ℕ → Option ℕ) (by
  simp)) (by
  decide +kernel)

-- List.Nodup.map, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.map.h4 : ¬∀ {α β : Type} {l : List α} {f : α → β}, l.Nodup → (List.map f l).Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0, 1]) (fun _ => 0 : ℕ → ℕ) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.map.h5 : ¬∀ {α β : Type} {l : List α} {f : α → β}, Function.Injective f → (List.map f l).Nodup := fun hc_h => absurd (@hc_h (Bool) (ℕ) ([Bool.false, Bool.false]) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.insert.h4 : ¬∀ {α : Type} {l : List α} {a : α} [inst : BEq α], l.Nodup → (List.insert a l).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (⟨fun a b => a != b⟩ : BEq ℕ) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.insert, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.insert.h5 : ¬∀ {α : Type} {l : List α} {a : α} [inst : BEq α] [inst_1 : LawfulBEq α], (List.insert a l).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (0) (instBEqOfDecidableEq) _) (by
  decide +kernel)

-- Set.union_congr_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.union_congr_left.h4 : ¬∀ {α : Type} {s t u : Set α}, u ⊆ s ∪ t → s ∪ t = s ∪ u := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) (by
  simp)) (by
  simp)

-- Set.union_congr_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.union_congr_left.h5 : ¬∀ {α : Type} {s t u : Set α}, t ⊆ s ∪ u → s ∪ t = s ∪ u := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | True}) (by
  simp)) (by
  simp)

-- List.minimum_of_length_pos_le_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minimum_of_length_pos_le_of_mem.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {a : α} (w : 0 < l.length), List.minimum_of_length_pos w ≤ a := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (Nat.instLinearOrder) ([1]) (0) hc_k0) (by
  decide +kernel)

-- List.minimum_of_length_pos_le_of_mem, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.minimum_of_length_pos_le_of_mem.h5.der.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] {l : List α} {a : α}, a ∈ l → 0 < l.length := by
  (intros; grind)
theorem HypCheckProof.List.minimum_of_length_pos_le_of_mem.h5.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] {l : List α} {a : α} (h : a ∈ l),
      List.minimum_of_length_pos (HypCheckProof.List.minimum_of_length_pos_le_of_mem.h5.der h) ≤ a := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @List.minimum_of_length_pos_le_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.List.minimum_of_length_pos_le_of_mem.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- List.getElem_le_maximum_of_length_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_le_maximum_of_length_pos.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {i : ℕ}, i < l.length := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([]) (0)) (by
  decide +kernel)

-- List.getElem_le_maximum_of_length_pos, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.getElem_le_maximum_of_length_pos.h5.der.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] {l : List α} {i : ℕ}, i < l.length → 0 < l.length := by
  (intros; lia)
theorem HypCheckProof.List.getElem_le_maximum_of_length_pos.h5.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] {l : List α} {i : ℕ} (w : i < l.length),
      l[i] ≤ List.maximum_of_length_pos (HypCheckProof.List.getElem_le_maximum_of_length_pos.h5.der w) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @List.getElem_le_maximum_of_length_pos hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.List.getElem_le_maximum_of_length_pos.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- List.Nodup.sdiff_eq_filter, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.sdiff_eq_filter.h2 : ¬∀ {α : Type} [inst : BEq α] {l₁ : List α} {l₂ : List α}, l₁.Nodup → LawfulBEq α := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) ([]) ([]) (by
  decide)) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_beq (a := (0 : ℕ)) (b := (1 : ℕ))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.foldl_eq_foldr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldl_eq_foldr.h4 : ¬∀ {α : Type} {l : List α} {a : α} {f : α → α → α} [inst : Std.Associative f], List.foldl f a l = List.foldr f a l := fun hc_h => absurd (@hc_h (ℕ) ([0]) (1) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done)))) (by
  decide +kernel)

-- List.get_idxOf, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.get_idxOf.h2 : ¬∀ {α : Type} [inst : BEq α] {l : List α}, l.Nodup → ∀ (i : Fin l.length), List.idxOf (l.get i) l = ↑i := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a != b⟩ : BEq ℕ) ([0]) (by
  decide) (0)) (by
  decide +kernel)

-- List.get_idxOf, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.get_idxOf.h4 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l : List α} (i : Fin l.length), List.idxOf (l.get i) l = ↑i := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ ([0, 0]) (1)) (by
  decide +kernel)

-- List.Nodup.union, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.union.h3 : ¬∀ {α : Type} {l₂ : List α} [inst : BEq α] (l₁ : List α), l₂.Nodup → (l₁ ∪ l₂).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0]) (⟨fun a b => a != b⟩ : BEq ℕ) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.union, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.union.h5 : ¬∀ {α : Type} {l₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] (l₁ : List α), (l₁ ∪ l₂).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (instBEqOfDecidableEq) _ ([])) (by
  decide +kernel)

-- set_coe_cast, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.set_coe_cast.h4.der.{u} : ∀ {α : Type u} {s t : Set α}, @Eq (Set α) s t → ∀ (x : @Set.Elem α s), @Eq (Type u) (@Set.Elem α s) (@Set.Elem α t) := by
  (intros; solve_by_elim)
theorem HypCheckProof.set_coe_cast.h4.{u} : ∀ {α : Type u} {s t : Set α} (H' : @Eq (Set α) s t) (x : @Set.Elem α s),
      @Eq (@Set.Elem α t) (@cast (@Set.Elem α s) (@Set.Elem α t) (@HypCheckProof.set_coe_cast.h4.der α s t H' x) x)
        (@Subtype.mk α (fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) t x)
          (@Subtype.val α (fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) s x) x)
          (@Eq.rec (Set α) s
            (fun (x_1 : Set α) (h : @Eq (Set α) s x_1) =>
              @Membership.mem α (Set α) (@Set.instMembership α) x_1
                (@Subtype.val α (fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) s x) x))
            (@Subtype.property α (fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) s x) x) t H')) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @set_coe_cast hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.set_coe_cast.h4.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4) hc_x4

-- List.splitLengths_length_getElem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.splitLengths_length_getElem.h3 : ¬∀ {α : Type} (l : List α) (sz : List ℕ) (i : ℕ) (hi : i < (sz.splitLengths l).length),
        List.length (GetElem.getElem (sz.splitLengths l) i hi) = GetElem.getElem sz i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) ([]) ([1]) (0) hc_k0) (by
  decide +kernel)

-- List.splitLengths_length_getElem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.splitLengths_length_getElem.h5 : ¬∀ {α : Type} (l : List α) (sz : List ℕ), sz.sum ≤ l.length → ∀ (i : ℕ), i < (sz.splitLengths l).length := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (by
  decide) (0)) (by
  decide +kernel)

-- List.Nodup.take_eq_filter_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.take_eq_filter_mem.h2 : ¬∀ {α : Type} [inst : BEq α] {l : List α} {n : ℕ},
        l.Nodup → List.take n l = List.filter (fun (a : α) => List.elem a (List.take n l)) l := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) ([0, 1]) (1) (by
  decide)) (by
  decide +kernel)

-- IsUnit.natCast_factorial_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsUnit.natCast_factorial_of_lt.h3 : Not
      (∀ {A : Type} [inst : Semiring A] {n m : Nat},
        @LT.lt Nat instLTNat m n →
          @IsUnit A (@Semiring.toMonoid A inst)
            (@Nat.cast A
              (@AddMonoidWithOne.toNatCast A
                (@AddCommMonoidWithOne.toAddMonoidWithOne A
                  (@NonAssocSemiring.toAddCommMonoidWithOne A (@Semiring.toNonAssocSemiring A inst))))
              m.factorial)) := fun hc_h => absurd (@hc_h (Nat) (Nat.instSemiring) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- IsUnit.natCast_factorial_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsUnit.natCast_factorial_of_lt.h5 : Not
      (∀ {A : Type} [inst : Semiring A] {n : Nat},
        @IsUnit A (@Semiring.toMonoid A inst)
            (@Nat.cast A
              (@AddMonoidWithOne.toNatCast A
                (@AddCommMonoidWithOne.toAddMonoidWithOne A
                  (@NonAssocSemiring.toAddCommMonoidWithOne A (@Semiring.toNonAssocSemiring A inst))))
              (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).factorial) →
          ∀ {m : Nat},
            @IsUnit A (@Semiring.toMonoid A inst)
              (@Nat.cast A
                (@AddMonoidWithOne.toNatCast A
                  (@AddCommMonoidWithOne.toAddMonoidWithOne A
                    (@NonAssocSemiring.toAddCommMonoidWithOne A (@Semiring.toNonAssocSemiring A inst))))
                m.factorial)) := fun hc_h => absurd (@hc_h (Nat) (Nat.instSemiring) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (by
  decide +kernel)

-- Nat.castChoose_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.castChoose_eq.h4 : Not
      (∀ {A : Type} [inst : CommSemiring A] {m : Nat} {k : Prod Nat Nat},
        @Membership.mem (Prod Nat Nat) (Finset (Prod Nat Nat))
            (@SetLike.instMembership (Finset (Prod Nat Nat)) (Prod Nat Nat) (@Finset.instSetLike (Prod Nat Nat)))
            (@Finset.HasAntidiagonal.antidiagonal Nat instAddNat Finset.Nat.instHasAntidiagonal m) k →
          @Eq A
            (@Nat.cast A
              (@AddMonoidWithOne.toNatCast A
                (@AddCommMonoidWithOne.toAddMonoidWithOne A
                  (@NonAssocSemiring.toAddCommMonoidWithOne A
                    (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A inst)))))
              (m.choose (@Prod.fst Nat Nat k)))
            (@HMul.hMul A A A (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@CommSemiring.toSemiring A inst))))
              (@HMul.hMul A A A
                (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@CommSemiring.toSemiring A inst))))
                (@Nat.cast A
                  (@AddMonoidWithOne.toNatCast A
                    (@AddCommMonoidWithOne.toAddMonoidWithOne A
                      (@NonAssocSemiring.toAddCommMonoidWithOne A
                        (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A inst)))))
                  m.factorial)
                (@Ring.inverse A (@Semiring.toMonoidWithZero A (@CommSemiring.toSemiring A inst))
                  (@Nat.cast A
                    (@AddMonoidWithOne.toNatCast A
                      (@AddCommMonoidWithOne.toAddMonoidWithOne A
                        (@NonAssocSemiring.toAddCommMonoidWithOne A
                          (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A inst)))))
                    (@Prod.fst Nat Nat k).factorial)))
              (@Ring.inverse A (@Semiring.toMonoidWithZero A (@CommSemiring.toSemiring A inst))
                (@Nat.cast A
                  (@AddMonoidWithOne.toNatCast A
                    (@AddCommMonoidWithOne.toAddMonoidWithOne A
                      (@NonAssocSemiring.toAddCommMonoidWithOne A
                        (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A inst)))))
                  (@Prod.snd Nat Nat k).factorial)))) := fun hc_h => absurd (@hc_h (Nat) (Nat.instCommSemiring) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide)) (by
  simp)

-- Nat.castChoose_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.castChoose_eq.h5 : Not
      (∀ {A : Type} [inst : CommSemiring A] {m : Nat} {k : Prod Nat Nat},
        @IsUnit A (@Semiring.toMonoid A (@CommSemiring.toSemiring A inst))
            (@Nat.cast A
              (@AddMonoidWithOne.toNatCast A
                (@AddCommMonoidWithOne.toAddMonoidWithOne A
                  (@NonAssocSemiring.toAddCommMonoidWithOne A
                    (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A inst)))))
              m.factorial) →
          @Eq A
            (@Nat.cast A
              (@AddMonoidWithOne.toNatCast A
                (@AddCommMonoidWithOne.toAddMonoidWithOne A
                  (@NonAssocSemiring.toAddCommMonoidWithOne A
                    (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A inst)))))
              (m.choose (@Prod.fst Nat Nat k)))
            (@HMul.hMul A A A (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@CommSemiring.toSemiring A inst))))
              (@HMul.hMul A A A
                (@instHMul A (@Distrib.toMul A (@instDistribOfSemiring A (@CommSemiring.toSemiring A inst))))
                (@Nat.cast A
                  (@AddMonoidWithOne.toNatCast A
                    (@AddCommMonoidWithOne.toAddMonoidWithOne A
                      (@NonAssocSemiring.toAddCommMonoidWithOne A
                        (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A inst)))))
                  m.factorial)
                (@Ring.inverse A (@Semiring.toMonoidWithZero A (@CommSemiring.toSemiring A inst))
                  (@Nat.cast A
                    (@AddMonoidWithOne.toNatCast A
                      (@AddCommMonoidWithOne.toAddMonoidWithOne A
                        (@NonAssocSemiring.toAddCommMonoidWithOne A
                          (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A inst)))))
                    (@Prod.fst Nat Nat k).factorial)))
              (@Ring.inverse A (@Semiring.toMonoidWithZero A (@CommSemiring.toSemiring A inst))
                (@Nat.cast A
                  (@AddMonoidWithOne.toNatCast A
                    (@AddCommMonoidWithOne.toAddMonoidWithOne A
                      (@NonAssocSemiring.toAddCommMonoidWithOne A
                        (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A inst)))))
                  (@Prod.snd Nat Nat k).factorial)))) := fun hc_h => absurd (@hc_h (Nat) (Nat.instCommSemiring) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide)) (by
  simp)

-- Ordnode.Sized.node', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.node'.h4 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α}, r.Sized → (l.node' x r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.nil) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Sized.node', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.node'.h5 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α}, l.Sized → (l.node' x r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Sized.rotateR, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.rotateR.h5 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α}, l.Sized → (l.rotateR x r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.All.imp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.All.imp.h3 : ¬∀ {α : Type} {P Q : α → Prop} {t : Ordnode α}, Ordnode.All P t → Ordnode.All Q t := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  decide)) (by
  decide +kernel)

-- Ordnode.All.imp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.All.imp.h5 : ¬∀ {α : Type} {P Q : α → Prop}, (∀ (a : α), P a → Q a) → ∀ {t : Ordnode α}, Ordnode.All Q t := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (by
  simp) (Ordnode.node 0 Ordnode.nil 1 Ordnode.nil)) (by
  decide +kernel)

-- Ordnode.findMin'_all, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.findMin'_all.h4 : ¬∀ {α : Type} {P : α → Prop} (t : Ordnode α) (x : α), P x → P (t.findMin' x) := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (Ordnode.node 0 Ordnode.nil 1 Ordnode.nil) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Ordnode.findMin'_all, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.findMin'_all.h5 : ¬∀ {α : Type} {P : α → Prop} (t : Ordnode α) (x : α), Ordnode.All P t → P (t.findMin' x) := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (Ordnode.nil) (1) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Any.imp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Any.imp.h3 : ¬∀ {α : Type} {P Q : α → Prop} {t : Ordnode α}, Ordnode.Any P t → Ordnode.Any Q t := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Any.imp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Any.imp.h5 : ¬∀ {α : Type} {P Q : α → Prop}, (∀ (a : α), P a → Q a) → ∀ {t : Ordnode α}, Ordnode.Any Q t := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (by
  simp) (Ordnode.nil)) (by
  decide +kernel)

-- Set.inclusion_comp_inclusion, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inclusion_comp_inclusion.h4 : ¬∀ {α : Type} {s t u : Set α}, t ⊆ u → s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.inclusion_comp_inclusion, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inclusion_comp_inclusion.h5 : ¬∀ {α : Type} {s t u : Set α}, s ⊆ t → t ⊆ u := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  rfl)) (by
  simp)

-- Set.inclusion_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inclusion_mk.h3 : ¬∀ {α : Type} {s t : Set α}, ∀ a ∈ s, s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (0) (by
  decide)) (by
  simp)

-- Set.inclusion_mk, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inclusion_mk.h5 : ¬∀ {α : Type} {s t : Set α} {h : s ⊆ t} (a : α), a ∈ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl) (1)) (by
  decide +kernel)

-- Disjoint.union_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.union_left.h4 : ¬∀ {α : Type} {s t u : Set α}, Disjoint t u → Disjoint (s ∪ t) u := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Disjoint.union_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.union_left.h5 : ¬∀ {α : Type} {s t u : Set α}, Disjoint s u → Disjoint (s ∪ t) u := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Prod.trichotomous, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.trichotomous.h4 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop} [inst : Std.Trichotomous s], Std.Trichotomous (Prod.Lex r s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.trichotomous ((0, 0) : ℕ × ℕ) ((1, 0) : ℕ × ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Prod.trichotomous, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.trichotomous.h5 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop} [inst : Std.Trichotomous r], Std.Trichotomous (Prod.Lex r s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a = b : ℕ → ℕ → Prop) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.trichotomous ((0, 0) : ℕ × ℕ) ((0, 1) : ℕ × ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Disjoint.subset_right_of_subset_union, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.subset_right_of_subset_union.h4 : ¬∀ {α : Type} {s t u : Set α}, Disjoint s t → s ⊆ u := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp)) (by
  simp)

-- Disjoint.subset_right_of_subset_union, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.subset_right_of_subset_union.h5 : ¬∀ {α : Type} {s t u : Set α}, s ⊆ t ∪ u → s ⊆ u := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Disjoint.union_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.union_right.h4 : ¬∀ {α : Type} {s t u : Set α}, Disjoint s u → Disjoint s (t ∪ u) := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Disjoint.union_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.union_right.h5 : ¬∀ {α : Type} {s t u : Set α}, Disjoint s t → Disjoint s (t ∪ u) := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- List.find?_eq_find?_of_perm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.find?_eq_find?_of_perm.h4 : ¬∀ {α : Type} {p : α → Bool} {l₁ l₂ : List α},
        {x : α | x ∈ l₁ ∧ p x = Bool.true}.Subsingleton → List.find? p l₁ = List.find? p l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) ([]) ([0]) (by
  simp)) (by
  decide +kernel)

-- EReal.div_mul_cancel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_mul_cancel.h2 : ¬∀ {a b : EReal}, b ≠ ⊤ → b ≠ 0 → a / b * b = a := fun hc_h => absurd (@hc_h (1) (⊥) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.div_mul_cancel, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_mul_cancel.h3 : ¬∀ {a b : EReal}, b ≠ ⊥ → b ≠ 0 → a / b * b = a := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.div_mul_cancel, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_mul_cancel.h4 : ¬∀ {a b : EReal}, b ≠ ⊥ → b ≠ ⊤ → a / b * b = a := fun hc_h => absurd (@hc_h (1) (0) (by
  decide) (by
  decide)) (by
  simp)

-- Nat.eq_of_factorization_eq', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_of_factorization_eq'.h2 : ¬∀ {a b : ℕ}, b ≠ 0 → a.factorization = b.factorization → a = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide) (by
  decide +kernel)) (by
  decide +kernel)

-- Nat.eq_of_factorization_eq', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_of_factorization_eq'.h3 : ¬∀ {a b : ℕ}, a ≠ 0 → a.factorization = b.factorization → a = b := fun hc_h => absurd (@hc_h (1) (0) (by
  decide) (by
  decide +kernel)) (by
  decide +kernel)

-- Nat.eq_of_factorization_eq', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_of_factorization_eq'.h4 : ¬∀ {a b : ℕ}, a ≠ 0 → b ≠ 0 → a = b := fun hc_h => absurd (@hc_h (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.eq_of_factorization_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_of_factorization_eq.h2 : ¬∀ {a b : ℕ}, b ≠ 0 → (∀ (p : ℕ), a.factorization p = b.factorization p) → a = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Nat.eq_of_factorization_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_of_factorization_eq.h3 : ¬∀ {a b : ℕ}, a ≠ 0 → (∀ (p : ℕ), a.factorization p = b.factorization p) → a = b := fun hc_h => absurd (@hc_h (1) (0) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Nat.eq_of_factorization_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_of_factorization_eq.h4 : ¬∀ {a b : ℕ}, a ≠ 0 → b ≠ 0 → a = b := fun hc_h => absurd (@hc_h (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Matrix.map_natCast, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.map_natCast.h7 : Not
      (∀ {n α β : Type} [inst : DecidableEq n] [inst_1 : AddMonoidWithOne α] [inst_2 : Zero β] {f : α → β} (d : Nat),
        @Eq (Matrix n n β)
          (@Matrix.map n n α β
            (@Nat.cast (Matrix n n α)
              (@Matrix.instNatCastOfZero n α inst
                (@AddZero.toZero α
                  (@AddZeroClass.toAddZero α (@AddMonoid.toAddZeroClass α (@AddMonoidWithOne.toAddMonoid α inst_1))))
                (@AddMonoidWithOne.toNatCast α inst_1))
              d)
            f)
          (@Matrix.diagonal n β inst inst_2 fun (x : n) => f (@Nat.cast α (@AddMonoidWithOne.toNatCast α inst_1) d))) := fun hc_h => absurd (@hc_h (Bool) (Nat) (Nat) (instDecidableEqBool) (Nat.instAddMonoidWithOne) (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (fun n => n + 1 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Sum.LiftRel.isRight_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sum.LiftRel.isRight_right.h8 : ¬∀ {α β γ δ : Type} {r : α → γ → Prop} {s : β → δ → Prop} {y : γ ⊕ δ} {b : β}, y.isRight = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (Sum.inl 0) (0)) (by
  decide +kernel)

-- Sum.LiftRel.isRight_congr, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sum.LiftRel.isRight_congr.h8 : ¬∀ {α β γ δ : Type} {r : α → γ → Prop} {s : β → δ → Prop} {x : α ⊕ β} {y : γ ⊕ δ},
        x.isRight = Bool.true ↔ y.isRight = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (Sum.inl 0) (Sum.inr 0)) (by
  decide +kernel)

-- Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul.h2 : ¬∀ {p n : ℕ}, p ≤ n → 2 * n < 3 * p → n.centralBinom.factorization p = 0 := fun hc_h => absurd (@hc_h (2) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul.h3 : ¬∀ {p n : ℕ}, 2 < n → 2 * n < 3 * p → n.centralBinom.factorization p = 0 := fun hc_h => absurd (@hc_h (5) (3) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul.h4 : ¬∀ {p n : ℕ}, 2 < n → p ≤ n → n.centralBinom.factorization p = 0 := fun hc_h => absurd (@hc_h (2) (3) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.map_insertionSort, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map_insertionSort.h8 : ¬∀ {α β : Type} (r : α → α → Prop) (s : β → β → Prop) [inst : DecidableRel r] [inst_1 : DecidableRel s] (f : α → β)
        (l : List α), List.map f (List.insertionSort r l) = List.insertionSort s (List.map f l) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a = b : ℕ → ℕ → Prop) (Nat.decLt) (instDecidableEqNat) (fun n => n + 1 : ℕ → ℕ) ([0, 1])) (by
  decide +kernel)

-- Choose.eq_pow_multiplicity_of_choose_modEq_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.eq_pow_multiplicity_of_choose_modEq_zero.h2 : ¬∀ {n p : ℕ}, 0 < n → (∀ i ∈ Finset.Icc 1 (n - 1), ↑(n.choose i) ≡ 0 [ZMOD ↑p]) → n = p ^ multiplicity p n := fun hc_h => absurd (@hc_h (2) (1) (by
  decide) (by
  decide)) (by
  simp)

-- List.map_destutter, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map_destutter.h8 : ¬∀ {α β : Type} {R : α → α → Prop} [inst : DecidableRel R] {R₂ : β → β → Prop} [inst_1 : DecidableRel R₂] {f : α → β}
        {l : List α}, List.map f (List.destutter R l) = List.destutter R₂ (List.map f l) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) (fun _ => 0 : ℕ → ℕ) ([0, 1])) (by
  decide +kernel)

-- DFinsupp.comapDomain'_add, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.comapDomain'_add.h6 : ¬∀ {ι : Type} {β : ι → Type} {κ : Type} [inst : (i : ι) → AddZeroClass (β i)] (h : κ → ι) {h' : ι → κ}
        (f g : Π₀ (i : ι), β i), Function.LeftInverse h' h := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (Bool) (fun (i : ℕ) => Nat.instAddMonoid.toAddZeroClass) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n % 2 == 0 : ℕ → Bool) (0) (0)) (by
  decide +kernel)

-- Fin.castPred_mk, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_mk.h2 : ¬∀ {n : ℕ} (i : ℕ), i < n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Fin.castPred_mk, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.castPred_mk.h3.der : ∀ {n : ℕ}, ∀ i < n, i < n.succ := by
  (intros; solve_by_elim)
theorem HypCheckProof.Fin.castPred_mk.h3 : ∀ {n : ℕ} (i : ℕ) (h₁ : i < n)
      (h₃ :
        optParam ((⟨i, HypCheckProof.Fin.castPred_mk.h3.der i h₁⟩ : Fin (n + 1)) ≠ Fin.last n)
          ((Fin.ne_iff_vne (⟨i, HypCheckProof.Fin.castPred_mk.h3.der i h₁⟩ : Fin (n + 1)) (Fin.last n)).mpr
            (Eq.symm (Fin.val_last i) ▸ Nat.ne_of_lt h₁))),
      (⟨i, HypCheckProof.Fin.castPred_mk.h3.der i h₁⟩ : Fin (n + 1)).castPred h₃ = (⟨i, h₁⟩ : Fin n) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Fin.castPred_mk hc_x0 hc_x1 hc_x2 (@HypCheckProof.Fin.castPred_mk.h3.der hc_x0 hc_x1 hc_x2) hc_x3

-- Fin.castPred_mk, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.castPred_mk.h4.der : ∀ {n : ℕ} (i : ℕ) (h₁ : i < n) (h₂ : optParam (i < n.succ) (Nat.lt_trans h₁ (Nat.lt_succ_self n))),
      (⟨i, h₂⟩ : Fin (n + 1)) ≠ Fin.last n := by
  (intros; grind)
theorem HypCheckProof.Fin.castPred_mk.h4 : ∀ {n : ℕ} (i : ℕ) (h₁ : i < n) (h₂ : optParam (i < n.succ) (Nat.lt_trans h₁ (Nat.lt_succ_self n))),
      (⟨i, h₂⟩ : Fin (n + 1)).castPred (HypCheckProof.Fin.castPred_mk.h4.der i h₁ h₂) = (⟨i, h₁⟩ : Fin n) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Fin.castPred_mk hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Fin.castPred_mk.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- Nat.eq_or_coprime_of_le_prime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_or_coprime_of_le_prime.h2 : ¬∀ {n p : ℕ}, n ≤ p → Nat.Prime p → p = n ∨ p.Coprime n := fun hc_h => absurd (@hc_h (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.eq_or_coprime_of_le_prime, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_or_coprime_of_le_prime.h3 : ¬∀ {n p : ℕ}, n ≠ 0 → Nat.Prime p → p = n ∨ p.Coprime n := fun hc_h => absurd (@hc_h (4) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.eq_or_coprime_of_le_prime, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_or_coprime_of_le_prime.h4 : ¬∀ {n p : ℕ}, n ≠ 0 → n ≤ p → p = n ∨ p.Coprime n := fun hc_h => absurd (@hc_h (2) (4) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.find_comp_succ, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Nat.find_comp_succ.h2.der : ∀ {p : ℕ → Prop} [inst : DecidablePred p], (∃ (n : ℕ), p (n + 1)) → ¬p 0 → ∃ (n : ℕ), p n := by
  (intros; grind)
theorem HypCheckProof.Nat.find_comp_succ.h2 : ∀ {p : ℕ → Prop} [inst : DecidablePred p] (h₂ : ∃ (n : ℕ), p (n + 1)) (h0 : ¬p 0),
      Nat.find (HypCheckProof.Nat.find_comp_succ.h2.der h₂ h0) = Nat.find h₂ + 1 := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Nat.find_comp_succ hc_x0 hc_x1 (@HypCheckProof.Nat.find_comp_succ.h2.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x2 hc_x3

-- Nat.find_comp_succ, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_comp_succ.h4 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] (h₁ : ∃ (n : ℕ), p n) (h₂ : ∃ (n : ℕ), p (n + 1)),
        Nat.find h₁ = Nat.find h₂ + 1 := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (fun _ => True : ℕ → Prop) (fun (a : ℕ) => instDecidableTrue) hc_k0 hc_k1) (by
  simp)

-- Nat.not_prime_of_dvd_of_ne, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_prime_of_dvd_of_ne.h2 : ¬∀ {m n : ℕ}, m ≠ 1 → m ≠ n → ¬Nat.Prime n := fun hc_h => absurd (@hc_h (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.not_prime_of_dvd_of_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_prime_of_dvd_of_ne.h3 : ¬∀ {m n : ℕ}, m ∣ n → m ≠ n → ¬Nat.Prime n := fun hc_h => absurd (@hc_h (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.not_prime_of_dvd_of_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_prime_of_dvd_of_ne.h4 : ¬∀ {m n : ℕ}, m ∣ n → m ≠ 1 → ¬Nat.Prime n := fun hc_h => absurd (@hc_h (2) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.eq_of_perm_primeFactorsList, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_of_perm_primeFactorsList.h2 : ¬∀ {a b : ℕ}, b ≠ 0 → a.primeFactorsList.Perm b.primeFactorsList → a = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide) (by
  decide +kernel)) (by
  decide +kernel)

-- Nat.eq_of_perm_primeFactorsList, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_of_perm_primeFactorsList.h3 : ¬∀ {a b : ℕ}, a ≠ 0 → a.primeFactorsList.Perm b.primeFactorsList → a = b := fun hc_h => absurd (@hc_h (1) (0) (by
  decide) (by
  decide +kernel)) (by
  decide +kernel)

-- Nat.eq_of_perm_primeFactorsList, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_of_perm_primeFactorsList.h4 : ¬∀ {a b : ℕ}, a ≠ 0 → b ≠ 0 → a = b := fun hc_h => absurd (@hc_h (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.mem_primeFactors, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.mem_primeFactors.h2 : ¬∀ {n p : ℕ}, p ∣ n → n ≠ 0 → p ∈ n.primeFactors := fun hc_h => absurd (@hc_h (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.mem_primeFactors, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.mem_primeFactors.h3 : ¬∀ {n p : ℕ}, Nat.Prime p → n ≠ 0 → p ∈ n.primeFactors := fun hc_h => absurd (@hc_h (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.mem_primeFactors, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.mem_primeFactors.h4 : ¬∀ {n p : ℕ}, Nat.Prime p → p ∣ n → p ∈ n.primeFactors := fun hc_h => absurd (@hc_h (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Matrix.submatrix_one, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.submatrix_one.h8 : Not
      (∀ {l m α : Type} [inst : Zero α] [inst_1 : One α] [inst_2 : DecidableEq m] [inst_3 : DecidableEq l] (e : l → m),
        @Eq (Matrix l l α)
          (@Matrix.submatrix l m m l α
            (@OfNat.ofNat (Matrix m m α) (nat_lit 1) (@One.toOfNat1 (Matrix m m α) (@Matrix.one m α inst_2 inst inst_1))) e
            e)
          (@OfNat.ofNat (Matrix l l α) (nat_lit 1) (@One.toOfNat1 (Matrix l l α) (@Matrix.one l α inst_3 inst inst_1)))) := fun hc_h => absurd (@hc_h (Bool) (Nat) (Nat) (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (Nat.instOne) (instDecidableEqNat) (instDecidableEqBool) (fun _ => 0 : Bool → Nat)) (by
  decide +kernel)

-- Nat.digits_ofDigits, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_ofDigits.h3 : ¬∀ (b : ℕ), 1 < b → ∀ (L : List ℕ), (∀ (h : L ≠ []), L.getLast h ≠ 0) → b.digits (Nat.ofDigits b L) = L := fun hc_h => absurd (@hc_h (2) (by
  decide) ([2]) (by
  decide)) (by
  decide +kernel)

-- Nat.digits_ofDigits, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_ofDigits.h4 : ¬∀ (b : ℕ), 1 < b → ∀ (L : List ℕ), (∀ l ∈ L, l < b) → b.digits (Nat.ofDigits b L) = L := fun hc_h => absurd (@hc_h (2) (by
  decide) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.SortedLE.sortedLT_of_nodup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLE.sortedLT_of_nodup.h3 : ¬∀ {α : Type} [inst : PartialOrder α] {l : List α}, l.Nodup → l.SortedLT := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([1, 0]) (by
  decide)) (by
  decide +kernel)

-- List.SortedLE.sortedLT_of_nodup, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLE.sortedLT_of_nodup.h4 : ¬∀ {α : Type} [inst : PartialOrder α] {l : List α}, l.SortedLE → l.SortedLT := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0, 0]) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.coprime_pow_of_not_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.coprime_pow_of_not_dvd.h3 : ¬∀ {p m a : ℕ}, ¬p ∣ a → a.Coprime (p ^ m) := fun hc_h => absurd (@hc_h (0) (1) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.coprime_pow_of_not_dvd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.coprime_pow_of_not_dvd.h4 : ¬∀ {p m a : ℕ}, Nat.Prime p → a.Coprime (p ^ m) := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.mem_primeFactorsList_mul_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mem_primeFactorsList_mul_right.h3 : ¬∀ {p a b : ℕ}, a ≠ 0 → p ∈ (a * b).primeFactorsList := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.mem_primeFactorsList_mul_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mem_primeFactorsList_mul_right.h4 : ¬∀ {p a b : ℕ}, p ∈ b.primeFactorsList → p ∈ (a * b).primeFactorsList := fun hc_h => absurd (@hc_h (2) (0) (2) (by
  decide +kernel)) (by
  decide +kernel)

-- Set.ncard_compl_of_ncard_eq_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_compl_of_ncard_eq_add.h3 : ¬∀ {α : Type} (s : Set α) {n : ℕ}, autoParam s.Finite Set.ncard_compl_of_ncard_eq_add._auto_1 → sᶜ.ncard = n := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1) (by
  simp)) (by
  simp)

-- Set.ncard_le_ncard, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_le_ncard.h3 : ¬∀ {α : Type} {s t : Set α}, autoParam t.Finite Set.ncard_le_ncard._auto_1 → s.ncard ≤ t.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Set.ncard_le_ncard, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_le_ncard.h4 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t → s.ncard ≤ t.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | True}) (by
  simp)) (by
  simp)

-- ZMod.ringEquivCongr_trans, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.ringEquivCongr_trans.h3 : ¬∀ {a b c : ℕ}, b = c → a = b := fun hc_h => absurd (@hc_h (0) _ (1) rfl) (by
  decide +kernel)

-- ZMod.ringEquivCongr_trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.ringEquivCongr_trans.h4 : ¬∀ {a b c : ℕ}, a = b → b = c := fun hc_h => absurd (@hc_h _ (0) (1) rfl) (by
  decide +kernel)

-- Set.ncard_sdiff_singleton_lt_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_sdiff_singleton_lt_of_mem.h3 : ¬∀ {α : Type} {s : Set α} {a : α},
        autoParam s.Finite Set.ncard_sdiff_singleton_lt_of_mem._auto_1 → (s \ {a}).ncard < s.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1) (by
  simp)) (by
  simp)

-- Set.odd_card_insert_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.odd_card_insert_iff.h3 : ¬∀ {α : Type} {s : Set α} {a : α},
        autoParam s.Finite Set.odd_card_insert_iff._auto_1 → (Odd (Insert.insert a s).ncard ↔ Even s.ncard) := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0) (by
  simp)) (by
  simp)

-- Nat.ofDigits_mod_pow_eq_ofDigits_take, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofDigits_mod_pow_eq_ofDigits_take.h4 : ¬∀ {p : ℕ} (i : ℕ), 0 < p → ∀ (digits : List ℕ), Nat.ofDigits p digits % p ^ i = Nat.ofDigits p (List.take i digits) := fun hc_h => absurd (@hc_h (1) (1) (by
  decide) ([1])) (by
  decide +kernel)

-- Nat.digits_base_pow_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_base_pow_mul.h3 : ¬∀ {b k m : ℕ}, 0 < m → b.digits (b ^ k * m) = List.replicate k 0 ++ b.digits m := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.digits_base_pow_mul, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_base_pow_mul.h4 : ¬∀ {b k m : ℕ}, 1 < b → b.digits (b ^ k * m) = List.replicate k 0 ++ b.digits m := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Set.ncard_sdiff_add_ncard_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_sdiff_add_ncard_of_subset.h3 : ¬∀ {α : Type} {s t : Set α},
        autoParam t.Finite Set.ncard_sdiff_add_ncard_of_subset._auto_1 → (t \ s).ncard + s.ncard = t.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Nat.sum_digits_ofDigits_eq_sum, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.sum_digits_ofDigits_eq_sum.h4 : ¬∀ {b : ℕ}, 1 < b → ∀ {l : ℕ} {L : List ℕ}, (b.digits (Nat.ofDigits b L)).sum = L.sum := fun hc_h => absurd (@hc_h (2) (by
  decide) (0) ([2])) (by
  decide +kernel)

-- padicValNat_base_pow_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.padicValNat_base_pow_mul.h2 : ¬∀ {p n : ℕ}, n ≠ 0 → ∀ (k : ℕ), multiplicity p (p ^ k * n) = multiplicity p n + k := fun hc_h => absurd (@hc_h (1) (1) (by
  decide) (1)) (by
  simp)

-- Nat.factorization_eq_of_coprime_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_of_coprime_left.h3 : ¬∀ {p a b : ℕ}, p ∈ a.primeFactorsList → (a * b).factorization p = a.factorization p := fun hc_h => absurd (@hc_h (2) (2) (0) (by
  decide +kernel)) (by
  decide +kernel)

-- Nat.factorization_eq_of_coprime_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_of_coprime_left.h4 : ¬∀ {p a b : ℕ}, a.Coprime b → (a * b).factorization p = a.factorization p := fun hc_h => absurd (@hc_h (2) (1) (2) (by
  decide)) (by
  decide +kernel)

-- Set.subset_iff_eq_of_ncard_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_iff_eq_of_ncard_le.h3 : ¬∀ {α : Type} {s t : Set α}, autoParam t.Finite Set.subset_iff_eq_of_ncard_le._auto_1 → (s ⊆ t ↔ s = t) := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.subset_iff_eq_of_ncard_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_iff_eq_of_ncard_le.h4 : ¬∀ {α : Type} {s t : Set α}, t.ncard ≤ s.ncard → (s ⊆ t ↔ s = t) := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | True}) (by
  simp)) (by
  simp)

-- Nat.ordProj_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordProj_mul.h3 : ¬∀ {a b : ℕ} (p : ℕ), b ≠ 0 → p ^ (a * b).factorization p = p ^ a.factorization p * p ^ b.factorization p := fun hc_h => absurd (@hc_h (0) (2) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.ordProj_mul, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordProj_mul.h4 : ¬∀ {a b : ℕ} (p : ℕ), a ≠ 0 → p ^ (a * b).factorization p = p ^ a.factorization p * p ^ b.factorization p := fun hc_h => absurd (@hc_h (2) (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.dvd_ordCompl_of_dvd_not_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_ordCompl_of_dvd_not_dvd.h3 : ¬∀ {p d n : ℕ}, ¬p ∣ d → d ∣ n / p ^ n.factorization p := fun hc_h => absurd (@hc_h (0) (2) (1) (by
  decide)) (by
  decide +kernel)

-- Set.Infinite.mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.mono.h4 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t → t.Infinite := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Nat.Prime.emultiplicity_factorial, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.emultiplicity_factorial.h1 : ¬∀ {p n b : ℕ}, Nat.log p n < b → emultiplicity p n.factorial = ↑(∑ i ∈ Finset.Ico 1 b, n / p ^ i) := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide)) (by
  simp)

-- Set.Infinite.inter_of_finite_sdiff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.inter_of_finite_sdiff.h3 : ¬∀ {α : Type} {s t : Set α}, (s \ t).Finite → (s ∩ t).Infinite := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n % 2 = 0}) (by
  simp)) (by
  simp)

-- Set.infinite_range_of_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infinite_range_of_injective.h2 : ¬∀ {α β : Type} {f : α → β}, Function.Injective f → (Set.range f).Infinite := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  simp)

-- Set.infinite_range_of_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infinite_range_of_injective.h4 : ¬∀ {α β : Type} [inst : Infinite α] {f : α → β}, (Set.range f).Infinite := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _ (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Set.MapsTo.comp_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.comp_left.h7 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {f : α → β} (g : β → γ), Set.MapsTo (g ∘ f) s (g '' t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.ncard_sdiff', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_sdiff'.h3 : ¬∀ {α : Type} {s t : Set α}, autoParam t.Finite Set.ncard_sdiff'._auto_1 → (t \ s).ncard = t.ncard - s.ncard := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (by
  simp)) (by
  simp)

-- Set.even_card_insert_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.even_card_insert_iff.h3 : ¬∀ {α : Type} {s : Set α} {a : α},
        autoParam s.Finite Set.even_card_insert_iff._auto_1 → (Even (Insert.insert a s).ncard ↔ Odd s.ncard) := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0) (by
  simp)) (by
  simp)

-- Set.ncard_diff_singleton_lt_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_diff_singleton_lt_of_mem.h3 : ¬∀ {α : Type} {s : Set α} {a : α},
        autoParam s.Finite Set.ncard_sdiff_singleton_lt_of_mem._auto_1 → (s \ {a}).ncard < s.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1) (by
  simp)) (by
  simp)

-- Set.MapsTo.comp_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.comp_right.h6 : ¬∀ {α β γ : Type} {g : β → γ} {s : Set β} {t : Set γ} (f : α → β), Set.MapsTo (g ∘ f) (f ⁻¹' s) t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- List.Sublist.antisymm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.antisymm.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₂.Sublist l₁ → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.Sublist.antisymm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.antisymm.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.Sublist l₂ → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- Set.subset_eq_empty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_eq_empty.h3 : ¬∀ {α : Type} {s t : Set α}, s = ∅ → t = ∅ := fun hc_h => absurd (@hc_h (ℕ) _ ({n : ℕ | n = 0}) rfl) (by
  simp)

-- Set.subset_eq_empty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_eq_empty.h4 : ¬∀ {α : Type} {s t : Set α}, t ⊆ s → t = ∅ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Set.exists_eq_const_of_preimage_singleton, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_eq_const_of_preimage_singleton.h4 : ¬∀ {α β : Type} [inst : Nonempty β] {f : α → β}, ∃ (b : β), f = Function.const α b := fun hc_h => absurd (@hc_h (Bool) (Bool) _ (not : Bool → Bool)) (by
  decide +kernel)

-- Set.image2_congr', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_congr'.h7 : ¬∀ {α β γ : Type} {f f' : α → β → γ} {s : Set α} {t : Set β}, Set.image2 f s t = Set.image2 f' s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) (fun a b => a < b : ℕ → ℕ → Bool) (fun a b => a ≤ b : ℕ → ℕ → Bool) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- List.relationReflTransGen_of_exists_isChain, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.relationReflTransGen_of_exists_isChain.h4 : ¬∀ {α : Type} {r : α → α → Prop} (l : List α), List.IsChain r l → l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (by
  decide)) (by
  decide +kernel)

-- List.eq_of_head?_eq_of_tail_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.eq_of_head?_eq_of_tail_eq.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.tail = l₂.tail → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.eq_of_head?_eq_of_tail_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.eq_of_head?_eq_of_tail_eq.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.head? = l₂.head? → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([0, 1]) (by
  decide)) (by
  decide +kernel)

-- Int.lt.elim, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.lt.elim.h2 : ¬∀ {a b : ℤ} {P : Prop}, (∀ (n : ℕ), a + ↑n.succ = b → P) → P := fun hc_h => absurd (@hc_h (0) (0) (False) (by
  omega)) (by
  decide +kernel)

-- Int.lt.elim, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.lt.elim.h4 : ¬∀ {a b : ℤ}, a < b → ∀ {P : Prop}, P := fun hc_h => absurd (@hc_h (0) (1) (by
  decide) (False)) (by
  decide +kernel)

-- List.mem_dropLast_of_mem_of_ne_getLast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_dropLast_of_mem_of_ne_getLast.h3 : ¬∀ {α : Type} {l : List α} {a : α}, a ∈ l := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- List.mem_dropLast_of_mem_of_ne_getLast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_dropLast_of_mem_of_ne_getLast.h4 : ¬∀ {α : Type} {l : List α} {a : α}, a ∈ l → a ∈ l.dropLast := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (by
  decide)) (by
  decide +kernel)

-- Set.image2_subset_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_subset_right.h7 : ¬∀ {α β γ : Type} {f : α → β → γ} {s s' : Set α} {t : Set β}, Set.image2 f s t ⊆ Set.image2 f s' t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- EReal.div_lt_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_lt_iff.h3 : ¬∀ {a b c : EReal}, c ≠ ⊤ → (b / c < a ↔ b < a * c) := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  (simp <;> omega))

-- EReal.div_le_iff_le_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_le_iff_le_mul.h3 : ¬∀ {a b c : EReal}, b ≠ ⊤ → (a / b ≤ c ↔ a ≤ b * c) := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  (simp <;> omega))

-- Int.le_div_iff_of_dvd_of_neg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.le_div_iff_of_dvd_of_neg.h3 : ¬∀ {a b c : ℤ}, c ∣ b → (a ≤ b / c ↔ b ≤ c * a) := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Int.le_div_iff_of_dvd_of_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.le_div_iff_of_dvd_of_neg.h4 : ¬∀ {a b c : ℤ}, c < 0 → (a ≤ b / c ↔ b ≤ c * a) := fun hc_h => absurd (@hc_h (0) (1) (-2) (by
  decide)) (by
  decide +kernel)

-- Set.empty_eq_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.empty_eq_of_subset.h3 : ¬∀ {α : Type} {s t : Set α}, ∅ = s → ∅ = t := fun hc_h => absurd (@hc_h (ℕ) _ ({n : ℕ | n = 0}) rfl) (by
  simp)

-- Set.empty_eq_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.empty_eq_of_subset.h4 : ¬∀ {α : Type} {s t : Set α}, t ⊆ s → ∅ = t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Sum.getRight_eq_getRight?, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Sum.getRight_eq_getRight?.h3.der.{u, v} : ∀ {α : Type u} {β : Type v} {x : α ⊕ β}, x.getRight?.isSome = Bool.true → x.isRight = Bool.true := by
  (intros; simp_all; done)
theorem HypCheckProof.Sum.getRight_eq_getRight?.h3.{u, v} : ∀ {α : Type u} {β : Type v} {x : α ⊕ β} (h₂ : x.getRight?.isSome = Bool.true),
      x.getRight (HypCheckProof.Sum.getRight_eq_getRight?.h3.der h₂) = x.getRight?.get h₂ := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Sum.getRight_eq_getRight? hc_x0 hc_x1 hc_x2 (@HypCheckProof.Sum.getRight_eq_getRight?.h3.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x3

-- Sum.getRight_eq_getRight?, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Sum.getRight_eq_getRight?.h4.der.{u, v} : ∀ {α : Type u} {β : Type v} {x : α ⊕ β}, x.isRight = Bool.true → x.getRight?.isSome = Bool.true := by
  (intros; simp_all; done)
theorem HypCheckProof.Sum.getRight_eq_getRight?.h4.{u, v} : ∀ {α : Type u} {β : Type v} {x : α ⊕ β} (h₁ : x.isRight = Bool.true),
      x.getRight h₁ = x.getRight?.get (HypCheckProof.Sum.getRight_eq_getRight?.h4.der h₁) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Sum.getRight_eq_getRight? hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Sum.getRight_eq_getRight?.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- Int.div_dvd_iff_dvd_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_dvd_iff_dvd_mul.h3 : ¬∀ {a b c : ℤ}, b ≠ 0 → (a / b ∣ c ↔ a ∣ b * c) := fun hc_h => absurd (@hc_h (1) (2) (1) (by
  decide)) (by
  decide +kernel)

-- Int.div_dvd_iff_dvd_mul, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_dvd_iff_dvd_mul.h4 : ¬∀ {a b c : ℤ}, b ∣ a → (a / b ∣ c ↔ a ∣ b * c) := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Int.mul_dvd_of_dvd_div, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.mul_dvd_of_dvd_div.h3 : ¬∀ {a b c : ℤ}, a ∣ b / c → c * a ∣ b := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Int.mul_dvd_of_dvd_div, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.mul_dvd_of_dvd_div.h4 : ¬∀ {a b c : ℤ}, c ∣ b → c * a ∣ b := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Int.le_div_iff_of_dvd_of_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.le_div_iff_of_dvd_of_pos.h3 : ¬∀ {a b c : ℤ}, c ∣ b → (a ≤ b / c ↔ c * a ≤ b) := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Int.lt_div_iff_of_dvd_of_neg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.lt_div_iff_of_dvd_of_neg.h3 : ¬∀ {a b c : ℤ}, c ∣ b → (a < b / c ↔ b < c * a) := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- List.zipWith_rotate_distrib, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.zipWith_rotate_distrib.h7 : ¬∀ {α β γ : Type} (f : α → β → γ) (l : List α) (l' : List β) (n : ℕ),
        (List.zipWith f l l').rotate n = List.zipWith f (l.rotate n) (l'.rotate n) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ([0, 1]) ([0]) (1)) (by
  decide +kernel)

-- Part.eq_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.eq_of_mem.h3 : ¬∀ {α : Type} {a : Part α} {b : Part α}, a.Dom := fun hc_h => absurd (@hc_h (ℕ) (⊥) (0)) (by
  nofun)

-- Matrix.diagonal_apply_ne', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.diagonal_apply_ne'.h7 : ¬∀ {n α : Type} [inst : DecidableEq n] [inst_1 : Zero α] (d : n → α) {i j : n}, Matrix.diagonal d i j = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (Nat.instMulZeroClass.toZero) (fun n => n + 1 : ℕ → ℕ) (0) (0)) (by
  decide +kernel)

-- Matrix.diagonal_apply_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.diagonal_apply_ne.h7 : ¬∀ {n α : Type} [inst : DecidableEq n] [inst_1 : Zero α] (d : n → α) {i j : n}, Matrix.diagonal d i j = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (Nat.instMulZeroClass.toZero) (fun n => n + 1 : ℕ → ℕ) (0) (0)) (by
  decide +kernel)

-- Part.eq_iff_of_dom, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.eq_iff_of_dom.h3 : ¬∀ {α : Type} {a b : Part α}, b.Dom → a.Dom := fun hc_h => absurd (@hc_h (ℕ) (⊥) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.eq_iff_of_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.eq_iff_of_dom.h4 : ¬∀ {α : Type} {a b : Part α}, a.Dom → b.Dom := fun hc_h => absurd (@hc_h (ℕ) (0) (⊥) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Matrix.one_apply_ne', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.one_apply_ne'.h7 : Not
      (∀ {n α : Type} [inst : DecidableEq n] [inst_1 : Zero α] [inst_2 : One α] {i j : n},
        @Eq α
          (@OfNat.ofNat (Matrix n n α) (nat_lit 1) (@One.toOfNat1 (Matrix n n α) (@Matrix.one n α inst inst_1 inst_2)) i j)
          (@OfNat.ofNat α (nat_lit 0) (@Zero.toOfNat0 α inst_1))) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (Nat.instOne) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Matrix.diagonal_eq_ofNat, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.diagonal_eq_ofNat.h7 : ¬∀ {n α : Type} [inst : DecidableEq n] [inst : Zero α] [inst : NatCast α] {d : n → α} {m : ℕ}, m.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (Nat.instMulZeroClass.toZero) (instNatCastNat) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.Pi.cons_same, hypothesis 7: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Multiset.Pi.cons_same.h7.der.{u_1, u_2} : ∀ {α : Type u_1} [inst : DecidableEq α] {δ : α → Sort u_2} {m : Multiset α} {a : α} {b : δ a}
      {f : (a : α) → @Membership.mem α (Multiset α) (@Multiset.instMembership α) m a → δ a},
      @Membership.mem α (Multiset α) (@Multiset.instMembership α) (@Multiset.cons α a m) a := by
  (intros; simp; done)
theorem HypCheckProof.Multiset.Pi.cons_same.h7.{u_1, u_2} : ∀ {α : Type u_1} [inst : DecidableEq α] {δ : α → Sort u_2} {m : Multiset α} {a : α} {b : δ a}
      {f : (a : α) → @Membership.mem α (Multiset α) (@Multiset.instMembership α) m a → δ a},
      @Eq (δ a) (@Multiset.Pi.cons α inst δ m a b f a (@HypCheckProof.Multiset.Pi.cons_same.h7.der α inst δ m a b f)) b := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Multiset.Pi.cons_same hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.Multiset.Pi.cons_same.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6)

-- Int.mul_ediv_le_mul_ediv_assoc, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.mul_ediv_le_mul_ediv_assoc.h1 : ¬∀ {a : ℤ} (b : ℤ) {c : ℤ}, 0 ≤ c → a * (b / c) ≤ a * b / c := fun hc_h => absurd (@hc_h (-1) (1) (2) (by
  decide)) (by
  decide +kernel)

-- Int.mul_ediv_le_mul_ediv_assoc, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.mul_ediv_le_mul_ediv_assoc.h4 : ¬∀ {a : ℤ}, 0 ≤ a → ∀ (b : ℤ) {c : ℤ}, a * (b / c) ≤ a * b / c := fun hc_h => absurd (@hc_h (2) (by
  decide) (1) (-2)) (by
  decide +kernel)

-- Int.fdiv_fdiv_eq_fdiv_mul, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.fdiv_fdiv_eq_fdiv_mul.h4 : ¬∀ (m : ℤ) {n k : ℤ}, 0 ≤ n → (m.fdiv n).fdiv k = m.fdiv (n * k) := fun hc_h => absurd (@hc_h (1) (2) (-1) (by
  decide)) (by
  decide +kernel)

-- List.dlookup_kinsert_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dlookup_kinsert_ne.h7 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a a' : α} {b' : β a'} {l : List (Sigma β)},
        List.dlookup a (List.kinsert a' b' l) = List.dlookup a l := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) (0) (0) ([])) (by
  decide +kernel)

-- List.Pairwise.nodup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.nodup.h3 : ¬∀ {α : Type} {l : List α} {r : α → α → Prop}, List.Pairwise r l → l.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (fun a b => a ≤ b : ℕ → ℕ → Prop) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.nodup, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.nodup.h4 : ¬∀ {α : Type} {l : List α} {r : α → α → Prop} [inst : Std.Irrefl r], l.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (fun a b => a < b : ℕ → ℕ → Prop) _) (by
  decide +kernel)

-- Fin.natCast_le_natCast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.natCast_le_natCast.h3 : Not
      (∀ {n a b : Nat},
        @LE.le Nat instLENat b n →
          Iff
            (@LE.le
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@instLEFin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Nat.cast
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Fin.NatCast.instNatCast
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                a)
              (@Nat.cast
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Fin.NatCast.instNatCast
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                b))
            (@LE.le Nat instLENat a b)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Fin.natCast_le_natCast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.natCast_le_natCast.h4 : Not
      (∀ {n a b : Nat},
        @LE.le Nat instLENat a n →
          Iff
            (@LE.le
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@instLEFin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Nat.cast
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Fin.NatCast.instNatCast
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                a)
              (@Nat.cast
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Fin.NatCast.instNatCast
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                b))
            (@LE.le Nat instLENat a b)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Matrix.vecMul_ofNat, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.vecMul_ofNat.h6 : ¬∀ {m α : Type} [inst : NonAssocSemiring α] [inst : Fintype m] [inst : DecidableEq m] (x : ℕ) (v : m → α), x.AtLeastTwo := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Nat.instNonAssocSemiring) (Bool.fintype) (instDecidableEqBool) (0) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fin.sub_ne_last_of_ne_last_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.sub_ne_last_of_ne_last_of_le.h3 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, b ≤ a → a - b ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- Fin.sub_ne_last_of_ne_last_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.sub_ne_last_of_ne_last_of_le.h4 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, a ≠ Fin.last n → a - b ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.mk_eq_mk, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.mk_eq_mk.h2 : ¬∀ {n a a' : ℕ} {h' : a' < n}, a < n := fun hc_h => absurd (@hc_h (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Fin.mk_eq_mk, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.mk_eq_mk.h4 : ¬∀ {n a : ℕ} {h : a < n} {a' : ℕ}, a' < n := fun hc_h => absurd (@hc_h (1) (0) (by
  decide) (1)) (by
  decide +kernel)

-- Fin.castLE_natCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castLE_natCast.h2 : ¬∀ {m n : ℕ}, m ≤ n → ∀ (a : ℕ), NeZero m := fun hc_h => absurd (@hc_h (0) (0) (by
  decide) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fin.castLE_natCast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castLE_natCast.h3 : ¬∀ {m n : ℕ} [inst : NeZero m] (a : ℕ), m ≤ n := fun hc_h => absurd (@hc_h (1) (0) _ (0)) (by
  decide +kernel)

-- Fin.succAbove_eq_zero_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_eq_zero_iff.h4 : ¬∀ {n : ℕ} [inst : NeZero n] {a : Fin (n + 1)} {b : Fin n}, a.succAbove b = 0 ↔ b = 0 := fun hc_h => absurd (@hc_h (1) _ ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- AList.lookup_insert_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.AList.lookup_insert_ne.h7 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a a' : α} {b' : β a'} {s : AList β},
        AList.lookup a (AList.insert a' b' s) = AList.lookup a s := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) (0) (0) (∅)) (by
  decide +kernel)

-- Fin.predAbove_castPred_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_castPred_of_le.h3 : ¬∀ {n : ℕ} (p i : Fin (n + 1)), p ≠ Fin.last n → i ≤ p := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.predAbove_castPred_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_castPred_of_le.h4 : ¬∀ {n : ℕ} (p i : Fin (n + 1)), i ≤ p → p ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- Fin.pred_succAbove, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.pred_succAbove.h3 : ¬∀ {n : ℕ} (x : Fin n) (y : Fin (n + 1)), y ≤ x.castSucc := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- AList.lookupFinsupp_eq_iff_of_ne_zero, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.AList.lookupFinsupp_eq_iff_of_ne_zero.h7 : ¬∀ {α M : Type} [inst : Zero M] [inst_1 : DecidableEq α] {l : AList fun (_x : α) => M} {a : α} {x : M},
        l.lookupFinsupp a = x ↔ x ∈ AList.lookup a l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (instDecidableEqNat) (∅) (0) (0)) (by
  decide +kernel)

-- Fin.castPred_le_castPred_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_le_castPred_iff.h3 : ¬∀ {n : ℕ} {i j : Fin (n + 1)} {hj : j ≠ Fin.last n}, i ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.castPred_le_castPred_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_le_castPred_iff.h4 : ¬∀ {n : ℕ} {i j : Fin (n + 1)} {hi : i ≠ Fin.last n}, j ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.castPred_lt_castPred, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_lt_castPred.h3 : ¬∀ {n : ℕ} {i j : Fin (n + 1)}, j ≠ Fin.last n → i < j := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.castPred_lt_castPred, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_lt_castPred.h4 : ¬∀ {n : ℕ} {i j : Fin (n + 1)}, i < j → j ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- finCongr_apply_mk, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finCongr_apply_mk.h2 : ¬∀ {n m : ℕ}, ∀ k < m, m = n := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- finCongr_apply_mk, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finCongr_apply_mk.h4 : ¬∀ {n m : ℕ}, m = n → ∀ (k : ℕ), k < m := fun hc_h => absurd (@hc_h (0) _ rfl (0)) (by
  decide +kernel)

-- Fin.sub_castPred_eq_castPred_sub_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.sub_castPred_eq_castPred_sub_of_le.h3 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, b ≤ a → a ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- Fin.sub_castPred_eq_castPred_sub_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.sub_castPred_eq_castPred_sub_of_le.h4 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, a ≠ Fin.last n → b ≤ a := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.succAbove_castPred_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_castPred_of_le.h3 : ¬∀ {n : ℕ} (p i : Fin (n + 1)) (hi : i ≠ Fin.last n), p.succAbove (i.castPred hi) = (i.castPred hi).succ := fun hc_h => absurd (fun hc_k0 => @hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) hc_k0) (by
  decide +kernel)

-- Fin.succAbove_castPred_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_castPred_of_le.h4 : ¬∀ {n : ℕ} (p i : Fin (n + 1)), p ≤ i → i ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- ENat.mul_le_mul_left_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.mul_le_mul_left_iff.h3 : ¬∀ {a x y : ℕ∞}, a ≠ ⊤ → (a * x ≤ a * y ↔ x ≤ y) := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- ENat.mul_le_mul_left_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.mul_le_mul_left_iff.h4 : ¬∀ {a x y : ℕ∞}, a ≠ 0 → (a * x ≤ a * y ↔ x ≤ y) := fun hc_h => absurd (@hc_h (⊤) (2) (1) (by
  decide)) (by
  decide +kernel)

-- Sum.getLeft_eq_getLeft?, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Sum.getLeft_eq_getLeft?.h3.der.{u, v} : ∀ {α : Type u} {β : Type v} {x : α ⊕ β}, x.getLeft?.isSome = Bool.true → x.isLeft = Bool.true := by
  (intros; simp_all; done)
theorem HypCheckProof.Sum.getLeft_eq_getLeft?.h3.{u, v} : ∀ {α : Type u} {β : Type v} {x : α ⊕ β} (h₂ : x.getLeft?.isSome = Bool.true),
      x.getLeft (HypCheckProof.Sum.getLeft_eq_getLeft?.h3.der h₂) = x.getLeft?.get h₂ := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Sum.getLeft_eq_getLeft? hc_x0 hc_x1 hc_x2 (@HypCheckProof.Sum.getLeft_eq_getLeft?.h3.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x3

-- Sum.getLeft_eq_getLeft?, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Sum.getLeft_eq_getLeft?.h4.der.{u, v} : ∀ {α : Type u} {β : Type v} {x : α ⊕ β}, x.isLeft = Bool.true → x.getLeft?.isSome = Bool.true := by
  (intros; simp_all; done)
theorem HypCheckProof.Sum.getLeft_eq_getLeft?.h4.{u, v} : ∀ {α : Type u} {β : Type v} {x : α ⊕ β} (h₁ : x.isLeft = Bool.true),
      x.getLeft h₁ = x.getLeft?.get (HypCheckProof.Sum.getLeft_eq_getLeft?.h4.der h₁) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Sum.getLeft_eq_getLeft? hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Sum.getLeft_eq_getLeft?.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- List.Ico.append_consecutive, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.append_consecutive.h3 : ¬∀ {n m l : ℕ}, m ≤ l → List.Ico n m ++ List.Ico m l = List.Ico n l := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.Ico.append_consecutive, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.append_consecutive.h4 : ¬∀ {n m l : ℕ}, n ≤ m → List.Ico n m ++ List.Ico m l = List.Ico n l := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Fin.succAbove_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_pos.h4 : ¬∀ {n : ℕ} [inst : NeZero n] (p : Fin (n + 1)) (i : Fin n), 0 < p.succAbove i := fun hc_h => absurd (@hc_h (1) _ ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.sigma_eq_of_eq_comp_cast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.sigma_eq_of_eq_comp_cast.h3 : ¬∀ {α : Type} {a b : (ii : ℕ) × (Fin ii → α)}, a.fst = b.fst := fun hc_h => absurd (@hc_h (ℕ) ((⟨0, fun (a : Fin 0) => 0⟩ : (ii : ℕ) × (Fin ii → ℕ))) ((⟨1, fun (a : Fin 1) => 0⟩ : (ii : ℕ) × (Fin ii → ℕ)))) (by
  decide +kernel)

-- Fin.sigma_eq_of_eq_comp_cast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.sigma_eq_of_eq_comp_cast.h4 : ¬∀ {α : Type} {a b : (ii : ℕ) × (Fin ii → α)}, a.fst = b.fst → a = b := fun hc_h => absurd (@hc_h (ℕ) ((⟨1, fun (a : Fin 1) => 0⟩ : (ii : ℕ) × (Fin ii → ℕ))) ((⟨1, fun (a : Fin 1) => 1⟩ : (ii : ℕ) × (Fin ii → ℕ))) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Nat.Coprime.of_dvd_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.of_dvd_right.h3 : ¬∀ {a b₁ b₂ : ℕ}, a.Coprime b₂ → a.Coprime b₁ := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.Coprime.of_dvd_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.of_dvd_right.h4 : ¬∀ {a b₁ b₂ : ℕ}, b₁ ∣ b₂ → a.Coprime b₁ := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- List.next_getLast_eq_head, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_getLast_eq_head.h3 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α), l.Nodup → l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (by
  decide)) (by
  decide +kernel)

-- Nat.div_lcm_eq_div_gcd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.div_lcm_eq_div_gcd.h3 : ¬∀ {n m k : ℕ}, n ∣ k → (k / m).lcm (k / n) = k / m.gcd n := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.div_lcm_eq_div_gcd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.div_lcm_eq_div_gcd.h4 : ¬∀ {n m k : ℕ}, m ∣ k → (k / m).lcm (k / n) = k / m.gcd n := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.nth_lt_nth', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_lt_nth'.h3 : ¬∀ {p : ℕ → Prop} {m n : ℕ}, (∀ (hf : (Set.ofPred p).Finite), n < hf.toFinset.card) → Nat.nth p m < Nat.nth p n := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (0) (0) (by
  simp)) (by
  simp)

-- Nat.nth_lt_nth', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_lt_nth'.h4 : ¬∀ {p : ℕ → Prop} {m n : ℕ}, m < n → Nat.nth p m < Nat.nth p n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (0) (1) (by
  decide)) (by
  simp)

-- Finsupp.comapDomain_single, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.comapDomain_single.h7 : ¬∀ {α β M : Type} [inst : Zero M] (f : α → β) (a : α) (m : M), Set.InjOn f (f ⁻¹' ↑(fun₀ | f a => m).support) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (fun _ => 0 : ℕ → ℕ) (0) (1)) (by
  simp)

-- Ordnode.Valid'.rotateL_lemma₁, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.rotateL_lemma₁.h3 : ¬∀ {a b c : ℕ}, c ≤ 3 * b → a ≤ 3 * b := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Valid'.rotateL_lemma₁, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.rotateL_lemma₁.h4 : ¬∀ {a b c : ℕ}, 3 * a ≤ b + c → a ≤ 3 * b := fun hc_h => absurd (@hc_h (1) (0) (3) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Valid'.merge_lemma, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.merge_lemma.h3 : ¬∀ {a b c : ℕ}, b ≤ 3 * c → 2 * (a + b) ≤ 9 * c + 5 := fun hc_h => absurd (@hc_h (3) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Valid'.merge_lemma, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.merge_lemma.h4 : ¬∀ {a b c : ℕ}, 3 * a < b + c + 1 → 2 * (a + b) ≤ 9 * c + 5 := fun hc_h => absurd (@hc_h (0) (3) (0) (by
  decide)) (by
  decide +kernel)

-- Set.image2_subset_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_subset_left.h7 : ¬∀ {α β γ : Type} {f : α → β → γ} {s : Set α} {t t' : Set β}, Set.image2 f s t ⊆ Set.image2 f s t' := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Ordnode.Valid'.node4L_lemma₃, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.node4L_lemma₃.h3 : ¬∀ {b c d : ℕ}, b ≤ 3 * c → d ≤ 3 * c := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Valid'.node4L_lemma₃, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.node4L_lemma₃.h4 : ¬∀ {b c d : ℕ}, 2 * d ≤ b + c + 1 → d ≤ 3 * c := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Set.eq_of_subset_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_subset_of_subset.h3 : ¬∀ {α : Type} {a b : Set α}, b ⊆ a → a = b := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Set.eq_of_subset_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_subset_of_subset.h4 : ¬∀ {α : Type} {a b : Set α}, a ⊆ b → a = b := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.eq_of_inclusion_surjective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_inclusion_surjective.h3 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Set.eq_of_inclusion_surjective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_inclusion_surjective.h4 : ¬∀ {α : Type} {s t : Set α} {h : s ⊆ t}, s = t := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.image_subset_image2_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_subset_image2_left.h7 : ¬∀ {α β γ : Type} {f : α → β → γ} {s : Set α} {t : Set β} {b : β}, (fun (a : α) => f a b) '' s ⊆ Set.image2 f s t := fun hc_h => absurd (@hc_h (ℕ) (Bool) (ℕ) (fun (a : ℕ) (b : Bool) => if b = Bool.true then 1 else 0) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.true}) (Bool.false)) (by
  simp)

-- Set.image2_comm, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_comm.h7 : ¬∀ {α β γ : Type} {f : α → β → γ} {s : Set α} {t : Set β} {g : β → α → γ}, Set.image2 f s t = Set.image2 g t s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) (fun a b => a < b : ℕ → ℕ → Bool) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun a b => a ≤ b : ℕ → ℕ → Bool)) (by
  simp)

-- List.concat_get_prefix, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.concat_get_prefix.h3 : ¬∀ {α : Type} {x y : List α} (hl : x.length < y.length), x ++ [y.get (⟨x.length, hl⟩ : Fin y.length)] <+: y := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) ([0]) ([1, 0]) hc_k0) (by
  decide +kernel)

-- List.concat_get_prefix, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.concat_get_prefix.h4 : ¬∀ {α : Type} {x y : List α}, x <+: y → x.length < y.length := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.infix_antisymm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.infix_antisymm.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₂ <:+: l₁ → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.infix_antisymm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.infix_antisymm.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <:+: l₂ → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.IsInfix.nodup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsInfix.nodup.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₂.Nodup → l₁.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) ([]) (by
  decide)) (by
  decide +kernel)

-- Nat.le_mod_add_mod_of_dvd_add_of_not_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_mod_add_mod_of_dvd_add_of_not_dvd.h3 : ¬∀ {a b c : ℕ}, ¬c ∣ a → c ≤ a % c + b % c := fun hc_h => absurd (@hc_h (1) (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.le_mod_add_mod_of_dvd_add_of_not_dvd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_mod_add_mod_of_dvd_add_of_not_dvd.h4 : ¬∀ {a b c : ℕ}, c ∣ a + b → c ≤ a % c + b % c := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Int.dvd_of_dvd_mul_right_of_gcd_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.dvd_of_dvd_mul_right_of_gcd_one.h3 : ¬∀ {a b c : ℤ}, a.gcd b = 1 → a ∣ c := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Int.dvd_of_dvd_mul_right_of_gcd_one, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.dvd_of_dvd_mul_right_of_gcd_one.h4 : ¬∀ {a b c : ℤ}, a ∣ b * c → a ∣ c := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.exists_mul_mod_eq_of_coprime, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_mul_mod_eq_of_coprime.h3 : ¬∀ {k n : ℕ} (r : ℕ), k ≠ 0 → ∃ m < k, n * m % k = r % k := fun hc_h => absurd (@hc_h (2) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.exists_mul_mod_eq_of_coprime, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_mul_mod_eq_of_coprime.h4 : ¬∀ {k n : ℕ} (r : ℕ), n.Coprime k → ∃ m < k, n * m % k = r % k := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Int.dvd_of_dvd_mul_left_of_gcd_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.dvd_of_dvd_mul_left_of_gcd_one.h3 : ¬∀ {a b c : ℤ}, a.gcd c = 1 → a ∣ b := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Int.dvd_of_dvd_mul_left_of_gcd_one, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.dvd_of_dvd_mul_left_of_gcd_one.h4 : ¬∀ {a b c : ℤ}, a ∣ b * c → a ∣ b := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Int.gcd_div, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.gcd_div.h3 : ¬∀ {a b c : ℤ}, c ∣ b → (a / c).gcd (b / c) = a.gcd b / c.natAbs := fun hc_h => absurd (@hc_h (-1) (0) (2) (by
  decide)) (by
  decide +kernel)

-- Int.gcd_div, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.gcd_div.h4 : ¬∀ {a b c : ℤ}, c ∣ a → (a / c).gcd (b / c) = a.gcd b / c.natAbs := fun hc_h => absurd (@hc_h (0) (-1) (2) (by
  decide)) (by
  decide +kernel)

-- Function.Injective.left_inv_of_invOfMemRange, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.left_inv_of_invOfMemRange.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst : DecidableEq β] {f : α → β} (b : ↑(Set.range f)), Function.Injective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (instDecidableEqNat) (fun _ => 0 : Bool → ℕ) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ Set.range fun (x : Bool) => 0 }))) (by
  decide +kernel)

-- Monotone.domRestrict, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Monotone.domRestrict.h5 : ¬∀ {α β : Type} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β} (s : Set α), Monotone (s.domRestrict f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.instPartialOrder.toPreorder) (Bool.instPartialOrder.toPreorder) (not : Bool → Bool) ({x : Bool | True})) (by
  decide +kernel)

-- List.toFinset_filterMap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.toFinset_filterMap.h5 : ¬∀ {α β : Type} (f : α → Option β) [inst : DecidableEq α] [inst : DecidableEq β] (s : List α) (a a' : α) (b : β),
        f a = Option.some b → f a' = Option.some b → a = a' := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun (a : Bool) => Option.some 0) (instDecidableEqBool) (instDecidableEqNat) ([])) (by
  decide +kernel)

-- Finset.image_univ_of_surjective, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_univ_of_surjective.h6 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : DecidableEq α] [inst_2 : Fintype β] {f : β → α},
        Finset.image f Finset.univ = Finset.univ := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (instDecidableEqBool) (Bool.fintype) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- Set.EqOn.surjOn_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.surjOn_iff.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f₁ f₂ : α → β}, Set.SurjOn f₁ s t ↔ Set.SurjOn f₂ s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- List.foldr_ext, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldr_ext.h6 : ¬∀ {α β : Type} (f g : α → β → β) (b : β) {l : List α}, List.foldr f b l = List.foldr g b l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun a b => a + b : ℕ → ℕ → ℕ) (1) ([0])) (by
  decide +kernel)

-- List.erase_orderedInsert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.erase_orderedInsert.h4 : ¬∀ {α : Type} {r : α → α → Prop} [inst : DecidableRel r] [inst_1 : DecidableEq α] (x : α) (xs : List α),
        (List.orderedInsert r x xs).erase x = xs := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) (instDecidableEqNat) (1) ([1, 0])) (by
  decide +kernel)

-- Finsupp.single_eq_of_ne', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.single_eq_of_ne'.h6 : ¬∀ {α M : Type} [inst : Zero M] {a a' : α} {b : M}, (fun₀ | a => b) a' = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (0) (0) (1)) (by
  simp)

-- List.kerase_append_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.kerase_append_left.h6 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {l₁ l₂ : List (Sigma β)},
        List.kerase a (l₁ ++ l₂) = List.kerase a l₁ ++ l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ([]) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  decide +kernel)

-- List.mapIdxMAux'_eq_mapIdxMGo, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mapIdxMAux'_eq_mapIdxMGo.h2 : ¬∀ {m : Type → Type} [inst : Monad m] {α : Type} (f : ℕ → α → m PUnit.{1}) (as : List α) (arr : Array PUnit.{1}),
        List.mapIdxMAux' f arr.size as = List.mapIdxM.go f as arr *> Pure.pure PUnit.unit := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => ℕ × α) (ℕ) (fun (a a_1 : ℕ) => (0, PUnit.unit)) ([]) (#[])) (by
  decide +kernel)

-- Set.EqOn.mapsTo_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.mapsTo_iff.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f₁ f₂ : α → β}, Set.MapsTo f₁ s t ↔ Set.MapsTo f₂ s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- List.forall₂_drop_append, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forall₂_drop_append.h6 : ¬∀ {α β : Type} {R : α → β → Prop} (l : List α) (l₁ l₂ : List β), List.Forall₂ R (List.drop l₁.length l) l₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([]) ([0])) (by
  decide +kernel)

-- Set.domRestrict_comp_codRestrict, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.domRestrict_comp_codRestrict.h6 : ¬∀ {α β ι : Type} {f : ι → α} {g : α → β} {b : Set α} (x : ι), f x ∈ b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- List.foldl_ext, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldl_ext.h6 : ¬∀ {α β : Type} (f g : α → β → α) (a : α) {l : List β}, List.foldl f a l = List.foldl g a l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun a b => a + b : ℕ → ℕ → ℕ) (0) ([1])) (by
  decide +kernel)

-- StrictMono.sortedGT_listMap, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictMono.sortedGT_listMap.h6 : ¬∀ {α β : Type} [inst : LinearOrder α] [inst_1 : Preorder β] {f : α → β} {l : List α},
        (List.map f l).SortedGT ↔ l.SortedGT := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Nat.instLinearOrder) (Bool.instPartialOrder.toPreorder) (fun n => n % 2 == 0 : ℕ → Bool) ([0, 1])) (by
  decide +kernel)

-- Fintype.sum_congr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.sum_congr.h6 : ¬∀ {α M : Type} [inst : Fintype α] [inst_1 : AddCommMonoid M] (f g : α → M), ∑ a : α, f a = ∑ a : α, g a := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (Nat.instAddCommMonoid) (fun b => if b then 1 else 0 : Bool → ℕ) (fun _ => 0 : Bool → ℕ)) (by
  decide +kernel)

-- List.foldl_cons_eq_apply_foldl, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldl_cons_eq_apply_foldl.h6 : ¬∀ {α β : Type} {l : List α} {v : β → α → β} {a : α} {b : β}, List.foldl v b (a :: l) = v (List.foldl v b l) a := fun hc_h => absurd (@hc_h (ℕ) (Bool) ([0]) (fun (a : Bool) (n : ℕ) => n % 2 == 0) (1) (Bool.false)) (by
  decide +kernel)

-- List.foldr_cons_eq_foldr_apply, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldr_cons_eq_foldr_apply.h6 : ¬∀ {α β : Type} {l : List α} {f : α → β → β} {a : α} {b : β}, List.foldr f b (a :: l) = List.foldr f (f a b) l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0]) (fun a b => a - b : ℕ → ℕ → ℕ) (1) (0)) (by
  decide +kernel)

-- List.interleaves_append_singleton_append_singleton_of_length_eq_length_add_one, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.interleaves_append_singleton_append_singleton_of_length_eq_length_add_one.h6 : ¬∀ {α : Type} {r : α → α → Prop} {l₁ l₂ : List α} {a b : α},
        List.Interleaves r (l₁ ++ [a]) (l₂ ++ [b]) ↔ r a b ∧ List.Interleaves r (l₁ ++ [a]) l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([]) (1) (0)) (by
  simp)

-- Set.Nonempty.of_image2_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.of_image2_right.h6 : ¬∀ {α β γ : Type} {f : α → β → γ} {s : Set α} {t : Set β}, t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- SemiconjBy.natCast_mul_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SemiconjBy.natCast_mul_left.h5 : ¬∀ {α : Type} [inst : Semiring α] {a x y : α} (n : ℕ), SemiconjBy (↑n * a) x y := fun hc_h => absurd (@hc_h (ℕ) (Nat.instSemiring) (1) (0) (1) (1)) (by
  nofun)

-- Fin.contractNth_apply_of_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.contractNth_apply_of_ne.h6 : ¬∀ {n : ℕ} {α : Type} (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n),
        j.contractNth op g k = g (j.succAbove k) := fun hc_h => absurd (@hc_h (1) (ℕ) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (fun a b => a - b : ℕ → ℕ → ℕ) (fun (a : Fin (1 + 1)) => 1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.contractNth_apply_of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.contractNth_apply_of_lt.h6 : ¬∀ {n : ℕ} {α : Type} (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n),
        j.contractNth op g k = g k.castSucc := fun hc_h => absurd (@hc_h (1) (ℕ) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (fun a b => a - b : ℕ → ℕ → ℕ) (fun (a : Fin (1 + 1)) => 1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.contractNth_apply_of_gt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.contractNth_apply_of_gt.h6 : ¬∀ {n : ℕ} {α : Type} (j : Fin (n + 1)) (op : α → α → α) (g : Fin (n + 1) → α) (k : Fin n),
        j.contractNth op g k = g k.succ := fun hc_h => absurd (@hc_h (1) (ℕ) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (fun a b => a - b : ℕ → ℕ → ℕ) (fun (a : Fin (1 + 1)) => 1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Monotone.restrict, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Monotone.restrict.h5 : ¬∀ {α β : Type} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β} (s : Set α), Monotone (s.domRestrict f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.instPartialOrder.toPreorder) (Bool.instPartialOrder.toPreorder) (not : Bool → Bool) ({x : Bool | True})) (by
  decide +kernel)

-- List.le_length_destutter'_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_length_destutter'_cons.h5 : ¬∀ {α : Type} {R : α → α → Prop} [inst : DecidableRel R] {a b : α} {l : List α},
        (List.destutter' R b l).length ≤ (List.destutter' R a (b :: l)).length := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) (1) (0) ([1])) (by
  decide +kernel)

-- Matrix.cons_vecAlt1, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.cons_vecAlt1.h3 : ¬∀ {α : Type} {m n : ℕ} (x y : α) (u : Fin m → α), m + 1 + 1 = n + 1 + (n + 1) := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (0) (0) (fun (a : Fin 0) => 0)) (by
  decide +kernel)

-- List.destutter'_cons_pos, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.destutter'_cons_pos.h6 : ¬∀ {α : Type} (l : List α) {R : α → α → Prop} [inst : DecidableRel R] {a b : α},
        List.destutter' R b (a :: l) = b :: List.destutter' R a l := fun hc_h => absurd (@hc_h (ℕ) ([]) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) (0) (0)) (by
  decide +kernel)

-- StrictAnti.sortedGT_listMap, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictAnti.sortedGT_listMap.h6 : ¬∀ {α β : Type} [inst : LinearOrder α] [inst_1 : Preorder β] {f : α → β} {l : List α},
        (List.map f l).SortedGT ↔ l.SortedLT := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instPreorder) (fun n => n + 1 : ℕ → ℕ) ([0, 1])) (by
  decide +kernel)

-- Bundle.TotalSpace.mk_cast, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bundle.TotalSpace.mk_cast.h5 : ¬∀ {B : Type} {F : Type} {E : B → Type} {x x' : B} (b : E x), x = x' := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => ℕ) (0) (1) (0)) (by
  decide +kernel)

-- Int.log_of_one_le_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.log_of_one_le_right.h6 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] (b : ℕ) {r : R},
        Int.log b r = ↑(Nat.log b ⌊r⌋₊) := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) (2) (1 / 2)) (by
  decide +kernel)

-- Ordnode.Valid.right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid.right.h6 : ¬∀ {α : Type} [inst : Preorder α] {s : ℕ} {l : Ordnode α} {x : α} {r : Ordnode α}, r.Valid := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (0) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil)) (by
  nofun)

-- Rat.isNat_round, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.isNat_round.h6 : ¬∀ {R : Type} [inst : Ring R] [inst_1 : LinearOrder R] [inst_2 : FloorRing R] (r : R) (m : ℕ),
        Mathlib.Meta.NormNum.IsNat (round r) m := fun hc_h => absurd (@hc_h (ℤ) (Int.instRing) (Int.instLinearOrder) (instFloorRingInt) (0) (1)) (by
  nofun)

-- Rat.isInt_intCeil, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.isInt_intCeil.h6 : ¬∀ {R : Type} [inst : Ring R] [inst_1 : LinearOrder R] [inst_2 : FloorRing R] (r : R) (m : ℤ),
        Mathlib.Meta.NormNum.IsInt ⌈r⌉ m := fun hc_h => absurd (@hc_h (ℤ) (Int.instRing) (Int.instLinearOrder) (instFloorRingInt) (0) (1)) (by
  nofun)

-- Finsupp.mapRange_zero, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.mapRange_zero.h6 : ¬∀ {α : Type} {M N : Type} [inst : Zero M] [inst_1 : Zero N] {f : M → N}, f 0 = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instMulZeroClass.toZero) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Set.surjOn_iUnion_iUnion, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.surjOn_iUnion_iUnion.h6 : ¬∀ {α β ι : Type} {s : ι → Set α} {t : ι → Set β} {f : α → β}, Set.SurjOn f (⋃ (i : ι), s i) (⋃ (i : ι), t i) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Ordnode.Valid.left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid.left.h6 : ¬∀ {α : Type} [inst : Preorder α] {s : ℕ} {l : Ordnode α} {x : α} {r : Ordnode α}, l.Valid := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.nil)) (by
  nofun)

-- Set.InjOn.of_comp, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.of_comp.h6 : ¬∀ {α β γ : Type} {s : Set α} {f : α → β} {g : β → γ}, Set.InjOn f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({x : ℕ | True}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.bijOn_comm, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.bijOn_comm.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} {g : β → α}, Set.BijOn f s t ↔ Set.BijOn g t s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Int.log_of_left_le_one, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.log_of_left_le_one.h5 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] {b : ℕ} (r : R), Int.log b r = 0 := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) (2) (1 / 2)) (by
  decide +kernel)

-- Subtype.map_coe, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.map_coe.h5 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} (f : α → β) (a : Subtype p) (a : α), p a → q (f a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun n => n + 1 : ℕ → ℕ) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n = 0 }))) (by
  simp)

-- Ordnode.Valid.size_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid.size_eq.h6 : ¬∀ {α : Type} [inst : Preorder α] {s : ℕ} {l : Ordnode α} {x : α} {r : Ordnode α},
        (Ordnode.node s l x r).size = l.size + r.size + 1 := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (0) (Ordnode.nil) (0) (Ordnode.nil)) (by
  decide +kernel)

-- Finsupp.range_mapRange, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.range_mapRange.h6 : ¬∀ {α : Type} {M N : Type} [inst : Zero M] [inst_1 : Zero N] (e : M → N), e 0 = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instMulZeroClass.toZero) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- List.orderedInsert_cons_of_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.orderedInsert_cons_of_le.h6 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] {a b : α} (l : List α),
        List.orderedInsert r a (b :: l) = a :: b :: l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) (1) (0) ([])) (by
  decide +kernel)

-- Fintype.prod_congr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.prod_congr.h6 : ¬∀ {α M : Type} [inst : Fintype α] [inst_1 : CommMonoid M] (f g : α → M), ∏ a : α, f a = ∏ a : α, g a := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (BooleanRing.toCommRing.toCommMonoid) (not : Bool → Bool) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- StrictMono.sortedGE_listMap, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictMono.sortedGE_listMap.h6 : ¬∀ {α β : Type} [inst : LinearOrder α] [inst_1 : Preorder β] {f : α → β} {l : List α},
        (List.map f l).SortedGE ↔ l.SortedGE := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instPreorder) (fun _ => 0 : ℕ → ℕ) ([0, 1])) (by
  decide +kernel)

-- Matrix.diagonal_ofNat', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.diagonal_ofNat'.h6 : ¬∀ {n α : Type} [inst : DecidableEq n] [inst : Zero α] [inst : NatCast α] (m : ℕ), m.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (Nat.instMulZeroClass.toZero) (instNatCastNat) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- pow_eq_pow_iff_of_coprime, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.pow_eq_pow_iff_of_coprime.h6 : ¬∀ {α : Type} [inst : CommGroupWithZero α] {a b : α} {m n : ℕ}, a ^ m = b ^ n ↔ ∃ (c : α), a = c ^ n ∧ b = c ^ m := fun hc_h => absurd (@hc_h (ℚ) (Rat.commGroupWithZero) (0) (0) (0) (0)) (by
  simp)

-- List.orderedInsert_of_not_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.orderedInsert_of_not_le.h6 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] {a b : α} (l : List α),
        List.orderedInsert r a (b :: l) = b :: List.orderedInsert r a l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) (0) (1) ([])) (by
  decide +kernel)

-- Int.le_iff_pos_of_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.le_iff_pos_of_dvd.h2 : ¬∀ {a b : ℤ}, a ∣ b → (a ≤ b ↔ 0 < b) := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- Int.le_iff_pos_of_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.le_iff_pos_of_dvd.h3 : ¬∀ {a b : ℤ}, 0 < a → (a ≤ b ↔ 0 < b) := fun hc_h => absurd (@hc_h (2) (1) (by
  decide)) (by
  decide +kernel)

-- Set.ncard_compl_add_ncard, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_compl_add_ncard.h3 : ¬∀ {α : Type} (s : Set α), autoParam s.Finite Set.ncard_compl_add_ncard._auto_1 → sᶜ.ncard + s.ncard = Nat.card α := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Multiset.coe_foldr_swap, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.coe_foldr_swap.h3 : ¬∀ {α β : Type} (f : α → β → β) (b : β) (l : List α), LeftCommutative f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.left_comm (0 : ℕ) (1 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.iInter_subset_of_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iInter_subset_of_subset.h5 : ¬∀ {α ι : Type} {s : ι → Set α} {t : Set α} (i : ι), ⋂ (i : ι), s i ⊆ t := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun (a : ℕ) => {b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (0)) (by
  simp)

-- Finset.map_univ_of_surjective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.map_univ_of_surjective.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] {f : β ↪ α}, Finset.map f Finset.univ = Finset.univ := fun hc_h => absurd (@hc_h (Fin 3) (Bool) (Fin.fintype 3) (Bool.fintype) ({
      toFun := fun (a : Bool) =>
        if a = Bool.false then (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3)
        else (⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3),
      inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Bool ↪ Fin 3 })) (by
  decide +kernel)

-- Set.iInter_mono', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iInter_mono'.h5 : ¬∀ {α ι ι' : Type} {s : ι → Set α} {t : ι' → Set α}, ⋂ (i : ι), s i ⊆ ⋂ (j : ι'), t j := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (fun (a : ℕ) => {b : Bool | b = Bool.true}) (fun (a : ℕ) => {b : Bool | b = Bool.false})) (by
  simp)

-- Multiset.eq_of_mem_map_const, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.eq_of_mem_map_const.h5 : ¬∀ {α β : Type} {b₁ b₂ : β} {l : List α}, b₁ = b₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) (1) ([])) (by
  decide +kernel)

-- Fintype.exists_ne_map_eq_of_card_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.exists_ne_map_eq_of_card_lt.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst : Fintype β] (f : α → β), ∃ (x : α) (y : α), x ≠ y ∧ f x = f y := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype) (not : Bool → Bool)) (by
  decide +kernel)

-- Multiset.foldr_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.foldr_singleton.h3 : ¬∀ {α β : Type} (f : α → β → β) (b : β) (a : α), LeftCommutative f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.left_comm (0 : ℕ) (1 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.log_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_pos.h2 : ¬∀ {b n : ℕ}, b ≤ n → 0 < Nat.log b n := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.log_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_pos.h3 : ¬∀ {b n : ℕ}, 1 < b → 0 < Nat.log b n := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.clog_of_one_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_of_one_lt.h2 : ¬∀ {b n : ℕ}, 1 < n → Nat.clog b n = Nat.clog b ((n + b - 1) / b) + 1 := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.clog_of_one_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_of_one_lt.h3 : ¬∀ {b n : ℕ}, 1 < b → Nat.clog b n = Nat.clog b ((n + b - 1) / b) + 1 := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- EReal.toENNReal_eq_toENNReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toENNReal_eq_toENNReal.h2 : ¬∀ {x y : EReal}, 0 ≤ y → (x.toENNReal = y.toENNReal ↔ x = y) := fun hc_h => absurd (@hc_h (⊥) (0) (by
  rfl)) (by
  simp)

-- EReal.toENNReal_eq_toENNReal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toENNReal_eq_toENNReal.h3 : ¬∀ {x y : EReal}, 0 ≤ x → (x.toENNReal = y.toENNReal ↔ x = y) := fun hc_h => absurd (@hc_h (0) (⊥) (by
  rfl)) (by
  simp)

-- Nat.pow_pred_clog_lt_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_pred_clog_lt_self.h3 : ¬∀ {b : ℕ}, 1 < b → ∀ {x : ℕ}, b ^ (Nat.clog b x).pred < x := fun hc_h => absurd (@hc_h (2) (by
  decide) (0)) (by
  decide +kernel)

-- EReal.toENNReal_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toENNReal_add.h2 : ¬∀ {x y : EReal}, 0 ≤ y → (x + y).toENNReal = x.toENNReal + y.toENNReal := fun hc_h => absurd (@hc_h (⊥) (⊤) (by
  decide)) (by
  decide +kernel)

-- EReal.toENNReal_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toENNReal_add.h3 : ¬∀ {x y : EReal}, 0 ≤ x → (x + y).toENNReal = x.toENNReal + y.toENNReal := fun hc_h => absurd (@hc_h (⊤) (⊥) (by
  decide)) (by
  decide +kernel)

-- EReal.add_ne_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_ne_top.h2 : ¬∀ {x y : EReal}, y ≠ ⊤ → x + y ≠ ⊤ := fun hc_h => absurd (@hc_h (⊤) (0) (by
  decide)) (by
  decide +kernel)

-- EReal.add_ne_top, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_ne_top.h3 : ¬∀ {x y : EReal}, x ≠ ⊤ → x + y ≠ ⊤ := fun hc_h => absurd (@hc_h (0) (⊤) (by
  decide)) (by
  decide +kernel)

-- Finset.preimage_univ, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.preimage_univ.h5 : Not
      (∀ {α β : Type} {f : α → β} [inst : Fintype α] [inst : Fintype β],
        @Set.InjOn α β f (@Set.preimage α β f (@SetLike.coe (Finset β) β (@Finset.instSetLike β) (@Finset.univ β inst)))) := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ => true : Bool → Bool) (Bool.fintype) (Bool.fintype)) (by
  simp)

-- Multiset.coe_foldl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.coe_foldl.h3 : ¬∀ {α β : Type} (f : β → α → β) (b : β) (l : List α), RightCommutative f := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun (a : Bool) (n : ℕ) => n % 2 == 0) (Bool.false) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.right_comm (Bool.false : Bool) (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- EReal.add_eq_top_iff_eq_top_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_eq_top_iff_eq_top_left.h2 : ¬∀ {x y : EReal}, y ≠ ⊤ → (x + y = ⊤ ↔ x = ⊤) := fun hc_h => absurd (@hc_h (⊤) (⊥) (by
  decide)) (by
  decide +kernel)

-- EReal.add_eq_top_iff_eq_top_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_eq_top_iff_eq_top_left.h3 : ¬∀ {x y : EReal}, y ≠ ⊥ → (x + y = ⊤ ↔ x = ⊤) := fun hc_h => absurd (@hc_h (0) (⊤) (by
  decide)) (by
  decide +kernel)

-- EReal.add_ne_top_iff_ne_top_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_ne_top_iff_ne_top_left.h2 : ¬∀ {x y : EReal}, y ≠ ⊤ → (x + y ≠ ⊤ ↔ x ≠ ⊤) := fun hc_h => absurd (@hc_h (⊤) (⊥) (by
  decide)) (by
  decide +kernel)

-- EReal.add_ne_top_iff_ne_top_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_ne_top_iff_ne_top_left.h3 : ¬∀ {x y : EReal}, y ≠ ⊥ → (x + y ≠ ⊤ ↔ x ≠ ⊤) := fun hc_h => absurd (@hc_h (0) (⊤) (by
  decide)) (by
  decide +kernel)

-- EReal.add_eq_top_iff_eq_top_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_eq_top_iff_eq_top_right.h2 : ¬∀ {x y : EReal}, x ≠ ⊤ → (x + y = ⊤ ↔ y = ⊤) := fun hc_h => absurd (@hc_h (⊥) (⊤) (by
  decide)) (by
  decide +kernel)

-- EReal.add_eq_top_iff_eq_top_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_eq_top_iff_eq_top_right.h3 : ¬∀ {x y : EReal}, x ≠ ⊥ → (x + y = ⊤ ↔ y = ⊤) := fun hc_h => absurd (@hc_h (⊤) (0) (by
  decide)) (by
  decide +kernel)

-- EReal.add_ne_top_iff_ne_top_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_ne_top_iff_ne_top_right.h2 : ¬∀ {x y : EReal}, x ≠ ⊤ → (x + y ≠ ⊤ ↔ y ≠ ⊤) := fun hc_h => absurd (@hc_h (⊥) (⊤) (by
  decide)) (by
  decide +kernel)

-- EReal.add_ne_top_iff_ne_top_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_ne_top_iff_ne_top_right.h3 : ¬∀ {x y : EReal}, x ≠ ⊥ → (x + y ≠ ⊤ ↔ y ≠ ⊤) := fun hc_h => absurd (@hc_h (⊤) (0) (by
  decide)) (by
  decide +kernel)

-- EReal.neg_sub, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.neg_sub.h2 : ¬∀ {x y : EReal}, x ≠ ⊤ ∨ y ≠ ⊤ → -(x - y) = -x + y := fun hc_h => absurd (@hc_h (⊥) (⊥) (by
  decide)) (by
  decide +kernel)

-- EReal.neg_sub, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.neg_sub.h3 : ¬∀ {x y : EReal}, x ≠ ⊥ ∨ y ≠ ⊥ → -(x - y) = -x + y := fun hc_h => absurd (@hc_h (⊤) (⊤) (by
  decide)) (by
  decide +kernel)

-- EReal.add_ne_top_iff_ne_top₂, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_ne_top_iff_ne_top₂.h2 : ¬∀ {x y : EReal}, y ≠ ⊥ → (x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤) := fun hc_h => absurd (@hc_h (⊥) (⊤) (by
  decide)) (by
  decide +kernel)

-- EReal.add_ne_top_iff_ne_top₂, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_ne_top_iff_ne_top₂.h3 : ¬∀ {x y : EReal}, x ≠ ⊥ → (x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤) := fun hc_h => absurd (@hc_h (⊤) (⊥) (by
  decide)) (by
  decide +kernel)

-- Fin.succ_castPred_eq_castPred_succ, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succ_castPred_eq_castPred_succ.h2 : ¬∀ {n : ℕ} {a : Fin (n + 1)}, a ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.succ_castPred_eq_castPred_succ, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.succ_castPred_eq_castPred_succ.h3.der : ∀ {n : ℕ} {a : Fin (n + 1)}, a ≠ Fin.last n → a.succ ≠ Fin.last (n + 1) := by
  (intros; simp_all; done)
theorem HypCheckProof.Fin.succ_castPred_eq_castPred_succ.h3 : ∀ {n : ℕ} {a : Fin (n + 1)} (ha : a ≠ Fin.last n),
      (a.castPred ha).succ = a.succ.castPred (HypCheckProof.Fin.succ_castPred_eq_castPred_succ.h3.der ha) := by
  intro hc_x0 hc_x1 hc_x2
  exact @Fin.succ_castPred_eq_castPred_succ hc_x0 hc_x1 hc_x2 (@HypCheckProof.Fin.succ_castPred_eq_castPred_succ.h3.der hc_x0 hc_x1 hc_x2)

-- Fin.predAbove_zero_of_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_zero_of_ne_zero.h3 : ¬∀ {n : ℕ} [inst : NeZero n] {i : Fin (n + 1)}, i ≠ 0 := fun hc_h => absurd (@hc_h (1) _ ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- List.inter_cons_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.inter_cons_of_notMem.h5 : ¬∀ {α : Type} {l₂ : List α} {a : α} [inst : DecidableEq α] (l₁ : List α), (a :: l₁) ∩ l₂ = l₁ ∩ l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (instDecidableEqNat) ([])) (by
  decide +kernel)

-- List.le_min_of_forall_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_min_of_forall_le.h5 : ¬∀ {α : Type} [inst : LinearOrder α] [inst_1 : OrderTop α] (l : List α) (a : α), a ≤ List.foldr Min.min ⊤ l := fun hc_h => absurd (@hc_h (Bool) (Bool.linearOrder) (CompleteBooleanAlgebra.toCompleteDistribLattice.toCoframe.toCoheytingAlgebra.toOrderTop) ([Bool.false]) (Bool.true)) (by
  decide +kernel)

-- List.cons_bagInter_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_bagInter_of_notMem.h5 : ¬∀ {α : Type} {l₂ : List α} {a : α} [inst : DecidableEq α] (l₁ : List α), (a :: l₁).bagInter l₂ = l₁.bagInter l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (instDecidableEqNat) ([])) (by
  decide +kernel)

-- List.mem_union_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_union_right.h5 : ¬∀ {α : Type} {l₂ : List α} {a : α} [inst : DecidableEq α] (l₁ : List α), a ∈ l₁ ∪ l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (instDecidableEqNat) ([])) (by
  decide +kernel)

-- List.not_maximum_lt_of_mem', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_maximum_lt_of_mem'.h5 : ¬∀ {α : Type} [inst : Preorder α] [inst_1 : DecidableLT α] {l : List α} {a : α}, ¬l.maximum < ↑a := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Nat.decLt) ([]) (0)) (by
  decide +kernel)

-- EReal.div_nonneg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_nonneg.h2 : ¬∀ {a b : EReal}, 0 ≤ b → 0 ≤ a / b := fun hc_h => absurd (@hc_h (⊥) (1) (by
  simp)) (by
  simp)

-- EReal.div_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_self.h1 : ¬∀ {a : EReal}, a ≠ ⊤ → a ≠ 0 → a / a = 1 := fun hc_h => absurd (@hc_h (⊥) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.div_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_self.h2 : ¬∀ {a : EReal}, a ≠ ⊥ → a ≠ 0 → a / a = 1 := fun hc_h => absurd (@hc_h (⊤) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.div_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_self.h3 : ¬∀ {a : EReal}, a ≠ ⊥ → a ≠ ⊤ → a / a = 1 := fun hc_h => absurd (@hc_h (0) (by
  decide) (by
  decide)) (by
  simp)

-- List.Sublist.inter_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.inter_left.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {l₁ l₂ l₃ : List α}, (l₁ ∩ l₂).Sublist (l₁ ∩ l₃) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([0]) ([])) (by
  decide +kernel)

-- List.cons_bagInter_of_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_bagInter_of_neg.h5 : ¬∀ {α : Type} {l₂ : List α} {a : α} [inst : DecidableEq α] (l₁ : List α), (a :: l₁).bagInter l₂ = l₁.bagInter l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (instDecidableEqNat) ([])) (by
  decide +kernel)

-- Fin.rev_pred, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.rev_pred.h2 : ¬∀ {n : ℕ} {i : Fin (n + 1)}, i ≠ 0 := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.cons_bagInter_of_not_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_bagInter_of_not_mem.h5 : ¬∀ {α : Type} {l₂ : List α} {a : α} [inst : DecidableEq α] (l₁ : List α), (a :: l₁).bagInter l₂ = l₁.bagInter l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (instDecidableEqNat) ([])) (by
  decide +kernel)

-- List.foldr_fixed', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldr_fixed'.h4 : ¬∀ {α β : Type} {f : α → β → β} {b : β} (l : List α), List.foldr f b l = b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) ([1])) (by
  decide +kernel)

-- List.Perm.bagInter_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.bagInter_left.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) {t₁ t₂ : List α}, l.bagInter t₁ = l.bagInter t₂ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([]) ([0])) (by
  decide +kernel)

-- List.Perm.inter_append, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.inter_append.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {l t₁ t₂ : List α}, (l ∩ (t₁ ++ t₂)).Perm (l ∩ t₁ ++ l ∩ t₂) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([0]) ([0])) (by
  decide +kernel)

-- List.foldl_fixed', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldl_fixed'.h4 : ¬∀ {α β : Type} {f : α → β → α} {a : α} (l : List β), List.foldl f a l = a := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun (a : Bool) (n : ℕ) => n % 2 == 0) (Bool.false) ([0])) (by
  decide +kernel)

-- Fin.append_left_nil, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.append_left_nil.h5 : ¬∀ {m n : ℕ} {α : Type} (u : Fin m → α) (v : Fin n → α), m = 0 := fun hc_h => absurd (@hc_h (1) (0) (ℕ) (fun (a : Fin 1) => 0) (fun (a : Fin 0) => 0)) (by
  decide +kernel)

-- Fin.append_right_nil, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.append_right_nil.h5 : ¬∀ {m n : ℕ} {α : Type} (u : Fin m → α) (v : Fin n → α), n = 0 := fun hc_h => absurd (@hc_h (0) (1) (ℕ) (fun (a : Fin 0) => 0) (fun (a : Fin 1) => 0)) (by
  decide +kernel)

-- List.find?_ofFn_eq_some_of_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.find?_ofFn_eq_some_of_injective.h5 : ¬∀ {α : Type} {n : ℕ} {f : Fin n → α} {p : α → Bool} {i : Fin n},
        List.find? p (List.ofFn f) = Option.some (f i) ↔ p (f i) = Bool.true ∧ ∀ j < i, ¬p (f j) = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (2) (fun (a : Fin 2) => 0) (fun n => n % 2 == 0 : ℕ → Bool) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- List.getD_replicate, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getD_replicate.h5 : ¬∀ {α : Type} (x : α) {y : α} {i n : ℕ}, (List.replicate n x).getD i y = x := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (0) (0)) (by
  decide +kernel)

-- List.getD_append_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getD_append_right.h5 : ¬∀ {α : Type} (l l' : List α) (d : α) (n : ℕ), (l ++ l').getD n d = l'.getD (n - l.length) d := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (1) (0)) (by
  decide +kernel)

-- List.toFinsupp_apply_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.toFinsupp_apply_lt.h5 : ¬∀ {M : Type} [inst : Zero M] (l : List M) [inst : DecidablePred fun (x : ℕ) => l.getD x 0 ≠ 0] (n : ℕ), n < l.length := fun hc_h => absurd (@hc_h (ℕ) (Nat.instMulZeroClass.toZero) ([]) (fun (a : ℕ) => instDecidableNot) (0)) (by
  decide +kernel)

-- List.toFinsupp_apply_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.toFinsupp_apply_le.h5 : ¬∀ {M : Type} [inst : Zero M] (l : List M) [inst_1 : DecidablePred fun (x : ℕ) => l.getD x 0 ≠ 0] (n : ℕ),
        l.toFinsupp n = 0 := fun hc_h => absurd (@hc_h (ℕ) (Nat.instMulZeroClass.toZero) ([1]) (fun (a : ℕ) => instDecidableNot) (0)) (by
  decide +kernel)

-- Nat.binomial_succ_succ, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.binomial_succ_succ.h5 : ¬∀ {α : Type} {f : α → ℕ} {a b : α} [inst : DecidableEq α],
        Nat.multinomial {a, b} (Function.update (Function.update f a (f a).succ) b (f b).succ) =
          Nat.multinomial {a, b} (Function.update f a (f a).succ) + Nat.multinomial {a, b} (Function.update f b (f b).succ) := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (0) (instDecidableEqNat)) (by
  decide +kernel)

-- Fintype.card_subtype_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_subtype_lt.h5 : ¬∀ {α : Type} [inst : Fintype α] {p : α → Prop} [inst_1 : Fintype { a : α // p a }] {x : α},
        Fintype.card { x : α // p x } < Fintype.card α := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) (fun _ => True : Bool → Prop) (Subtype.fintype fun (x : Bool) => True) (Bool.false)) (by
  decide +kernel)

-- Nat.binomial_eq_choose, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.binomial_eq_choose.h5 : ¬∀ {α : Type} {f : α → ℕ} {a b : α} [inst : DecidableEq α], Nat.multinomial {a, b} f = (f a + f b).choose (f a) := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (0) (instDecidableEqNat)) (by
  decide +kernel)

-- Fintype.card_le_of_surjective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_le_of_surjective.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] (f : α → β), Fintype.card β ≤ Fintype.card α := fun hc_h => absurd (@hc_h (Bool) (Fin 3) (Bool.fintype) (Fin.fintype 3) (fun (a : Bool) => (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3))) (by
  decide +kernel)

-- Fintype.card_subtype_mono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_subtype_mono.h3 : ¬∀ {α : Type} (p q : α → Prop) [inst : Fintype { x : α // p x }] [inst_1 : Fintype { x : α // q x }],
        Fintype.card { x : α // p x } ≤ Fintype.card { x : α // q x } := fun hc_h => absurd (@hc_h (Bool) (fun b => b = true : Bool → Prop) (fun _ => False : Bool → Prop) (Fintype.subtypeEq Bool.true) (Subtype.fintype fun (x : Bool) => False)) (by
  decide +kernel)

-- Fintype.not_injective_of_card_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.not_injective_of_card_lt.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst : Fintype β] (f : α → β), ¬Function.Injective f := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype) (not : Bool → Bool)) (by
  decide +kernel)

-- Matrix.transpose_ofNat, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.transpose_ofNat.h5 : ¬∀ {n α : Type} [inst : DecidableEq n] [inst : AddMonoidWithOne α] (d : ℕ), d.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (Nat.instAddMonoidWithOne) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Decidable.List.eq_or_ne_mem_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Decidable.List.eq_or_ne_mem_of_mem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {a b : α} {l : List α}, a = b ∨ a ≠ b ∧ a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (1) ([])) (by
  decide +kernel)

-- List.getElem_map_rev, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_map_rev.h5 : ¬∀ {α β : Type} (f : α → β) {l : List α} {n : ℕ}, n < l.length := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ([]) (0)) (by
  decide +kernel)

-- Set.MapsTo.restrict_commutes, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.restrict_commutes.h5 : ¬∀ {α β : Type} (f : α → β) (s : Set α) (t : Set β), Set.MapsTo f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- Int.natAbs_le_of_dvd_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_le_of_dvd_ne_zero.h2 : ¬∀ {m n : ℤ}, n ≠ 0 → m.natAbs ≤ n.natAbs := fun hc_h => absurd (@hc_h (2) (1) (by
  decide)) (by
  decide +kernel)

-- Int.natAbs_le_of_dvd_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_le_of_dvd_ne_zero.h3 : ¬∀ {m n : ℤ}, m ∣ n → m.natAbs ≤ n.natAbs := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- Set.val_codRestrict_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.val_codRestrict_apply.h4 : ¬∀ {α ι : Type} (f : ι → α) (s : Set α) (x x : ι), f x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- List.IsInfix.flatMap, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsInfix.flatMap.h4 : ¬∀ {α β : Type} {l₁ l₂ : List α} (f : α → List β), List.flatMap f l₁ <:+: List.flatMap f l₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0]) ([]) (fun n => [n] : ℕ → List ℕ)) (by
  decide +kernel)

-- List.insertionSort_cons_of_forall_rel, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.insertionSort_cons_of_forall_rel.h5 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] {a : α} {l : List α},
        List.insertionSort r (a :: l) = a :: List.insertionSort r l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) (1) ([0])) (by
  decide +kernel)

-- Set.MapsTo.restrict_eq_codRestrict, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.restrict_eq_codRestrict.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.MapsTo f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.preimage_subset_image_of_inverse, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.preimage_subset_image_of_inverse.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α} (s : Set β), f ⁻¹' s ⊆ g '' s := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n % 2 == 0 : ℕ → Bool) ({n : ℕ | n = 0})) (by
  simp)

-- List.flatMap_congr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.flatMap_congr.h5 : ¬∀ {α β : Type} {l : List α} {f g : α → List β}, List.flatMap f l = List.flatMap g l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0]) (fun _ => [] : ℕ → List ℕ) (fun n => [n] : ℕ → List ℕ)) (by
  decide +kernel)

-- List.SortedLT.coe_getIso_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.coe_getIso_apply.h4 : ¬∀ {α : Type} [inst : Preorder α] {l : List α} [inst_1 : DecidableEq α] {i : Fin l.length}, l.SortedLT := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) ([1, 0]) (instDecidableEqNat) (0)) (by
  decide +kernel)

-- List.destutter'_of_isChain_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.destutter'_of_isChain_cons.h5 : ¬∀ {α : Type} (l : List α) (R : α → α → Prop) [inst : DecidableRel R] {a : α}, List.destutter' R a l = a :: l := fun hc_h => absurd (@hc_h (ℕ) ([0]) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) (0)) (by
  decide +kernel)

-- Prod.snd_ofNat, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.snd_ofNat.h5 : ¬∀ {α β : Type} [inst : AddMonoidWithOne α] [inst : AddMonoidWithOne β] (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instAddMonoidWithOne) (Nat.instAddMonoidWithOne) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Prod.fst_ofNat, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.fst_ofNat.h5 : ¬∀ {α β : Type} [inst : AddMonoidWithOne α] [inst : AddMonoidWithOne β] (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instAddMonoidWithOne) (Nat.instAddMonoidWithOne) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Bool.and_intro, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.and_intro.h2 : ¬∀ {a b : Bool}, b = Bool.true → (a && b) = Bool.true := fun hc_h => absurd (@hc_h (Bool.false) _ rfl) (by
  decide +kernel)

-- Bool.and_intro, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.and_intro.h3 : ¬∀ {a b : Bool}, a = Bool.true → (a && b) = Bool.true := fun hc_h => absurd (@hc_h _ (Bool.false) rfl) (by
  decide +kernel)

-- WithZeroMulInt.toNNReal_eq_one_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithZeroMulInt.toNNReal_eq_one_iff.h2 : ¬∀ {e : NNReal} (m : WithZero (Multiplicative ℤ)), e ≠ 1 → e ≠ 0 := fun hc_h => absurd (@hc_h (0) (0) (by
  simp)) (by
  simp)

-- Set.Finite.exists_notMem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.exists_notMem.h2 : ¬∀ {α : Type} {s : Set α}, s.Finite → ∃ (a : α), a ∉ s := fun hc_h => absurd (@hc_h (Bool) ({x : Bool | True}) (by
  simp)) (by
  decide +kernel)

-- Set.Finite.exists_notMem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.exists_notMem.h3 : ¬∀ {α : Type} {s : Set α} [inst : Infinite α], ∃ (a : α), a ∉ s := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True}) _) (by
  simp)

-- ZMod.intCast_val_inv_mul, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.intCast_val_inv_mul.h1 : Not
      (∀ {n : Nat} {m : Int},
        @IsCoprime Int Int.instCommSemiring m (@Nat.cast Int instNatCastInt n) →
          @Eq (ZMod n)
            (@HMul.hMul (ZMod n) (ZMod n) (ZMod n)
              (@instHMul (ZMod n)
                (@Distrib.toMul (ZMod n)
                  (@instDistribOfSemiring (ZMod n)
                    (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))))
              (@Nat.cast (ZMod n)
                (@AddMonoidWithOne.toNatCast (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
                (@ZMod.val n
                  (@Inv.inv (ZMod n) (ZMod.instInv n)
                    (@Int.cast (ZMod n)
                      (@AddGroupWithOne.toIntCast (ZMod n)
                        (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
                      m))))
              (@Int.cast (ZMod n)
                (@AddGroupWithOne.toIntCast (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
                m))
            (@OfNat.ofNat (ZMod n) (nat_lit 1)
              (@One.toOfNat1 (ZMod n)
                (@AddMonoidWithOne.toOne (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  decide)) (by
  decide +kernel)

-- ZMod.intCast_val_inv_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.intCast_val_inv_mul.h3 : Not
      (∀ {n : Nat} [inst : @NeZero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) n] {m : Int},
        @Eq (ZMod n)
          (@HMul.hMul (ZMod n) (ZMod n) (ZMod n)
            (@instHMul (ZMod n)
              (@Distrib.toMul (ZMod n)
                (@instDistribOfSemiring (ZMod n)
                  (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))))
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              (@ZMod.val n
                (@Inv.inv (ZMod n) (ZMod.instInv n)
                  (@Int.cast (ZMod n)
                    (@AddGroupWithOne.toIntCast (ZMod n)
                      (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
                    m))))
            (@Int.cast (ZMod n)
              (@AddGroupWithOne.toIntCast (ZMod n)
                (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
              m))
          (@OfNat.ofNat (ZMod n) (nat_lit 1)
            (@One.toOfNat1 (ZMod n)
              (@AddMonoidWithOne.toOne (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- ZMod.unitsMap_surjective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.unitsMap_surjective.h3 : ¬∀ {n m : ℕ} [hm : NeZero m], n ∣ m := fun hc_h => absurd (@hc_h (0) (1) _) (by
  decide +kernel)

-- Finsupp.uniqueEquiv_symm_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.uniqueEquiv_symm_apply.h4 : ¬∀ {α M : Type} [inst : Zero M] (a : α) (b : M), Subsingleton α := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.LeftInverse.preimage_preimage, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.preimage_preimage.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α} (s : Set α), f ⁻¹' g ⁻¹' s = s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Finsupp.support_single, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.support_single.h5 : ¬∀ {α M : Type} [inst : Zero M] {b : M} (a : α), (fun₀ | a => b).support = {a} := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (0) (0)) (by
  simp)

-- Finsupp.support_single_ne_zero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.support_single_ne_zero.h5 : ¬∀ {α M : Type} [inst : Zero M] {b : M} (a : α), (fun₀ | a => b).support = {a} := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (0) (0)) (by
  simp)

-- List.perm_eraseIdx_of_getElem?_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.perm_eraseIdx_of_getElem?_eq.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} {m n : ℕ}, (l₁.eraseIdx m).Perm (l₂.eraseIdx n) ↔ l₁.Perm l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (0) (0)) (by
  decide +kernel)

-- List.Perm.product_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.product_left.h5 : ¬∀ {α β : Type} (l : List α) {t₁ t₂ : List β}, (l.product t₁).Perm (l.product t₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0]) ([]) ([0])) (by
  decide +kernel)

-- Set.card_lt_card, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.card_lt_card.h5 : ¬∀ {α : Type} {s t : Set α} [inst : Fintype ↑s] [inst_1 : Fintype ↑t], Fintype.card ↑s < Fintype.card ↑t := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.true})) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.true}))) (by
  decide +kernel)

-- Set.sups_subset_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sups_subset_right.h5 : Not
      (∀ {α : Type} [inst : SemilatticeSup α] {s₁ s₂ t : Set α},
        @LE.le (Set α) (@Set.instLE α) (@HasSups.sups (Set α) (@Set.hasSups α inst) s₁ t)
          (@HasSups.sups (Set α) (@Set.hasSups α inst) s₂ t)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (x : Nat) => False) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (by
  simp)

-- Set.infs_subset_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infs_subset_right.h5 : Not
      (∀ {α : Type} [inst : SemilatticeInf α] {s₁ s₂ t : Set α},
        @LE.le (Set α) (@Set.instLE α) (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s₁ t)
          (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s₂ t)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (x : Nat) => False) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (by
  simp)

-- Option.mem_map_of_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.mem_map_of_injective.h3 : ¬∀ {α β : Type} {f : α → β} {a : α} {o : Option α}, f a ∈ Option.map f o ↔ a ∈ o := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (0) (Option.some 1)) (by
  decide +kernel)

-- List.Perm.product_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.product_right.h5 : ¬∀ {α β : Type} {l₁ l₂ : List α} (t₁ : List β), (l₁.product t₁).Perm (l₂.product t₁) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([]) ([0]) ([0])) (by
  decide +kernel)

-- Nat.cast_max, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.cast_max.h3 : Not
      (∀ {α : Type} [inst : Semiring α] [inst_1 : LinearOrder α] (m n : Nat),
        @Eq α
          (@Nat.cast α
            (@AddMonoidWithOne.toNatCast α
              (@AddCommMonoidWithOne.toAddMonoidWithOne α
                (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
            (@Max.max Nat Nat.instMax m n))
          (@Max.max α
            (@SemilatticeSup.toMax α
              (@Lattice.toSemilatticeSup α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))
            (@Nat.cast α
              (@AddMonoidWithOne.toNatCast α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
              m)
            (@Nat.cast α
              (@AddMonoidWithOne.toNatCast α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
              n))) := fun hc_h => absurd (@hc_h (Bool) (@CommSemiring.toSemiring Bool (@CommRing.toCommSemiring Bool (@BooleanRing.toCommRing Bool instBooleanRingBool))) (Bool.linearOrder) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (by
  decide +kernel)

-- Nat.choose_eq_choose_pred_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_eq_choose_pred_add.h2 : ¬∀ {n k : ℕ}, 0 < k → n.choose k = (n - 1).choose (k - 1) + (n - 1).choose k := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.choose_eq_choose_pred_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_eq_choose_pred_add.h3 : ¬∀ {n k : ℕ}, 0 < n → n.choose k = (n - 1).choose (k - 1) + (n - 1).choose k := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- Finsupp.comapDomain_surjective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.comapDomain_surjective.h5 : ¬∀ {α β M : Type} [inst : Zero M] {f : α → β}, Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- List.takeD_left', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.takeD_left'.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} {n : ℕ} {a : α}, List.takeD n (l₁ ++ l₂) a = l₁ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (1) (0)) (by
  decide +kernel)

-- List.takeI_left', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.takeI_left'.h5 : ¬∀ {α : Type} [inst : Inhabited α] {l₁ l₂ : List α} {n : ℕ}, List.takeI n (l₁ ++ l₂) = l₁ := fun hc_h => absurd (@hc_h (ℕ) (instInhabitedNat) ([]) ([]) (1)) (by
  decide +kernel)

-- Nat.bitwise_bit, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bitwise_bit.h1 : ¬∀ {f : Bool → Bool → Bool} (a : Bool) (m : ℕ) (b : Bool) (n : ℕ),
        Nat.bitwise f (Nat.bit a m) (Nat.bit b n) = Nat.bit (f a b) (Nat.bitwise f m n) := fun hc_h => absurd (@hc_h (fun a b => !a || b : Bool → Bool → Bool) (Bool.false) (0) (Bool.false) (0)) (by
  decide +kernel)

-- Num.cast_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Num.cast_lt.h3 : Not
      (∀ {α : Type} [inst : Semiring α] [inst_1 : PartialOrder α] {m n : Num},
        Iff
          (@LT.lt α (@Preorder.toLT α (@PartialOrder.toPreorder α inst_1))
            (@castNum α
              (@AddMonoidWithOne.toOne α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
              (@Distrib.toAdd α (@instDistribOfSemiring α inst))
              (@MulZeroClass.toZero α (@instMulZeroClassOfSemiring α inst)) m)
            (@castNum α
              (@AddMonoidWithOne.toOne α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
              (@Distrib.toAdd α (@instDistribOfSemiring α inst))
              (@MulZeroClass.toZero α (@instMulZeroClassOfSemiring α inst)) n))
          (@LT.lt Num Num.instLT m n)) := fun hc_h => absurd (@hc_h (Bool) (@CommSemiring.toSemiring Bool (@CommRing.toCommSemiring Bool (@BooleanRing.toCommRing Bool instBooleanRingBool))) (Bool.instPartialOrder) (Num.zero) (Num.pos PosNum.one.bit0)) (by
  decide +kernel)

-- Num.cast_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Num.cast_le.h3 : Not
      (∀ {α : Type} [inst : Semiring α] [inst_1 : LinearOrder α] {m n : Num},
        Iff
          (@LE.le α
            (@Preorder.toLE α
              (@PartialOrder.toPreorder α
                (@SemilatticeInf.toPartialOrder α
                  (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
            (@castNum α
              (@AddMonoidWithOne.toOne α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
              (@Distrib.toAdd α (@instDistribOfSemiring α inst))
              (@MulZeroClass.toZero α (@instMulZeroClassOfSemiring α inst)) m)
            (@castNum α
              (@AddMonoidWithOne.toOne α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
              (@Distrib.toAdd α (@instDistribOfSemiring α inst))
              (@MulZeroClass.toZero α (@instMulZeroClassOfSemiring α inst)) n))
          (@LE.le Num Num.instLE m n)) := fun hc_h => absurd (@hc_h (Bool) (@CommSemiring.toSemiring Bool (@CommRing.toCommSemiring Bool (@BooleanRing.toCommRing Bool instBooleanRingBool))) (Bool.linearOrder) (Num.pos PosNum.one.bit1) (Num.pos PosNum.one)) (by
  decide +kernel)

-- PosNum.cast_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PosNum.cast_lt.h3 : Not
      (∀ {α : Type} [inst : Semiring α] [inst_1 : PartialOrder α] {m n : PosNum},
        Iff
          (@LT.lt α (@Preorder.toLT α (@PartialOrder.toPreorder α inst_1))
            (@castPosNum α
              (@AddMonoidWithOne.toOne α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
              (@Distrib.toAdd α (@instDistribOfSemiring α inst)) m)
            (@castPosNum α
              (@AddMonoidWithOne.toOne α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
              (@Distrib.toAdd α (@instDistribOfSemiring α inst)) n))
          (@LT.lt PosNum PosNum.instLT m n)) := fun hc_h => absurd (@hc_h (Bool) (@CommSemiring.toSemiring Bool (@CommRing.toCommSemiring Bool (@BooleanRing.toCommRing Bool instBooleanRingBool))) (Bool.instPartialOrder) (PosNum.one) (PosNum.one.bit1)) (by
  decide +kernel)

-- Num.cast_inj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Num.cast_inj.h3 : Not
      (∀ {α : Type} [inst : Semiring α] [inst_1 : PartialOrder α] {m n : Num},
        Iff
          (@Eq α
            (@castNum α
              (@AddMonoidWithOne.toOne α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
              (@Distrib.toAdd α (@instDistribOfSemiring α inst))
              (@MulZeroClass.toZero α (@instMulZeroClassOfSemiring α inst)) m)
            (@castNum α
              (@AddMonoidWithOne.toOne α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
              (@Distrib.toAdd α (@instDistribOfSemiring α inst))
              (@MulZeroClass.toZero α (@instMulZeroClassOfSemiring α inst)) n))
          (@Eq Num m n)) := fun hc_h => absurd (@hc_h (Bool) (@CommSemiring.toSemiring Bool (@CommRing.toCommSemiring Bool (@BooleanRing.toCommRing Bool instBooleanRingBool))) (Bool.instPartialOrder) (Num.zero) (Num.pos PosNum.one.bit0)) (by
  decide +kernel)

-- List.IsChain.count_not_eq_count, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.count_not_eq_count.h1 : ¬∀ {l : List Bool}, Even l.length → ∀ (b : Bool), List.count (!b) l = List.count b l := fun hc_h => absurd (@hc_h ([Bool.false, Bool.false]) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- List.IsChain.count_not_eq_count, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.count_not_eq_count.h2 : ¬∀ {l : List Bool}, List.IsChain (fun (x1 x2 : Bool) => x1 ≠ x2) l → ∀ (b : Bool), List.count (!b) l = List.count b l := fun hc_h => absurd (@hc_h ([Bool.false]) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- Nat.exists_prime_and_dvd_and_dvd_div, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_prime_and_dvd_and_dvd_div.h2 : ¬∀ {m n : ℕ}, m ≠ n → ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ m ∣ n / p := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  (simp <;> omega))

-- Nat.exists_prime_and_dvd_and_dvd_div, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_prime_and_dvd_and_dvd_div.h3 : ¬∀ {m n : ℕ}, m ∣ n → ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ m ∣ n / p := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  (simp <;> decide))

-- Nat.Prime.eq_one_or_self_of_dvd, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.eq_one_or_self_of_dvd.h1 : ¬∀ {p : ℕ} (m : ℕ), m ∣ p → m = 1 ∨ m = p := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.eq_one_or_self_of_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.eq_one_or_self_of_dvd.h3 : ¬∀ {p : ℕ}, Nat.Prime p → ∀ (m : ℕ), m = 1 ∨ m = p := fun hc_h => absurd (@hc_h (2) (by
  decide) (0)) (by
  decide +kernel)

-- AddCommGroup.intCast_modEq_intCast', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.AddCommGroup.intCast_modEq_intCast'.h2 : Not
      (∀ {G : Type} [inst : AddCommGroupWithOne G] {a b : Int} {n : Nat},
        Iff
          (@AddCommGroup.ModEq G
            (@AddCommMonoidWithOne.toAddCommMonoid G (@AddCommGroupWithOne.toAddCommMonoidWithOne G inst))
            (@Nat.cast G
              (@AddMonoidWithOne.toNatCast G
                (@AddGroupWithOne.toAddMonoidWithOne G (@AddCommGroupWithOne.toAddGroupWithOne G inst)))
              n)
            (@Int.cast G (@AddGroupWithOne.toIntCast G (@AddCommGroupWithOne.toAddGroupWithOne G inst)) a)
            (@Int.cast G (@AddGroupWithOne.toIntCast G (@AddCommGroupWithOne.toAddGroupWithOne G inst)) b))
          (@AddCommGroup.ModEq Int Int.instAddCommMonoid (@Nat.cast Int instNatCastInt n) a b)) := fun hc_h => absurd (@hc_h (Unit) (@NonAssocRing.toAddCommGroupWithOne Unit
      (@NonAssocCommRing.toNonAssocRing Unit (@CommRing.toNonAssocCommRing Unit PUnit.commRing))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  norm_num)

-- List.lookmap_map_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lookmap_map_eq.h4 : ¬∀ {α β : Type} (f : α → Option α) (g : α → β) (l : List α), List.map g (List.lookmap f l) = List.map g l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => some (n + 1) : ℕ → Option ℕ) (fun n => n + 1 : ℕ → ℕ) ([0])) (by
  decide +kernel)

-- List.lookmap_cons_some, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lookmap_cons_some.h5 : ¬∀ {α : Type} (f : α → Option α) {a b : α} (l : List α), List.lookmap f (a :: l) = b :: l := fun hc_h => absurd (@hc_h (ℕ) (fun _ => none : ℕ → Option ℕ) (0) (1) ([])) (by
  decide +kernel)

-- Rat.divInt_ne_zero_of_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.divInt_ne_zero_of_ne_zero.h2 : ¬∀ {n d : ℤ}, d ≠ 0 → Rat.divInt n d ≠ 0 := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Rat.divInt_ne_zero_of_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.divInt_ne_zero_of_ne_zero.h3 : ¬∀ {n d : ℤ}, n ≠ 0 → Rat.divInt n d ≠ 0 := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.notMem_keys_kerase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.notMem_keys_kerase.h5 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] (a : α) {l : List (Sigma β)}, a ∉ (List.kerase a l).keys := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ), (⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  decide +kernel)

-- List.kerase_of_notMem_keys, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.kerase_of_notMem_keys.h5 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {l : List (Sigma β)}, List.kerase a l = l := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  decide +kernel)

-- Nat.Prime.dvd_iff_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_iff_eq.h2 : ¬∀ {p a : ℕ}, a ≠ 1 → (a ∣ p ↔ p = a) := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_iff_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_iff_eq.h3 : ¬∀ {p a : ℕ}, Nat.Prime p → (a ∣ p ↔ p = a) := fun hc_h => absurd (@hc_h (2) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.gcd_eq_one_of_lt_minFac, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.gcd_eq_one_of_lt_minFac.h2 : ¬∀ {n m : ℕ}, m < n.minFac → n.gcd m = 1 := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.gcd_eq_one_of_lt_minFac, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.gcd_eq_one_of_lt_minFac.h3 : ¬∀ {n m : ℕ}, m ≠ 0 → n.gcd m = 1 := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.forall_prime_of_two_of_odd, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.forall_prime_of_two_of_odd.h1 : ¬∀ {P : ℕ → Prop} (p : ℕ), Nat.Prime p → P p := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (2) (by
  decide)) (by
  decide +kernel)

-- List.sizeOf_cons_le_sizeOf_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sizeOf_cons_le_sizeOf_cons.h5 : ¬∀ {α : Type} [inst : SizeOf α] {l r : List α} (a : α), SizeOf.sizeOf (a :: l) ≤ SizeOf.sizeOf (a :: r) := fun hc_h => absurd (@hc_h (ℕ) (instSizeOfNat) ([0]) ([]) (0)) (by
  decide +kernel)

-- Nat.primeFactorsList_subset_of_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactorsList_subset_of_dvd.h2 : ¬∀ {n k : ℕ}, k ≠ 0 → n.primeFactorsList ⊆ k.primeFactorsList := fun hc_h => absurd (@hc_h (2) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.primeFactorsList_subset_of_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactorsList_subset_of_dvd.h3 : ¬∀ {n k : ℕ}, n ∣ k → n.primeFactorsList ⊆ k.primeFactorsList := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.eq_prime_pow_of_unique_prime_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_prime_pow_of_unique_prime_dvd.h3 : ¬∀ {n p : ℕ}, n ≠ 0 → n = p ^ n.primeFactorsList.length := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- ZMod.val_ofNat_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.val_ofNat_of_lt.h2 : ¬∀ {n a : ℕ}, a < n → a.AtLeastTwo := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ZMod.val_ofNat_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.val_ofNat_of_lt.h3 : Not
      (∀ {n a : Nat} [inst : a.AtLeastTwo],
        @Eq Nat
          (@ZMod.val n
            (@OfNat.ofNat (ZMod n) a
              (@instOfNatAtLeastTwo (ZMod n) a
                (@AddMonoidWithOne.toNatCast (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
                inst)))
          (@OfNat.ofNat Nat a (instOfNatNat a))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) _) (by
  decide +kernel)

-- Nat.choose_lt_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_lt_pow.h2 : ¬∀ {n k : ℕ}, 2 ≤ k → n.choose k < n ^ k := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.choose_lt_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_lt_pow.h3 : ¬∀ {n k : ℕ}, n ≠ 0 → n.choose k < n ^ k := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- PNat.dvd_antisymm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.dvd_antisymm.h2 : ¬∀ {m n : ℕ+}, n ∣ m → m = n := fun hc_h => absurd (@hc_h (2) (1) (by
  simp)) (by
  decide +kernel)

-- PNat.dvd_antisymm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.dvd_antisymm.h3 : ¬∀ {m n : ℕ+}, m ∣ n → m = n := fun hc_h => absurd (@hc_h (1) (2) (by
  simp)) (by
  decide +kernel)

-- Holor.slice_zero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Holor.slice_zero.h5 : ¬∀ {α : Type} {d : ℕ} {ds : List ℕ} [inst : Zero α] (i : ℕ), i < d := fun hc_h => absurd (@hc_h (ℕ) (0) ([]) (Nat.instMulZeroClass.toZero) (0)) (by
  decide +kernel)

-- Int.natAbs_inj_of_nonpos_of_nonpos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_inj_of_nonpos_of_nonpos.h2 : ¬∀ {a b : ℤ}, b ≤ 0 → (a.natAbs = b.natAbs ↔ a = b) := fun hc_h => absurd (@hc_h (1) (-1) (by
  decide)) (by
  decide +kernel)

-- Int.natAbs_inj_of_nonpos_of_nonpos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_inj_of_nonpos_of_nonpos.h3 : ¬∀ {a b : ℤ}, a ≤ 0 → (a.natAbs = b.natAbs ↔ a = b) := fun hc_h => absurd (@hc_h (-1) (1) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.card_eq_countP, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.card_eq_countP.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {P : α → Prop} [inst_1 : DecidablePred P],
        (Finset.filter P l.toFinset).card = List.countP (fun (b : α) => Decidable.decide (P b)) l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0, 0]) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0)) (by
  decide +kernel)

-- Int.natAbs_inj_of_nonpos_of_nonneg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_inj_of_nonpos_of_nonneg.h2 : ¬∀ {a b : ℤ}, 0 ≤ b → (a.natAbs = b.natAbs ↔ -a = b) := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  decide +kernel)

-- Int.natAbs_inj_of_nonpos_of_nonneg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_inj_of_nonpos_of_nonneg.h3 : ¬∀ {a b : ℤ}, a ≤ 0 → (a.natAbs = b.natAbs ↔ -a = b) := fun hc_h => absurd (@hc_h (-1) (-1) (by
  decide)) (by
  decide +kernel)

-- Int.natAbs_inj_of_nonneg_of_nonpos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_inj_of_nonneg_of_nonpos.h2 : ¬∀ {a b : ℤ}, b ≤ 0 → (a.natAbs = b.natAbs ↔ a = -b) := fun hc_h => absurd (@hc_h (-1) (-1) (by
  decide)) (by
  decide +kernel)

-- Int.natAbs_inj_of_nonneg_of_nonpos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_inj_of_nonneg_of_nonpos.h3 : ¬∀ {a b : ℤ}, 0 ≤ a → (a.natAbs = b.natAbs ↔ a = -b) := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  decide +kernel)

-- Int.natAbs_inj_of_nonneg_of_nonneg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_inj_of_nonneg_of_nonneg.h2 : ¬∀ {a b : ℤ}, 0 ≤ b → (a.natAbs = b.natAbs ↔ a = b) := fun hc_h => absurd (@hc_h (-1) (1) (by
  decide)) (by
  decide +kernel)

-- Int.natAbs_inj_of_nonneg_of_nonneg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_inj_of_nonneg_of_nonneg.h3 : ¬∀ {a b : ℤ}, 0 ≤ a → (a.natAbs = b.natAbs ↔ a = b) := fun hc_h => absurd (@hc_h (1) (-1) (by
  decide)) (by
  decide +kernel)

-- Nat.digits_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_of_lt.h2 : ¬∀ (b x : ℕ), x < b → b.digits x = [x] := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.digits_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_of_lt.h3 : ¬∀ (b x : ℕ), x ≠ 0 → b.digits x = [x] := fun hc_h => absurd (@hc_h (1) (2) (by
  decide)) (by
  decide +kernel)

-- Int.Prime.dvd_natAbs_of_coe_dvd_sq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.Prime.dvd_natAbs_of_coe_dvd_sq.h3 : ¬∀ {p : ℕ}, Nat.Prime p → ∀ (k : ℤ), p ∣ k.natAbs := fun hc_h => absurd (@hc_h (2) (by
  decide) (1)) (by
  decide +kernel)

-- List.foldr_flip_eq_foldl, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldr_flip_eq_foldl.h5 : ¬∀ {α β : Type} {l : List α} {v : β → α → β} {b : β}, List.foldr (flip v) b l = List.foldl v b l := fun hc_h => absurd (@hc_h (ℕ) (Bool) ([0, 1]) (fun (a : Bool) (n : ℕ) => n % 2 == 0) (Bool.false)) (by
  decide +kernel)

-- List.foldl1_eq_foldr1, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldl1_eq_foldr1.h3 : ¬∀ {α : Type} {l : List α} {f : α → α → α} {a b : α}, f (List.foldl f a l) b = f a (List.foldr f b l) := fun hc_h => absurd (@hc_h (Bool) ([Bool.false]) (fun a b => !a || b : Bool → Bool → Bool) (Bool.false) (Bool.false)) (by
  decide +kernel)

-- List.foldl_flip_eq_foldr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldl_flip_eq_foldr.h5 : ¬∀ {α β : Type} {l : List α} {f : α → β → β} {b : β}, List.foldl (flip f) b l = List.foldr f b l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0, 1]) (fun a b => a - b : ℕ → ℕ → ℕ) (0)) (by
  decide +kernel)

-- Nat.digitsAux_def, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digitsAux_def.h1 : ¬∀ (b n : ℕ), 0 < n → 2 ≤ b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.digitsAux_def, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digitsAux_def.h3 : ¬∀ (b : ℕ) (h : 2 ≤ b) (n : ℕ), b.digitsAux h n = n % b :: b.digitsAux h (n / b) := fun hc_h => absurd (fun hc_k0 => @hc_h (2) hc_k0 (0)) (by
  decide +kernel)

-- Nat.digits_base_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_base_mul.h2 : ¬∀ {b m : ℕ}, 0 < m → b.digits (b * m) = 0 :: b.digits m := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.digits_base_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_base_mul.h3 : ¬∀ {b m : ℕ}, 1 < b → b.digits (b * m) = 0 :: b.digits m := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Set.SurjOn.exists_bijOn_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.exists_bijOn_subset.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, ∃ s' ⊆ s, Set.BijOn f s' t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- PNat.mk_le_mk, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.mk_le_mk.h2 : ¬∀ (n k : ℕ), 0 < k → 0 < n := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- PNat.mk_le_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.mk_le_mk.h3 : ¬∀ (n k : ℕ), 0 < n → 0 < k := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.splitBy_append_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.splitBy_append_cons.h5 : ¬∀ {α : Type} {r : α → α → Bool} {l : List α} {a : α} (m : List α),
        List.splitBy r (l ++ a :: m) = List.splitBy r l ++ List.splitBy r (a :: m) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Bool) ([0]) (1) ([])) (by
  decide +kernel)

-- multiplicity_base_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.multiplicity_base_mul.h2 : ¬∀ {p n : ℕ}, n ≠ 0 → multiplicity p (p * n) = multiplicity p n + 1 := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  simp)

-- Rat.num_div_eq_of_coprime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.num_div_eq_of_coprime.h2 : Not
      (∀ {a b : Int},
        a.natAbs.Coprime b.natAbs →
          @Eq Int
            (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast a)
                (@Int.cast Rat Rat.instIntCast b)).num
            a) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Rat.num_div_eq_of_coprime, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.num_div_eq_of_coprime.h3 : Not
      (∀ {a b : Int},
        @LT.lt Int Int.instLTInt (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) b →
          @Eq Int
            (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast a)
                (@Int.cast Rat Rat.instIntCast b)).num
            a) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Nat.pow_succ_factorization_not_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_succ_factorization_not_dvd.h2 : ¬∀ {n p : ℕ}, Nat.Prime p → ¬p ^ (n.factorization p + 1) ∣ n := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.pow_succ_factorization_not_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_succ_factorization_not_dvd.h3 : ¬∀ {n p : ℕ}, n ≠ 0 → ¬p ^ (n.factorization p + 1) ∣ n := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.exists_factorization_lt_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_factorization_lt_of_lt.h2 : ¬∀ {a b : ℕ}, a < b → ∃ (p : ℕ), a.factorization p < b.factorization p := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- Nat.exists_factorization_lt_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_factorization_lt_of_lt.h3 : ¬∀ {a b : ℕ}, a ≠ 0 → ∃ (p : ℕ), a.factorization p < b.factorization p := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  simp)

-- Nat.factorization_prime_le_iff_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_prime_le_iff_dvd.h2 : ¬∀ {d n : ℕ}, n ≠ 0 → ((∀ (p : ℕ), Nat.Prime p → d.factorization p ≤ n.factorization p) ↔ d ∣ n) := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- Nat.ordCompl_div_of_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordCompl_div_of_dvd.h3 : ¬∀ {x p : ℕ}, Nat.Prime p → x / p / p ^ (x / p).factorization p = x / p ^ x.factorization p := fun hc_h => absurd (@hc_h (1) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.exists_lt_card_finite_nth_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_lt_card_finite_nth_eq.h3 : ¬∀ {p : ℕ → Prop} (hf : (Set.ofPred p).Finite) {x : ℕ}, ∃ n < hf.toFinset.card, Nat.nth p n = x := fun hc_h => absurd (fun hc_k0 => @hc_h (fun n => n = 0 : ℕ → Prop) hc_k0 (1)) (by
  simp)

-- Nat.prod_pow_prime_multiplicity, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prod_pow_prime_multiplicity.h1 : ¬∀ (n m : ℕ), n < m → ∏ p ∈ Finset.range m with Nat.Prime p, p ^ multiplicity p n = n := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.prod_pow_prime_multiplicity, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prod_pow_prime_multiplicity.h3 : ¬∀ (n : ℕ), n ≠ 0 → ∀ (m : ℕ), ∏ p ∈ Finset.range m with Nat.Prime p, p ^ multiplicity p n = n := fun hc_h => absurd (@hc_h (2) (by
  decide) (0)) (by
  decide +kernel)

-- Set.mk_preimage_prod_left_eq_empty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mk_preimage_prod_left_eq_empty.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {b : β}, (fun (a : α) => (a, b)) ⁻¹' s ×ˢ t = ∅ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n % 2 = 0}) (0)) (by
  simp)

-- Nat.dvd_iff_div_factorization_eq_tsub, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_iff_div_factorization_eq_tsub.h2 : ¬∀ {d n : ℕ}, d ≤ n → (d ∣ n ↔ (n / d).factorization = n.factorization - d.factorization) := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Subtype.val_comp_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.val_comp_map.h5 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} {f : α → β} (a : α), p a → q (f a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.BijOn.image_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.image_eq.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, f '' s = t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Nat.findGreatest_mono_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.findGreatest_mono_left.h4 : ¬∀ {P Q : ℕ → Prop} [inst : DecidablePred P] [inst_1 : DecidablePred Q] (n : ℕ),
        Nat.findGreatest P n ≤ Nat.findGreatest Q n := fun hc_h => absurd (@hc_h (fun n => n % 2 = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat (a % 2) 0) (fun (a : ℕ) => instDecidableEqNat a 0) (2)) (by
  decide +kernel)

-- Nat.isLeast_nth_of_lt_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.isLeast_nth_of_lt_card.h3 : ¬∀ {p : ℕ → Prop} {n : ℕ}, (Set.ofPred p).Finite → IsLeast {i : ℕ | p i ∧ ∀ k < n, Nat.nth p k < i} (Nat.nth p n) := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (0) (by
  simp)) (by
  decide +kernel)

-- ZNum.cast_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZNum.cast_lt.h3 : Not
      (∀ {α : Type} [inst : Ring α] [inst_1 : PartialOrder α] {m n : ZNum},
        Iff
          (@LT.lt α (@Preorder.toLT α (@PartialOrder.toPreorder α inst_1))
            (@castZNum α (@MulZeroClass.toZero α (@instMulZeroClassOfSemiring α (@Ring.toSemiring α inst)))
              (@AddMonoidWithOne.toOne α (@AddGroupWithOne.toAddMonoidWithOne α (@Ring.toAddGroupWithOne α inst)))
              (@Distrib.toAdd α (@instDistribOfSemiring α (@Ring.toSemiring α inst)))
              (@NegZeroClass.toNeg α
                (@SubNegZeroMonoid.toNegZeroClass α
                  (@SubtractionMonoid.toSubNegZeroMonoid α
                    (@SubtractionCommMonoid.toSubtractionMonoid α
                      (@AddCommGroup.toDivisionAddCommMonoid α (@Ring.toAddCommGroup α inst))))))
              m)
            (@castZNum α (@MulZeroClass.toZero α (@instMulZeroClassOfSemiring α (@Ring.toSemiring α inst)))
              (@AddMonoidWithOne.toOne α (@AddGroupWithOne.toAddMonoidWithOne α (@Ring.toAddGroupWithOne α inst)))
              (@Distrib.toAdd α (@instDistribOfSemiring α (@Ring.toSemiring α inst)))
              (@NegZeroClass.toNeg α
                (@SubNegZeroMonoid.toNegZeroClass α
                  (@SubtractionMonoid.toSubNegZeroMonoid α
                    (@SubtractionCommMonoid.toSubtractionMonoid α
                      (@AddCommGroup.toDivisionAddCommMonoid α (@Ring.toAddCommGroup α inst))))))
              n))
          (@LT.lt ZNum ZNum.instLT m n)) := fun hc_h => absurd (@hc_h (Bool) (@BooleanRing.toRing Bool instBooleanRingBool) (Bool.instPartialOrder) (ZNum.zero) (ZNum.neg PosNum.one)) (by
  decide +kernel)

-- Set.Nonempty.eq_univ, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.eq_univ.h2 : ¬∀ {α : Type} {s : Set α}, s.Nonempty → s = Set.univ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- List.countP_erase, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countP_erase.h2 : ¬∀ {α : Type} [inst : BEq α] (p : α → Bool) (l : List α) (a : α), LawfulBEq α := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) (fun n => n % 2 == 0 : ℕ → Bool) ([]) (0)) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_beq (a := (0 : ℕ)) (b := (1 : ℕ))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.count_diff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.count_diff.h2 : ¬∀ {α : Type} [inst : BEq α] (a : α) (l₁ l₂ : List α), List.count a (l₁.diff l₂) = List.count a l₁ - List.count a l₂ := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a ≤ b⟩ : BEq ℕ) (1) ([0]) ([1])) (by
  decide +kernel)

-- List.getLast_flatten_eq_getLast_getLast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getLast_flatten_eq_getLast_getLast.h2 : ¬∀ {α : Type} {l : List (List α)}, l.flatten ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- List.getLast_flatten_eq_getLast_getLast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getLast_flatten_eq_getLast_getLast.h3 : ¬∀ {α : Type} {l : List (List α)} (hl : l.flatten ≠ []),
        l.getLast
            ((fun {α : Type} {l : List (List α)} (hl : l.flatten ≠ []) =>
                (fun {α : Type} {l : List (List α)} (hl : l.flatten ≠ []) =>
                    Classical.byContradiction
                      (Lean.Grind.intro_with_eq (¬¬l = []) (l = []) False (Lean.Grind.not_not (l = [])) fun (h : l = []) =>
                        id
                          (Eq.mp
                            (Eq.trans
                              (Eq.symm
                                (eq_true
                                  (Eq.trans (congrArg List.flatten h)
                                    (Eq.mp (Eq.refl ([].flatten = [])) List.flatten_nil))))
                              (eq_false hl))
                            True.intro)))
                  hl)
              hl) ≠
          [] := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) ([[0], []]) hc_k0) (by
  decide +kernel)

-- Set.image_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_mono.h5 : ¬∀ {α β : Type} {f : α → β} {s t : Set α}, f '' s ⊆ f '' t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- List.lex_cons_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lex_cons_iff.h2 : ¬∀ {α : Type} {r : α → α → Prop} {a : α} {l₁ l₂ : List α}, List.Lex r (a :: l₁) (a :: l₂) ↔ List.Lex r l₁ l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (0) ([]) ([])) (by
  decide +kernel)

-- Set.LeftInvOn.injOn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.LeftInvOn.injOn.h5 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {f₁' : β → α}, Set.InjOn f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | True}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- List.Lex.append_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.append_right.h5 : ¬∀ {α : Type} (r : α → α → Prop) {s₁ s₂ : List α} (t : List α), List.Lex r s₁ (s₂ ++ t) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([]) ([])) (by
  decide +kernel)

-- Ordnode.erase.valid, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.erase.valid.h5 : ¬∀ {α : Type} [inst : Preorder α] [inst_1 : DecidableLE α] (x : α) {t : Ordnode α}, (Ordnode.erase x t).Valid := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Nat.decLe) (0) (Ordnode.node 0 Ordnode.nil 0 (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil))) (by
  nofun)

-- Sym2.sound, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.sound.h5 : ¬∀ {α : Type} {a b c d : α}, s(a, b) = s(c, d) := fun hc_h => absurd (@hc_h (ℕ) (0) (0) (0) (1)) (by
  decide +kernel)

-- List.cons_le_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_le_cons.h5 : ¬∀ {α : Type} [inst : LinearOrder α] (a : α) {l l' : List α}, a :: l' ≤ a :: l := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) (0) ([]) ([0])) (by
  decide +kernel)

-- Set.mk_preimage_prod_right_eq_empty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mk_preimage_prod_right_eq_empty.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {a : α}, Prod.mk a ⁻¹' s ×ˢ t = ∅ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n % 2 = 0}) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- Nat.not_pos_pow_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_pos_pow_dvd.h2 : ¬∀ {a n : ℕ}, 1 < n → ¬a ^ n ∣ a := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.not_pos_pow_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_pos_pow_dvd.h3 : ¬∀ {a n : ℕ}, 1 < a → ¬a ^ n ∣ a := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.descFactorial_lt_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.descFactorial_lt_pow.h1 : ¬∀ {n k : ℕ}, 2 ≤ k → n.descFactorial k < n ^ k := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.descFactorial_lt_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.descFactorial_lt_pow.h3 : ¬∀ {n : ℕ}, n ≠ 0 → ∀ {k : ℕ}, n.descFactorial k < n ^ k := fun hc_h => absurd (@hc_h (1) (by
  decide) (0)) (by
  decide +kernel)

-- Nat.factorial_lt_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorial_lt_of_lt.h2 : ¬∀ {m n : ℕ}, n < m → n.factorial < m.factorial := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.factorial_lt_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorial_lt_of_lt.h3 : ¬∀ {m n : ℕ}, 0 < n → n.factorial < m.factorial := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Set.image_congr, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_congr.h5 : ¬∀ {α β : Type} {f g : α → β} {s : Set α}, f '' s = g '' s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Fintype.rightInverse_bijInv, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.rightInverse_bijInv.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst : DecidableEq β] {f : α → β}, Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (instDecidableEqNat) (fun _ => 0 : Bool → ℕ)) (by
  nofun)

-- Function.Injective.invOfMemRange_surjective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.invOfMemRange_surjective.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst : DecidableEq β] {f : α → β}, Function.Injective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (instDecidableEqNat) (fun _ => 0 : Bool → ℕ)) (by
  decide +kernel)

-- Set.mk_preimage_prod_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mk_preimage_prod_left.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {b : β}, (fun (a : α) => (a, b)) ⁻¹' s ×ˢ t = s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n % 2 = 0}) (1)) (by
  simp)

-- List.getElem?_iterate, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem?_iterate.h5 : ¬∀ {α : Type} (f : α → α) (a : α) (n i : ℕ), (List.iterate f a n)[i]? = Option.some (f^[i] a) := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (0) (0)) (by
  decide +kernel)

-- List.getElem_iterate, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_iterate.h5 : ¬∀ {α : Type} (f : α → α) (a : α) (n i : ℕ), i < (List.iterate f a n).length := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (0) (0)) (by
  decide +kernel)

-- Set.preimage_eq_iff_eq_image, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.preimage_eq_iff_eq_image.h3 : ¬∀ {α β : Type} {f : α → β} {s : Set β} {t : Set α}, f ⁻¹' s = t ↔ s = f '' t := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ => 0 : Bool → ℕ) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.true})) (by
  simp)

-- Set.prod_subset_prod_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.prod_subset_prod_left.h5 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {t : Set β}, s₁ ×ˢ t ⊆ s₂ ×ˢ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- Set.subset_biUnion_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_biUnion_of_mem.h5 : ¬∀ {α β : Type} {s : Set α} {u : α → Set β} {x : α}, u x ⊆ ⋃ x ∈ s, u x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) (fun (a : ℕ) => {n : ℕ | n = 0}) (0)) (by
  simp)

-- Set.mem_biInter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_biInter.h5 : ¬∀ {α β : Type} {s : Set α} {t : α → Set β} {y : β}, y ∈ ⋂ x ∈ s, t x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) (1)) (by
  simp)

-- List.Nodup.head_eq_getLast_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.head_eq_getLast_iff.h2 : ¬∀ {α : Type} {l : List α}, l.Nodup → l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([]) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.head_eq_getLast_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.head_eq_getLast_iff.h3 : ¬∀ {α : Type} {l : List α} (hne : l ≠ []), l.head hne = l.getLast hne ↔ ∃ (x : α), l = [x] := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) ([0, 0]) hc_k0) (by
  simp)

-- Nat.two_lt_of_ne, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.two_lt_of_ne.h1 : ¬∀ {n : ℕ}, n ≠ 1 → n ≠ 2 → 2 < n := fun hc_h => absurd (@hc_h (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.two_lt_of_ne, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.two_lt_of_ne.h2 : ¬∀ {n : ℕ}, n ≠ 0 → n ≠ 2 → 2 < n := fun hc_h => absurd (@hc_h (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.two_lt_of_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.two_lt_of_ne.h3 : ¬∀ {n : ℕ}, n ≠ 0 → n ≠ 1 → 2 < n := fun hc_h => absurd (@hc_h (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Monotone.rangeFactorization, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Monotone.rangeFactorization.h5 : ¬∀ {α β : Type} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β}, Monotone (Set.rangeFactorization f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.instPartialOrder.toPreorder) (Bool.instPartialOrder.toPreorder) (not : Bool → Bool)) (by
  decide +kernel)

-- Function.Injective.injOn_range, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.injOn_range.h5 : ¬∀ {α β γ : Type} {f : α → β} {g : β → γ}, Set.InjOn g (Set.range f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Set.prod_mono_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.prod_mono_right.h5 : ¬∀ {α β : Type} {s : Set α} {t₁ t₂ : Set β}, s ×ˢ t₁ ⊆ s ×ˢ t₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Prod.Lex.refl_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.Lex.refl_right.h4 : ¬∀ {α β : Type} (r : α → α → Prop) (s : β → β → Prop) (x : α × β), Prod.Lex r s x x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) ((0, 0))) (by
  decide +kernel)

-- Set.BijOn.bijective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.bijective.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.BijOn f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- List.IsRotated.map, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsRotated.map.h4 : ¬∀ {α β : Type} {l₁ l₂ : List α} (f : α → β), List.map f l₁ ~r List.map f l₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([]) ([0]) (fun n => n + 1 : ℕ → ℕ)) (by
  decide +kernel)

-- Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel.h2 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Std.Irrefl r], Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.ncard_lt_card, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_lt_card.h2 : ¬∀ {α : Type} {s : Set α}, s ≠ Set.univ → s.ncard < Nat.card α := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.ncard_lt_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_lt_card.h3 : ¬∀ {α : Type} {s : Set α} [inst : Finite α], s.ncard < Nat.card α := fun hc_h => absurd (@hc_h (Bool) ({x : Bool | True}) _) (by
  simp)

-- Set.injective_iff_injective_of_iUnion_eq_univ, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.injective_iff_injective_of_iUnion_eq_univ.h5 : ¬∀ {α β ι : Type} {f : α → β} {U : ι → Set β},
        Function.Injective f ↔ ∀ (i : ι), Function.Injective ((U i).restrictPreimage f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (fun (a : ℕ) => {x : ℕ | False})) (by
  (simp <;> decide))

-- Nat.factorizationLCMLeft_mul_factorizationLCMRight, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorizationLCMLeft_mul_factorizationLCMRight.h2 : ¬∀ {a b : ℕ}, b ≠ 0 → a.factorizationLCMLeft b * a.factorizationLCMRight b = a.lcm b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.factorizationLCMLeft_mul_factorizationLCMRight, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorizationLCMLeft_mul_factorizationLCMRight.h3 : ¬∀ {a b : ℕ}, a ≠ 0 → a.factorizationLCMLeft b * a.factorizationLCMRight b = a.lcm b := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- Set.powersetCard.compl_symm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.powersetCard.compl_symm.h5 : ¬∀ {α : Type} {n : ℕ} [inst : DecidableEq α] [inst : Fintype α] {m : ℕ}, m + n = Fintype.card α := fun hc_h => absurd (@hc_h (Bool) (0) (instDecidableEqBool) (Bool.fintype) (0)) (by
  decide +kernel)

-- ZMod.ne_zero_of_gcd_eq_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.ne_zero_of_gcd_eq_one.h2 : Not
      (∀ {a : Int} {p : Nat},
        @Eq Nat (a.gcd (@Nat.cast Int instNatCastInt p)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Ne (ZMod p)
            (@Int.cast (ZMod p)
              (@AddGroupWithOne.toIntCast (ZMod p)
                (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p))))
              a)
            (@OfNat.ofNat (ZMod p) (nat_lit 0)
              (@Zero.toOfNat0 (ZMod p)
                (@MulZeroClass.toZero (ZMod p)
                  (@instMulZeroClassOfSemiring (ZMod p)
                    (@CommSemiring.toSemiring (ZMod p) (@CommRing.toCommSemiring (ZMod p) (ZMod.commRing p)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- ZMod.ne_zero_of_gcd_eq_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.ne_zero_of_gcd_eq_one.h3 : Not
      (∀ {a : Int} {p : Nat},
        Nat.Prime p →
          @Ne (ZMod p)
            (@Int.cast (ZMod p)
              (@AddGroupWithOne.toIntCast (ZMod p)
                (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p))))
              a)
            (@OfNat.ofNat (ZMod p) (nat_lit 0)
              (@Zero.toOfNat0 (ZMod p)
                (@MulZeroClass.toZero (ZMod p)
                  (@instMulZeroClassOfSemiring (ZMod p)
                    (@CommSemiring.toSemiring (ZMod p) (@CommRing.toCommSemiring (ZMod p) (ZMod.commRing p)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Set.biInter_subset_biUnion, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.biInter_subset_biUnion.h3 : ¬∀ {α β : Type} {s : Set α} {t : α → Set β}, ⋂ x ∈ s, t x ⊆ ⋃ x ∈ s, t x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) (fun (a : ℕ) => {n : ℕ | n = 0})) (by
  simp)

-- Set.biUnion_const, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.biUnion_const.h3 : ¬∀ {α β : Type} {s : Set α} (t : Set β), ⋃ a ∈ s, t = t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- Int.ModEq.of_mul_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.of_mul_left.h4 : ¬∀ {n a b : ℤ} (m : ℤ), a ≡ b [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- Int.ModEq.add_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.add_right.h4 : ¬∀ {n a b : ℤ} (c : ℤ), a + c ≡ b + c [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- List.take_eraseIdx_eq_take_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.take_eraseIdx_eq_take_of_le.h4 : ¬∀ {α : Type} (l : List α) (i j : ℕ), List.take i (l.eraseIdx j) = List.take i l := fun hc_h => absurd (@hc_h (ℕ) ([0]) (1) (0)) (by
  decide +kernel)

-- Int.ModEq.add_left_cancel', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.add_left_cancel'.h4 : ¬∀ {n a b : ℤ} (c : ℤ), a ≡ b [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- Int.ModEq.mul_left_cancel_iff', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.mul_left_cancel_iff'.h4 : ¬∀ {m a b c : ℤ}, c * a ≡ c * b [ZMOD c * m] ↔ a ≡ b [ZMOD m] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- Set.prod_sInter, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.prod_sInter.h3 : ¬∀ {α β : Type} {T : Set (Set β)} (s : Set α), s ×ˢ ⋂₀ T = ⋂ t ∈ T, s ×ˢ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (∅) ({n : ℕ | n = 0})) (by
  simp)

-- Int.ModEq.pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.pow.h4 : ¬∀ {n a b : ℤ} (m : ℕ), a ^ m ≡ b ^ m [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (1)) (by
  decide +kernel)

-- Int.ModEq.sub_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.sub_right.h4 : ¬∀ {n a b : ℤ} (c : ℤ), a - c ≡ b - c [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- Int.ModEq.mul_right_cancel_iff', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.mul_right_cancel_iff'.h4 : ¬∀ {m a b c : ℤ}, a * c ≡ b * c [ZMOD m * c] ↔ a ≡ b [ZMOD m] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- List.Perm.subset_congr_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.subset_congr_left.h4 : ¬∀ {α : Type} {l₁ l₂ l₃ : List α}, l₁ ⊆ l₃ ↔ l₂ ⊆ l₃ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) ([])) (by
  decide +kernel)

-- List.Perm.subset_congr_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.subset_congr_right.h4 : ¬∀ {α : Type} {l₁ l₂ l₃ : List α}, l₃ ⊆ l₁ ↔ l₃ ⊆ l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) ([0])) (by
  decide +kernel)

-- Set.injOn_of_subsingleton, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.injOn_of_subsingleton.h2 : ¬∀ {α β : Type} (f : α → β) (s : Set α), Set.InjOn f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({x : ℕ | True})) (by
  simp)

-- Prime.dvd_prod_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prime.dvd_prod_iff.h4 : ¬∀ {M : Type} [inst : CommMonoidWithZero M] {p : M} {L : List M}, p ∣ L.prod ↔ ∃ a ∈ L, p ∣ a := fun hc_h => absurd (@hc_h (ℕ) (Nat.instCommMonoidWithZero) (1) ([])) (by
  decide +kernel)

-- Set.iInter_mono'', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iInter_mono''.h4 : ¬∀ {α ι : Type} {s t : ι → Set α}, Set.iInter s ⊆ Set.iInter t := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun (a : ℕ) => {b : Bool | b = Bool.true}) (fun (a : ℕ) => {b : Bool | b = Bool.false})) (by
  simp)

-- Set.iUnion_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iUnion_subset.h4 : ¬∀ {α ι : Type} {s : ι → Set α} {t : Set α}, ⋃ (i : ι), s i ⊆ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Set.iUnion_mono'', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iUnion_mono''.h4 : ¬∀ {α ι : Type} {s t : ι → Set α}, Set.iUnion s ⊆ Set.iUnion t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun (a : ℕ) => {x : ℕ | False})) (by
  simp)

-- List.set_perm_cons_eraseIdx, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.set_perm_cons_eraseIdx.h3 : ¬∀ {α : Type} {l : List α} {n : ℕ} (a : α), (l.set n a).Perm (a :: l.eraseIdx n) := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (0)) (by
  decide +kernel)

-- List.takeI_eq_take, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.takeI_eq_take.h4 : ¬∀ {α : Type} [inst : Inhabited α] {n : ℕ} {l : List α}, List.takeI n l = List.take n l := fun hc_h => absurd (@hc_h (ℕ) (instInhabitedNat) (1) ([])) (by
  decide +kernel)

-- List.takeD_eq_take, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.takeD_eq_take.h4 : ¬∀ {α : Type} {n : ℕ} {l : List α} (a : α), List.takeD n l a = List.take n l := fun hc_h => absurd (@hc_h (ℕ) (1) ([]) (0)) (by
  decide +kernel)

-- ZMod.cast_natCast', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.cast_natCast'.h3 : Not
      (∀ {n : Nat} {R : Type} [inst : Ring R] (k : Nat),
        @Eq R
          (@ZMod.cast R (@Ring.toAddGroupWithOne R inst) n
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              k))
          (@Nat.cast R
            (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R (@Ring.toAddGroupWithOne R inst))) k)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Bool) (@BooleanRing.toRing Bool instBooleanRingBool) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- zmod_val_inv_nsmul_nsmul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.zmod_val_inv_nsmul_nsmul.h3 : Not
      (∀ {α : Type} [inst : AddGroup α] {n : Nat} (a : α),
        @Eq α
          (@HSMul.hSMul Nat α α
            (@instHSMul Nat α
              (@NSMul.toSMul α (@AddMonoid.toNSMul α (@SubNegMonoid.toAddMonoid α (@AddGroup.toSubNegMonoid α inst)))))
            (@ZMod.val (Nat.card α)
              (@Inv.inv (ZMod (Nat.card α)) (ZMod.instInv (Nat.card α))
                (@Nat.cast (ZMod (Nat.card α))
                  (@AddMonoidWithOne.toNatCast (ZMod (Nat.card α))
                    (@AddGroupWithOne.toAddMonoidWithOne (ZMod (Nat.card α))
                      (@Ring.toAddGroupWithOne (ZMod (Nat.card α))
                        (@CommRing.toRing (ZMod (Nat.card α)) (ZMod.commRing (Nat.card α))))))
                  n)))
            (@HSMul.hSMul Nat α α
              (@instHSMul Nat α
                (@NSMul.toSMul α (@AddMonoid.toNSMul α (@SubNegMonoid.toAddMonoid α (@AddGroup.toSubNegMonoid α inst)))))
              n a))
          a) := fun hc_h => absurd (@hc_h (Bool) (@AddGroupWithOne.toAddGroup Bool (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Bool.true)) (by
  simp)

-- ZMod.cast_intCast', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.cast_intCast'.h3 : Not
      (∀ {n : Nat} {R : Type} [inst : Ring R] (k : Int),
        @Eq R
          (@ZMod.cast R (@Ring.toAddGroupWithOne R inst) n
            (@Int.cast (ZMod n)
              (@AddGroupWithOne.toIntCast (ZMod n)
                (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
              k))
          (@Int.cast R (@AddGroupWithOne.toIntCast R (@Ring.toAddGroupWithOne R inst)) k)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Bool) (@BooleanRing.toRing Bool instBooleanRingBool) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  decide +kernel)

-- Set.mem_union_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_union_left.h4 : ¬∀ {α : Type} {x : α} {a : Set α} (b : Set α), x ∈ a ∪ b := fun hc_h => absurd (@hc_h (ℕ) (1) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  decide +kernel)

-- Set.Nonempty.graphOn, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.graphOn.h4 : ¬∀ {α β : Type} {s : Set α} {f : α → β}, (Set.graphOn f s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Finset.card_pair, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.card_pair.h4 : Not
      (∀ {α : Type} {a b : α} [inst : DecidableEq α],
        @Eq Nat
          (@Finset.card α
            (@Insert.insert α (Finset α) (@Finset.instInsert α inst) a
              (@Singleton.singleton α (Finset α) (@Finset.instSingleton α) b)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (instDecidableEqNat)) (by
  decide +kernel)

-- List.minimum_of_length_pos_le_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minimum_of_length_pos_le_iff.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {b : α}, 0 < l.length := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([]) (0)) (by
  decide +kernel)

-- Set.iUnion_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iUnion_mono.h4 : ¬∀ {α ι : Type} {s t : ι → Set α}, ⋃ (i : ι), s i ⊆ ⋃ (i : ι), t i := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun (a : ℕ) => {x : ℕ | False})) (by
  simp)

-- List.le_maximum_of_length_pos_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_maximum_of_length_pos_iff.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {b : α}, 0 < l.length := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([]) (0)) (by
  decide +kernel)

-- Set.MapsTo.iterate_restrict, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.iterate_restrict.h3 : ¬∀ {α : Type} {f : α → α} {s : Set α} (n : ℕ), Set.MapsTo f s s := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- List.length_of_sublistsLen, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_of_sublistsLen.h4 : ¬∀ {α : Type} {n : ℕ} {l : List α} {l' : List α}, l'.length = n := fun hc_h => absurd (@hc_h (ℕ) (0) ([]) ([0])) (by
  decide +kernel)

-- List.revzip_sublists', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.revzip_sublists'.h4 : ¬∀ {α : Type} (l l₁ l₂ : List α), (l₁ ++ l₂).Perm l := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) ([0])) (by
  decide +kernel)

-- List.revzip_sublists, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.revzip_sublists.h4 : ¬∀ {α : Type} (l l₁ l₂ : List α), (l₁ ++ l₂).Perm l := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) ([0])) (by
  decide +kernel)

-- List.sublistsLen_sublist_of_sublist, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sublistsLen_sublist_of_sublist.h4 : ¬∀ {α : Type} (n : ℕ) {l₁ l₂ : List α}, (List.sublistsLen n l₁).Sublist (List.sublistsLen n l₂) := fun hc_h => absurd (@hc_h (ℕ) (1) ([0]) ([])) (by
  decide +kernel)

-- Set.Nonempty.snd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.snd.h4 : ¬∀ {α β : Type} {s : Set α} {t : Set β}, t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Sym2.fromRel_relationMap, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.fromRel_relationMap.h3 : ¬∀ {α β : Type} {r : α → α → Prop} (f : α → β), Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Sym2.fromRel_prop, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.fromRel_prop.h2 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α}, Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0)) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.InjOn.injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.injective.h4 : ¬∀ {α β : Type} {s : Set α} {f : α → β}, Function.Injective (s.domRestrict f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({x : Bool | True}) (fun _ => 0 : Bool → ℕ)) (by
  decide +kernel)

-- Set.Infinite.iUnion, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.iUnion.h4 : ¬∀ {α ι : Type} {s : ι → Set α} (i : ι), (⋃ (i : ι), s i).Infinite := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0}) (0)) (by
  simp)

-- Set.injective_codRestrict, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.injective_codRestrict.h4 : ¬∀ {α ι : Type} {f : ι → α} {s : Set α} (x : ι), f x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Fintype.choose_spec, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.choose_spec.h4 : ¬∀ {α : Type} [inst : Fintype α] (p : α → Prop) [inst : DecidablePred p], ∃! a : α, p a := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) (fun _ => False : Bool → Prop) (fun (a : Bool) => instDecidableFalse)) (by
  simp)

-- List.IsChain.iff_of_mem_imp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.iff_of_mem_imp.h4 : ¬∀ {α : Type} {R S : α → α → Prop} {l : List α}, List.IsChain R l ↔ List.IsChain S l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a = b : ℕ → ℕ → Prop) ([0, 1])) (by
  decide +kernel)

-- List.IsChain.left_of_append, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.left_of_append.h4 : ¬∀ {α : Type} {R : α → α → Prop} {l₁ : List α} {l₂ : List α}, List.IsChain R l₁ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0]) ([])) (by
  decide +kernel)

-- List.getLast_iterate, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getLast_iterate.h4 : ¬∀ {α : Type} (f : α → α) (a : α) (n : ℕ), List.iterate f a n ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (0)) (by
  decide +kernel)

-- Set.SurjOn.surjective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.surjective.h4 : ¬∀ {α β : Type} {s : Set α} {f : α → β}, Function.Surjective f := fun hc_h => absurd (@hc_h (Bool) (Bool) ({b : Bool | b = Bool.true}) (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- List.IsChain.iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.iff.h3 : ¬∀ {α : Type} {R S : α → α → Prop} {l : List α}, List.IsChain R l ↔ List.IsChain S l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a = b : ℕ → ℕ → Prop) ([0, 1])) (by
  decide +kernel)

-- Set.Subtype.range_coind, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subtype.range_coind.h4 : ¬∀ {α β : Type} (f : α → β) {p : β → Prop} (a : α), p (f a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n = 0 : ℕ → Prop)) (by
  simp)

-- List.IsChain.take, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.take.h3 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} (n : ℕ), List.IsChain R (List.take n l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0]) (2)) (by
  decide +kernel)

-- Set.injOn_of_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.injOn_of_injective.h3 : ¬∀ {α β : Type} {f : α → β} {s : Set α}, Set.InjOn f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({x : ℕ | True})) (by
  simp)

-- List.Nodup.rotate_congr_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.rotate_congr_iff.h2 : ¬∀ {α : Type} {l : List α} {i j : ℕ}, l.rotate i = l.rotate j ↔ i % l.length = j % l.length ∨ l = [] := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (0) (1)) (by
  decide +kernel)

-- List.nodup_map_iff_inj_on, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nodup_map_iff_inj_on.h4 : ¬∀ {α β : Type} {f : α → β} {l : List α}, (List.map f l).Nodup ↔ ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ([0, 0])) (by
  decide +kernel)

-- Set.pairwise_insert_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.pairwise_insert_of_notMem.h4 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α} {a : α},
        (Insert.insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, r a b ∧ r b a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- Set.range_codRestrict, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.range_codRestrict.h4 : ¬∀ {α ι : Type} {f : ι → α} {s : Set α} (x : ι), f x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Multiset.find?_coe, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.find?_coe.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (l : List α), {x : α | x ∈ ↑l ∧ p x}.Subsingleton := fun hc_h => absurd (@hc_h (Bool) (fun _ => True : Bool → Prop) (fun (a : Bool) => instDecidableTrue) ([Bool.false, Bool.true])) (by
  decide +kernel)

-- Set.Nonempty.image, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.image.h4 : ¬∀ {α β : Type} (f : α → β) {s : Set α}, (f '' s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({x : ℕ | False})) (by
  simp)

-- Multiset.pmap_zero, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Multiset.pmap_zero.h4.der.{v, u_1} : ∀ {α : Type u_1} {β : Type v} {p : α → Prop} (f : (a : α) → p a → β) (a : α),
      @Membership.mem α (Multiset α) (@Multiset.instMembership α)
          (@OfNat.ofNat (Multiset α) (nat_lit 0) (@Zero.toOfNat0 (Multiset α) (@Multiset.instZero α))) a →
        p a := by
  (intros; trivial)
theorem HypCheckProof.Multiset.pmap_zero.h4.{v, u_1} : ∀ {α : Type u_1} {β : Type v} {p : α → Prop} (f : (a : α) → p a → β),
      @Eq (Multiset β)
        (@Multiset.pmap α β p f (@OfNat.ofNat (Multiset α) (nat_lit 0) (@Zero.toOfNat0 (Multiset α) (@Multiset.instZero α)))
          (@HypCheckProof.Multiset.pmap_zero.h4.der α β p f))
        (@OfNat.ofNat (Multiset β) (nat_lit 0) (@Zero.toOfNat0 (Multiset β) (@Multiset.instZero β))) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Multiset.pmap_zero hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Multiset.pmap_zero.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- Fin.cast_le_cast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.cast_le_cast.h2 : ¬∀ {n m : ℕ} {a b : Fin n}, n = m := fun hc_h => absurd (@hc_h (1) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.cast_lt_cast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.cast_lt_cast.h2 : ¬∀ {n m : ℕ} {a b : Fin n}, n = m := fun hc_h => absurd (@hc_h (1) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.sub_castAdd_eq_castAdd_sub_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.sub_castAdd_eq_castAdd_sub_of_le.h4 : ¬∀ {m n : ℕ} {a b : Fin n}, Fin.castAdd m a - Fin.castAdd m b = Fin.castAdd m (a - b) := fun hc_h => absurd (@hc_h (1) (2) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Function.Surjective.nonempty_preimage, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.nonempty_preimage.h3 : ¬∀ {α β : Type} {f : α → β} {s : Set β}, (f ⁻¹' s).Nonempty ↔ s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun _ => true : ℕ → Bool) ({b : Bool | b = Bool.false})) (by
  simp)

-- List.getD_eq_getElem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getD_eq_getElem.h4 : ¬∀ {α : Type} (l : List α) (d : α) {n : ℕ}, n < l.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (0)) (by
  decide +kernel)

-- List.getD_eq_default, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getD_eq_default.h4 : ¬∀ {α : Type} (l : List α) (d : α) {n : ℕ}, l.getD n d = d := fun hc_h => absurd (@hc_h (ℕ) ([0]) (1) (0)) (by
  decide +kernel)

-- Matrix.vecHead_vecAlt0, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.vecHead_vecAlt0.h3 : ¬∀ {α : Type} {m n : ℕ} (v : Fin (m + 2) → α), m + 2 = n + 1 + (n + 1) := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (fun (a : Fin (0 + 2)) => 0)) (by
  decide +kernel)

-- Part.union_get_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.union_get_eq.h4 : ¬∀ {α : Type} [inst : Union α] (a b : Part α), (a ∪ b).Dom := fun hc_h => absurd (@hc_h (Lean.NameSet) (Lean.NameSet.instUnion_batteries) (⊥) (⊥)) (by
  nofun)

-- Part.left_dom_of_sub_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.left_dom_of_sub_dom.h4 : ¬∀ {α : Type} [inst : Sub α] {a : Part α} {b : Part α}, a.Dom := fun hc_h => absurd (@hc_h (ℕ) (instSubNat) (⊥) (0)) (by
  nofun)

-- Part.sub_get_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.sub_get_eq.h4 : ¬∀ {α : Type} [inst : Sub α] (a b : Part α), (a - b).Dom := fun hc_h => absurd (@hc_h (ℕ) (instSubNat) (0) (⊥)) (by
  nofun)

-- Part.mul_get_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.mul_get_eq.h4 : ¬∀ {α : Type} [inst : Mul α] (a b : Part α), (a * b).Dom := fun hc_h => absurd (@hc_h (ℕ) (instMulNat) (0) (⊥)) (by
  nofun)

-- Part.neg_mem_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.neg_mem_neg.h4 : ¬∀ {α : Type} [inst : Neg α] (a : Part α) (ma : α), -ma ∈ -a := fun hc_h => absurd (@hc_h (Bool) (instNegBool_mathlib) (0) (Bool.true)) (by
  nofun)

-- Part.right_dom_of_inter_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.right_dom_of_inter_dom.h4 : ¬∀ {α : Type} [inst : Inter α] {a : Part α} {b : Part α}, b.Dom := fun hc_h => absurd (@hc_h (Lean.NameSet) (Lean.NameSet.instInter_batteries) (⊥) (⊥)) (by
  nofun)

-- Part.right_dom_of_sdiff_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.right_dom_of_sdiff_dom.h4 : ¬∀ {α : Type} [inst : SDiff α] {a : Part α} {b : Part α}, b.Dom := fun hc_h => absurd (@hc_h (Bool) (Bool.instBooleanAlgebra.toSDiff) (0) (⊥)) (by
  nofun)

-- Part.left_dom_of_mul_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.left_dom_of_mul_dom.h4 : ¬∀ {α : Type} [inst : Mul α] {a : Part α} {b : Part α}, a.Dom := fun hc_h => absurd (@hc_h (ℕ) (instMulNat) (⊥) (0)) (by
  nofun)

-- Part.Dom.bind, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.Dom.bind.h3 : ¬∀ {α β : Type} {o : Part α} (f : α → Part β), o.Dom := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (⊥) (fun (a : ℕ) => 0)) (by
  nofun)

-- Nat.sum_divisors_filter_squarefree, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.sum_divisors_filter_squarefree.h1 : ¬∀ {n : ℕ} {α : Type} [inst : AddCommMonoid α] {f : ℕ → α},
        ∑ d ∈ n.divisors with Squarefree d, f d =
          ∑ i ∈ (UniqueFactorizationMonoid.normalizedFactors n).toFinset.powerset, f i.val.prod := fun hc_h => absurd (@hc_h (0) (ℕ) (Nat.instAddCommMonoid) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Nat.ModEq.add_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.add_right.h4 : ¬∀ {n a b : ℕ} (c : ℕ), a + c ≡ b + c [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- Nat.ModEq.pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.pow.h4 : ¬∀ {n a b : ℕ} (m : ℕ), a ^ m ≡ b ^ m [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (1)) (by
  decide +kernel)

-- Nat.ModEq.mul_left', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.mul_left'.h4 : ¬∀ {n a b : ℕ} (c : ℕ), c * a ≡ c * b [MOD c * n] := fun hc_h => absurd (@hc_h (0) (0) (1) (1)) (by
  decide +kernel)

-- Antitone.sortedGE_ofFn, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Antitone.sortedGE_ofFn.h4 : ¬∀ {α : Type} [inst : Preorder α] {n : ℕ} {f : Fin n → α}, (List.ofFn f).SortedGE := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (2) (fun (a : Fin 2) => if a = (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2) then 0 else 1)) (by
  decide +kernel)

-- Nat.ModEq.add_left_cancel', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.add_left_cancel'.h4 : ¬∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- Nat.ModEq.mul_left_cancel_iff', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.mul_left_cancel_iff'.h4 : ¬∀ {a b c m : ℕ}, c * a ≡ c * b [MOD c * m] ↔ a ≡ b [MOD m] := fun hc_h => absurd (@hc_h (0) (1) (0) (0)) (by
  decide +kernel)

-- StrictAnti.sortedGT_ofFn, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictAnti.sortedGT_ofFn.h4 : ¬∀ {α : Type} [inst : Preorder α] {n : ℕ} {f : Fin n → α}, (List.ofFn f).SortedGT := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (2) (fun (a : Fin 2) => 0)) (by
  decide +kernel)

-- List.SortedLT.strictMono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.strictMono.h4 : ¬∀ {α : Type} [inst : Preorder α] {n : ℕ} {f : Fin n → α}, StrictMono f := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (2) (fun (a : Fin 2) => 0)) (by
  decide +kernel)

-- Function.Injective.encard_image, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.encard_image.h3 : ¬∀ {α β : Type} {f : α → β} (s : Set α), (f '' s).encard = s.encard := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({x : ℕ | True})) (by
  simp)

-- Set.image_preimage_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_preimage_eq.h4 : ¬∀ {α β : Type} {f : α → β} (s : Set β), f '' f ⁻¹' s = s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({x : ℕ | True})) (by
  simp)

-- Nat.cast_dvd_cast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.cast_dvd_cast.h4 : Not
      (∀ {α : Type} [inst : Semiring α] {m n : Nat},
        @Dvd.dvd α
          (@semigroupDvd α
            (@SemigroupWithZero.toSemigroup α
              (@NonUnitalSemiring.toSemigroupWithZero α (@Semiring.toNonUnitalSemiring α inst))))
          (@Nat.cast α
            (@AddMonoidWithOne.toNatCast α
              (@AddCommMonoidWithOne.toAddMonoidWithOne α
                (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
            m)
          (@Nat.cast α
            (@AddMonoidWithOne.toNatCast α
              (@AddCommMonoidWithOne.toAddMonoidWithOne α
                (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
            n)) := fun hc_h => absurd (@hc_h (Nat) (Nat.instSemiring) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- List.Nodup.bagInter_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.bagInter_right.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : DecidableEq α], (l₁.bagInter l₂).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) ([0, 0]) (instDecidableEqNat)) (by
  decide +kernel)

-- List.Subset.union_eq_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subset.union_eq_right.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {xs ys : List α}, xs ∪ ys = ys := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([])) (by
  decide +kernel)

-- Set.ncard_image_of_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_image_of_injective.h4 : ¬∀ {α β : Type} {f : α → β} (s : Set α), (f '' s).ncard = s.ncard := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({x : ℕ | True})) (by
  simp)

-- Fin.Embedding.init_snoc, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.Embedding.init_snoc.h4 : ¬∀ {α : Type} {n : ℕ} (x : Fin n ↪ α) {a : α}, a ∉ Set.range ⇑x := fun hc_h => absurd (@hc_h (ℕ) (1) ({ toFun := fun (a : Fin 1) => 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Fin 1 ↪ ℕ }) (0)) (by
  decide +kernel)

-- Set.nontrivial_of_image, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_of_image.h4 : ¬∀ {α β : Type} (f : α → β) (s : Set α), s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Disjoint.inter_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.inter_right.h4 : ¬∀ {α : Type} {s t : Set α} (u : Set α), Disjoint s (t ∩ u) := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- List.lookmap_congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lookmap_congr.h4 : ¬∀ {α : Type} {f g : α → Option α} {l : List α}, List.lookmap f l = List.lookmap g l := fun hc_h => absurd (@hc_h (ℕ) (fun _ => none : ℕ → Option ℕ) (fun n => some (n + 1) : ℕ → Option ℕ) ([0])) (by
  decide +kernel)

-- List.mem_keys_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_keys_of_mem.h4 : ¬∀ {α : Type} {β : α → Type} {s : Sigma β} {l : List (Sigma β)}, s.fst ∈ l.keys := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ((⟨0, 0⟩ : (_ : ℕ) × ℕ)) ([])) (by
  decide +kernel)

-- Dvd.dvd.natCast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dvd.dvd.natCast.h4 : Not
      (∀ {α : Type} [inst : Semiring α] {m n : Nat},
        @Dvd.dvd α
          (@semigroupDvd α
            (@SemigroupWithZero.toSemigroup α
              (@NonUnitalSemiring.toSemigroupWithZero α (@Semiring.toNonUnitalSemiring α inst))))
          (@Nat.cast α
            (@AddMonoidWithOne.toNatCast α
              (@AddCommMonoidWithOne.toAddMonoidWithOne α
                (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
            m)
          (@Nat.cast α
            (@AddMonoidWithOne.toNatCast α
              (@AddCommMonoidWithOne.toAddMonoidWithOne α
                (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
            n)) := fun hc_h => absurd (@hc_h (Nat) (Nat.instSemiring) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Disjoint.inter_left', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.inter_left'.h4 : ¬∀ {α : Type} {s t : Set α} (u : Set α), Disjoint (u ∩ s) t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- Set.Nonempty.image_const, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.image_const.h3 : ¬∀ {α β : Type} {s : Set α} (a : β), (fun (x : α) => a) '' s = {a} := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) (0)) (by
  simp)

-- List.Disjoint.dedup_append, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Disjoint.dedup_append.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {xs ys : List α}, (xs ++ ys).dedup = xs.dedup ++ ys.dedup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([0])) (by
  decide +kernel)

-- List.notMem_keys_of_nodupKeys_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.notMem_keys_of_nodupKeys_cons.h4 : ¬∀ {α : Type} {β : α → Type} {s : Sigma β} {l : List (Sigma β)}, s.fst ∉ l.keys := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ((⟨0, 0⟩ : (_ : ℕ) × ℕ)) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  decide +kernel)

-- Set.encard_preimage_of_bijective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_preimage_of_bijective.h3 : ¬∀ {α β : Type} {f : α → β} (t : Set β), (f ⁻¹' t).encard = t.encard := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Set.Infinite.preimage', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.preimage'.h4 : ¬∀ {α β : Type} {f : α → β} {s : Set β}, (f ⁻¹' s).Infinite := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({x : ℕ | False})) (by
  simp)

-- List.dedup_cons_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dedup_cons_of_notMem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {l : List α}, (a :: l).dedup = a :: l.dedup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) ([0])) (by
  decide +kernel)

-- Set.card_fintypeInsertOfNotMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.card_fintypeInsertOfNotMem.h4 : ¬∀ {α : Type} {a : α} (s : Set α) [inst : Fintype ↑s], a ∉ s := fun hc_h => absurd (@hc_h (Bool) (Bool.false) ({b : Bool | b = Bool.false}) (Subtype.fintype (Membership.mem {b : Bool | b = Bool.false}))) (by
  decide +kernel)

-- Commute.ofNat_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Commute.ofNat_left.h3 : ¬∀ {α : Type} [inst : NonAssocSemiring α] (n : ℕ) (x : α), n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (Nat.instNonAssocSemiring) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.instNonemptyElemImage, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.instNonemptyElemImage.h4 : ¬∀ {α β : Type} (f : α → β) (s : Set α), Nonempty ↑(f '' s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({x : ℕ | False})) (by
  simp)

-- AList.mem_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.AList.mem_mk.h3 : ¬∀ {α : Type} {β : α → Type} {l : List (Sigma β)} {x : α}, l.NodupKeys := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ), (⟨0, 0⟩ : (_ : ℕ) × ℕ)]) (0)) (by
  simp)

-- Set.SurjOn.iterate, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.iterate.h3 : ¬∀ {α : Type} {f : α → α} {s : Set α} (n : ℕ), Set.SurjOn f^[n] s s := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- Set.mem_union_of_disjoint, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_union_of_disjoint.h3 : ¬∀ {α : Type} {s t : Set α} {x : α}, x ∈ s ∪ t ↔ Xor (x ∈ s) (x ∈ t) := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (0)) (by
  decide +kernel)

-- Int.cast_dvd_cast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.cast_dvd_cast.h4 : Not
      (∀ {α : Type} [inst : Ring α] (m n : Int),
        @Dvd.dvd α
          (@semigroupDvd α
            (@SemigroupWithZero.toSemigroup α
              (@NonUnitalSemiring.toSemigroupWithZero α (@Semiring.toNonUnitalSemiring α (@Ring.toSemiring α inst)))))
          (@Int.cast α (@AddGroupWithOne.toIntCast α (@Ring.toAddGroupWithOne α inst)) m)
          (@Int.cast α (@AddGroupWithOne.toIntCast α (@Ring.toAddGroupWithOne α inst)) n)) := fun hc_h => absurd (@hc_h (Bool) (@BooleanRing.toRing Bool instBooleanRingBool) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  decide +kernel)

-- Int.cast_inj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.cast_inj.h2 : Not
      (∀ {α : Type} [inst : AddGroupWithOne α] {m n : Int},
        Iff (@Eq α (@Int.cast α (@AddGroupWithOne.toIntCast α inst) m) (@Int.cast α (@AddGroupWithOne.toIntCast α inst) n))
          (@Eq Int m n)) := fun hc_h => absurd (@hc_h (Bool) (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool)) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))) (by
  decide +kernel)

-- Nat.Ico_filter_modEq_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Ico_filter_modEq_card.h3 : Not
      (∀ (a b : Nat) {r : Nat} (v : Nat),
        @Eq Int
          (@Nat.cast Int instNatCastInt
            (@Finset.card Nat ({x ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder a b | r.ModEq x v})))
          (@Max.max Int Int.instMax
            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
              (@Int.ceil Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing
                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                  (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) (@Nat.cast Rat Rat.instNatCast b)
                    (@Nat.cast Rat Rat.instNatCast v))
                  (@Nat.cast Rat Rat.instNatCast r)))
              (@Int.ceil Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing
                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                  (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) (@Nat.cast Rat Rat.instNatCast a)
                    (@Nat.cast Rat Rat.instNatCast v))
                  (@Nat.cast Rat Rat.instNatCast r))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Int.ediv_emod_unique'', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ediv_emod_unique''.h4 : ¬∀ {a b r q : ℤ}, a / b = q ∧ a % b = r ↔ r + b * q = a ∧ 0 ≤ r ∧ r < |b| := fun hc_h => absurd (@hc_h (0) (0) (0) (0)) (by
  decide +kernel)

-- List.infix_flatMap_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.infix_flatMap_of_mem.h3 : ¬∀ {α : Type} {a : α} {as : List α} (f : α → List α), f a <:+: List.flatMap f as := fun hc_h => absurd (@hc_h (ℕ) (0) ([]) (fun n => [n] : ℕ → List ℕ)) (by
  decide +kernel)

-- Function.Injective.injOn, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.injOn.h3 : ¬∀ {α β : Type} {f : α → β} {s : Set α}, Set.InjOn f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({x : ℕ | True})) (by
  simp)

-- List.rdropWhile_concat_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.rdropWhile_concat_pos.h4 : ¬∀ {α : Type} (p : α → Bool) (l : List α) (x : α), List.rdropWhile p (l ++ [x]) = List.rdropWhile p l := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) ([]) (1)) (by
  decide +kernel)

-- List.or_exists_of_exists_mem_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.or_exists_of_exists_mem_cons.h4 : ¬∀ {α : Type} {p : α → Prop} {a : α} {l : List α}, p a ∨ ∃ x ∈ l, p x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (1) ([])) (by
  decide +kernel)

-- List.toFinset.ext, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.toFinset.ext.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l l' : List α}, l.toFinset = l'.toFinset := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([0])) (by
  decide +kernel)

-- List.interleaves_reverse_reverse_of_length_eq_length_add_one, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.interleaves_reverse_reverse_of_length_eq_length_add_one.h4 : ¬∀ {α : Type} {r : α → α → Prop} {l₁ l₂ : List α},
        List.Interleaves r l₁.reverse l₂.reverse ↔ List.Interleaves (Function.swap r) l₁ l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) ([1])) (by
  simp)

-- Finset.Nonempty.fst, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.Nonempty.fst.h4.{u_1, u_2} : ¬∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : Finset β}, s.Nonempty := by
  (simp_all; done)

-- List.ne_nil_of_mem_splitBy, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.ne_nil_of_mem_splitBy.h4 : ¬∀ {α : Type} {m : List α} {r : α → α → Bool} {l : List α}, m ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([]) (fun a b => a < b : ℕ → ℕ → Bool) ([])) (by
  decide +kernel)

-- Set.inter_insert_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_insert_of_mem.h4 : ¬∀ {α : Type} {s t : Set α} {a : α}, s ∩ Insert.insert a t = Insert.insert a (s ∩ t) := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- Choose.choose_pow_mul_pow_mul_modEq_choose, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.choose_pow_mul_pow_mul_modEq_choose.h4 : ¬∀ {k a b p : ℕ}, ↑((p ^ k * a).choose (p ^ k * b)) ≡ ↑(a.choose b) [ZMOD ↑p] := fun hc_h => absurd (@hc_h (1) (0) (1) (0)) (by
  decide +kernel)

-- Nat.dvd_iff_dvd_ofDigits, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_iff_dvd_ofDigits.h3 : ¬∀ (b b' : ℕ) (c : ℤ) (n : ℕ), b ∣ n ↔ ↑b ∣ Nat.ofDigits c (b'.digits n) := fun hc_h => absurd (@hc_h (0) (2) (0) (2)) (by
  decide +kernel)

-- Nat.dist_eq_intro, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dist_eq_intro.h4 : ¬∀ {n m k l : ℕ}, n.dist k = l.dist m := fun hc_h => absurd (@hc_h (0) (0) (0) (1)) (by
  decide +kernel)

-- Nat.le_nth_of_count_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_nth_of_count_le.h4 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {n k : ℕ}, Nat.count p n ≤ k := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (1) (0)) (by
  decide +kernel)

-- Nat.nth_lt_of_lt_count, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_lt_of_lt_count.h4 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {n k : ℕ}, Nat.nth p k < n := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0) (0)) (by
  decide +kernel)

-- Prod.instReflLex_mathlib_1, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.instReflLex_mathlib_1.h4 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop}, Std.Refl (Prod.Lex r s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.refl ((0, 0) : ℕ × ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Perm.disjoint_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.disjoint_right.h4 : ¬∀ {α : Type} {l₁ l₂ l : List α}, l.Disjoint l₁ ↔ l.Disjoint l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) ([0])) (by
  simp)

-- List.idxOf_eq_length_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_eq_length_iff.h2 : ¬∀ {α : Type} [inst : BEq α] {a : α} {l : List α}, List.idxOf a l = l.length ↔ a ∉ l := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) (0) ([1])) (by
  decide +kernel)

-- List.toFinset_replicate_of_ne_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.toFinset_replicate_of_ne_zero.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {a : α} {n : ℕ}, (List.replicate n a).toFinset = {a} := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (0)) (by
  decide +kernel)

-- List.mem_getLast?_append_of_mem_getLast?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_getLast?_append_of_mem_getLast?.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} {x : α}, x ∈ (l₁ ++ l₂).getLast? := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (0)) (by
  decide +kernel)

-- Function.Surjective.image_preimage, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.image_preimage.h3 : ¬∀ {α β : Type} {f : α → β} (s : Set β), f '' f ⁻¹' s = s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({x : ℕ | True})) (by
  simp)

-- Function.Bijective.bijOn_preimage, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Bijective.bijOn_preimage.h4 : ¬∀ {α β : Type} {t : Set β} {f : α → β}, Set.BijOn f (f ⁻¹' t) t := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({b : Bool | b = Bool.true}) (fun _ => false : ℕ → Bool)) (by
  simp)

-- Set.insert_inj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.insert_inj.h4 : ¬∀ {α : Type} {s : Set α} {a b : α}, Insert.insert a s = Insert.insert b s ↔ a = b := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n % 2 = 0}) (0) (2)) (by
  simp)

-- Set.image_compl_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_compl_eq.h4 : ¬∀ {α β : Type} {f : α → β} {s : Set α}, f '' sᶜ = (f '' s)ᶜ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Set.injOn_of_eq_iff_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.injOn_of_eq_iff_eq.h4 : ¬∀ {α β : Type} {f : α → β} (s : Set α), Set.InjOn f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({x : ℕ | True})) (by
  simp)

-- List.sublist_cons_of_sublist, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sublist_cons_of_sublist.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} (a : α), l₁.Sublist (a :: l₂) := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (1)) (by
  decide +kernel)

-- List.Perm.disjoint_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.disjoint_left.h4 : ¬∀ {α : Type} {l₁ l₂ l : List α}, l₁.Disjoint l ↔ l₂.Disjoint l := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) ([0])) (by
  simp)

-- List.choose_property, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.choose_property.h4 : ¬∀ {α : Type} (p : α → Prop) [inst : DecidablePred p] (l : List α), ∃ a ∈ l, p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) ([])) (by
  decide +kernel)

-- Set.image2_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_left.h4 : ¬∀ {α β : Type} {s : Set α} {t : Set β}, Set.image2 (fun (x : α) (x_1 : β) => x) s t = s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Set.BijOn.iterate, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.iterate.h3 : ¬∀ {α : Type} {f : α → α} {s : Set α} (n : ℕ), Set.BijOn f^[n] s s := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- Set.subset_union_of_subset_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_union_of_subset_right.h3 : ¬∀ {α : Type} {s u : Set α} (t : Set α), s ⊆ t ∪ u := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true})) (by
  simp)

-- List.prev_eq_getElem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_eq_getElem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {a : α}, a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0)) (by
  decide +kernel)

-- Set.subset_insert_iff_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_insert_iff_of_notMem.h4 : ¬∀ {α : Type} {s t : Set α} {a : α}, s ⊆ Insert.insert a t ↔ s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (0)) (by
  simp)

-- List.monotone_filter_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.monotone_filter_right.h4 : ¬∀ {α : Type} (l : List α) ⦃p q : α → Bool⦄, (List.filter p l).Sublist (List.filter q l) := fun hc_h => absurd (@hc_h (ℕ) ([0]) (fun n => n % 2 == 0 : ℕ → Bool) (fun _ => false : ℕ → Bool)) (by
  decide +kernel)

-- Finset.image_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.image_injective.h4 : ¬∀ {α β : Type} [inst : DecidableEq β] {f : α → β}, Function.Injective (Finset.image f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (instDecidableEqNat) (fun _ => 0 : Bool → ℕ)) (by
  decide +kernel)

-- Set.iInter_of_empty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.iInter_of_empty.h2 : ¬∀ {α ι : Type} (s : ι → Set α), ⋂ (i : ι), s i = Set.univ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0})) (by
  simp)

-- Nat.digits_length_le_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_length_le_iff.h2 : ¬∀ {b k : ℕ} (n : ℕ), (b.digits n).length ≤ k ↔ n < b ^ k := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- exists_seq_of_forall_finset_exists, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.exists_seq_of_forall_finset_exists.h3 : ¬∀ {α : Type} (P : α → Prop) (r : α → α → Prop),
        ∃ (f : ℕ → α), (∀ (n : ℕ), P (f n)) ∧ ∀ (m n : ℕ), m < n → r (f m) (f n) := fun hc_h => absurd (@hc_h (Bool) (fun _ => False : Bool → Prop) (fun _ _ => True : Bool → Bool → Prop)) (by
  simp)

-- Part.get_eq_iff_eq_some, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.get_eq_iff_eq_some.h2 : ¬∀ {α : Type} {a : Part α} {b : α}, a.Dom := fun hc_h => absurd (@hc_h (ℕ) (⊥) (0)) (by
  nofun)

-- List.IsChain.dropLast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.dropLast.h3 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α}, List.IsChain R l.dropLast := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([2, 1, 0])) (by
  decide +kernel)

-- ENat.toNat_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.toNat_pos.h1 : ¬∀ {n : ℕ∞}, n ≠ ⊤ → 0 < n.toNat := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  decide +kernel)

-- ENat.toNat_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.toNat_pos.h2 : ¬∀ {n : ℕ∞}, n ≠ 0 → 0 < n.toNat := fun hc_h => absurd (@hc_h (⊤) (by
  decide)) (by
  decide +kernel)

-- ENat.add_lt_add_iff_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.add_lt_add_iff_left.h3 : ¬∀ {m n k : ℕ∞}, k + n < k + m ↔ n < m := fun hc_h => absurd (@hc_h (1) (0) (⊤)) (by
  decide +kernel)

-- List.cons_getElem_drop_succ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_getElem_drop_succ.h3 : ¬∀ {α : Type} {l : List α} {n : ℕ}, n < l.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- Set.range_eq_empty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.range_eq_empty.h2 : ¬∀ {α ι : Type} (f : ι → α), Set.range f = ∅ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- List.Duplicate.elim_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Duplicate.elim_singleton.h3 : ¬∀ {α : Type} {x y : α}, False := fun hc_h => absurd (@hc_h (ℕ) (0) (0)) (by
  decide +kernel)

-- Set.disjoint_powerset_insert, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.disjoint_powerset_insert.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, Disjoint (𝒫 s) (Insert.insert a '' 𝒫 s) := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True}) (0)) (by
  simp)

-- Nat.dvd_lcm_of_dvd_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_lcm_of_dvd_right.h2 : ¬∀ {a b : ℕ} (c : ℕ), a ∣ c.lcm b := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- List.length_mem_cyclicPermutations, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_mem_cyclicPermutations.h3 : ¬∀ {α : Type} {l' : List α} (l : List α), l'.length = l.length := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  decide +kernel)

-- Nat.add_coprime_iff_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_coprime_iff_left.h3 : ¬∀ {a b c : ℕ}, (a + b).Coprime c ↔ a.Coprime c := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- List.rotate_eq_drop_append_take, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.rotate_eq_drop_append_take.h3 : ¬∀ {α : Type} {l : List α} {n : ℕ}, l.rotate n = List.drop n l ++ List.take n l := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (3)) (by
  decide +kernel)

-- Nat.coprime_pow_left_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_pow_left_iff.h1 : ¬∀ {n : ℕ} (a b : ℕ), (a ^ n).Coprime b ↔ a.Coprime b := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- Nat.Coprime.dvd_mul_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.dvd_mul_left.h3 : ¬∀ {m n k : ℕ}, k ∣ m * n ↔ k ∣ n := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- Nat.modEq_iff_exists_eq_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.modEq_iff_exists_eq_add.h3 : ¬∀ {n a b : ℕ}, a ≡ b [MOD n] ↔ ∃ (t : ℕ), b = a + n * t := fun hc_h => absurd (@hc_h (1) (1) (0)) (by
  (simp <;> omega))

-- Set.Nontrivial.ne_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.ne_singleton.h3 : ¬∀ {α : Type} {s : Set α} {x : α}, s ≠ {x} := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- Nat.ModEq.symm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.symm.h3 : ¬∀ {n a b : ℕ}, b ≡ a [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- Nat.ordCompl_self_pow_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordCompl_self_pow_mul.h3 : ¬∀ (n k : ℕ) {p : ℕ}, p ^ k * n / p ^ (p ^ k * n).factorization p = n / p ^ n.factorization p := fun hc_h => absurd (@hc_h (1) (1) (0)) (by
  decide +kernel)

-- List.Nodup.rotate_eq_self_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.rotate_eq_self_iff.h2 : ¬∀ {α : Type} {l : List α} {n : ℕ}, l.rotate n = l ↔ n % l.length = 0 ∨ l = [] := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (1)) (by
  decide +kernel)

-- Nat.add_div_eq_of_add_mod_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_div_eq_of_add_mod_lt.h3 : ¬∀ {a b c : ℕ}, (a + b) / c = a / c + b / c := fun hc_h => absurd (@hc_h (1) (1) (2)) (by
  decide +kernel)

-- List.IsChain.sortedLT, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.sortedLT.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedLT := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- Nat.modEq_iff_eq_of_div_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.modEq_iff_eq_of_div_eq.h3 : ¬∀ {n a b : ℕ}, a ≡ b [MOD n] ↔ a = b := fun hc_h => absurd (@hc_h (1) (0) (1)) (by
  decide +kernel)

-- Nat.ordCompl_dvd_ordCompl_of_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordCompl_dvd_ordCompl_of_dvd.h2 : ¬∀ {a b : ℕ} (p : ℕ), a / p ^ a.factorization p ∣ b / p ^ b.factorization p := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- List.IsChain.sortedLE, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.sortedLE.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedLE := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- Rat.cast_ofNat, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.cast_ofNat.h3 : ¬∀ {α : Type} [inst : DivisionRing α] (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℚ) (Rat.instDivisionRing) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.Nonempty.inr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.inr.h3 : ¬∀ {α : Type} {s t : Set α}, (s ∪ t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({x : ℕ | False})) (by
  simp)

-- Set.preimage_val_eq_univ_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.preimage_val_eq_univ_of_subset.h3 : Not
      (∀ {α : Type} {A B : Set α},
        @Eq (Set (@Set.Elem α A))
          (@Set.preimage (@Set.Elem α A) α
            (@Subtype.val α fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) A x) B)
          (@Set.univ (@Set.Elem α A))) := fun hc_h => absurd (@hc_h (Bool) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.false)) (by
  simp)

-- Antitone.sortedGE, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Antitone.sortedGE.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedGE := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- Set.encard_ne_zero_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_ne_zero_of_mem.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, s.encard ≠ 0 := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (0)) (by
  simp)

-- List.SortedLT.map_toDual, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.map_toDual.h3 : ¬∀ {α : Type} [inst : Preorder α] {l : List α}, l.SortedGT := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) ([0, 1])) (by
  decide +kernel)

-- Set.exists_subset_card_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_subset_card_eq.h3 : ¬∀ {α : Type} {s : Set α} {n : ℕ}, ∃ t ⊆ s, t.ncard = n := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (1)) (by
  simp)

-- Nat.descFactorial_mul_descFactorial, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.descFactorial_mul_descFactorial.h3 : ¬∀ {k m n : ℕ}, (n - k).descFactorial (m - k) * n.descFactorial k = n.descFactorial m := fun hc_h => absurd (@hc_h (1) (0) (0)) (by
  decide +kernel)

-- List.maximum_ne_bot_of_ne_nil, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.maximum_ne_bot_of_ne_nil.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α}, l.maximum ≠ ⊥ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([])) (by
  decide +kernel)

-- List.SortedGE.isChain, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGE.isChain.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], List.IsChain (fun (x1 x2 : α) => x1 ≥ x2) l := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.SortedLE.pairwise, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLE.pairwise.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], List.Pairwise (fun (x1 x2 : α) => x1 ≤ x2) l := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- Set.powersetCard.ofCard_coe, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Set.powersetCard.ofCard_coe.h3.der.{u_1} : ∀ {α : Type u_1} {n : Nat} {s : @Set.Elem (Finset α) (Set.powersetCard α n)},
      @Eq Nat
        (@Finset.card α
          (@Subtype.val (Finset α)
            (fun (x : Finset α) =>
              @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α)) (Set.powersetCard α n) x)
            s))
        n := by
  (intros; simp; done)
theorem HypCheckProof.Set.powersetCard.ofCard_coe.h3.{u_1} : ∀ {α : Type u_1} {n : Nat} {s : @Set.Elem (Finset α) (Set.powersetCard α n)},
      @Eq (@Set.Elem (Finset α) (Set.powersetCard α n))
        (@Set.powersetCard.ofCard α n
          (@Subtype.val (Finset α)
            (fun (x : Finset α) =>
              @Membership.mem (Finset α) (Set (Finset α)) (@Set.instMembership (Finset α)) (Set.powersetCard α n) x)
            s)
          (@HypCheckProof.Set.powersetCard.ofCard_coe.h3.der α n s))
        s := by
  intro hc_x0 hc_x1 hc_x2
  exact @Set.powersetCard.ofCard_coe hc_x0 hc_x1 hc_x2 (@HypCheckProof.Set.powersetCard.ofCard_coe.h3.der hc_x0 hc_x1 hc_x2)

-- Nat.xor_trichotomy, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.xor_trichotomy.h3 : ¬∀ {a b c : ℕ}, b ^^^ c < a ∨ c ^^^ a < b ∨ a ^^^ b < c := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- Nat.shiftLeft_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.shiftLeft_lt.h3 : ¬∀ {x n m : ℕ}, x <<< m < 2 ^ (n + m) := fun hc_h => absurd (@hc_h (1) (0) (0)) (by
  decide +kernel)

-- Nat.lt_xor_cases, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_xor_cases.h3 : ¬∀ {a b c : ℕ}, a ^^^ c < b ∨ a ^^^ b < c := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- List.sortedGE_of_getElem_ge_getElem_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sortedGE_of_getElem_ge_getElem_of_le.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedGE := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.sortedLT_of_getElem_lt_getElem_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sortedLT_of_getElem_lt_getElem_of_lt.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedLT := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.pairwise_sublists, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwise_sublists.h3 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α}, List.Pairwise (Function.onFun (List.Lex R) List.reverse) l.sublists := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0])) (by
  decide +kernel)

-- List.Pairwise.sublists', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.sublists'.h3 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α}, List.Pairwise (List.Lex (Function.swap R)) l.sublists' := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0])) (by
  decide +kernel)

-- List.IsChain.count_false_eq_count_true, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.count_false_eq_count_true.h1 : ¬∀ {l : List Bool}, Even l.length → List.count Bool.false l = List.count Bool.true l := fun hc_h => absurd (@hc_h ([Bool.false, Bool.false]) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.count_false_eq_count_true, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.count_false_eq_count_true.h2 : ¬∀ {l : List Bool}, List.IsChain (fun (x1 x2 : Bool) => x1 ≠ x2) l → List.count Bool.false l = List.count Bool.true l := fun hc_h => absurd (@hc_h ([Bool.false]) (by
  decide)) (by
  decide +kernel)

-- Set.exists_subset_ncard_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_subset_ncard_eq.h3 : ¬∀ {α : Type} {s : Set α} {k : ℕ}, ∃ t ⊆ s, t.Finite ∧ t.ncard = k := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (1)) (by
  simp)

-- Nat.pow_factorization_choose_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_factorization_choose_le.h3 : ¬∀ {p n k : ℕ}, p ^ (n.choose k).factorization p ≤ n := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- List.instIsSymmOpZipWith, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.instIsSymmOpZipWith.h3 : ¬∀ {α β : Type} (f : α → α → β), IsSymmOp (List.zipWith f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.symm_op ([0] : List ℕ) ([1] : List ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.factorization_add_factorization_choose_le_log, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_add_factorization_choose_le_log.h3 : ¬∀ {p n k : ℕ}, k.factorization p + (n.choose k).factorization p ≤ Nat.log p n := fun hc_h => absurd (@hc_h (2) (0) (2)) (by
  decide +kernel)

-- Fin.le_of_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.le_of_injective.h3 : ¬∀ {m n : ℕ} (f : Fin m → Fin n), m ≤ n := fun hc_h => absurd (@hc_h (2) (1) (fun (a : Fin 2) => (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- ZMod.ringEquivCongr_intCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.ringEquivCongr_intCast.h2 : ¬∀ {a b : ℕ} (z : ℤ), a = b := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- Function.Embedding.embFinTwo_apply_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.embFinTwo_apply_zero.h3 : ¬∀ {α : Type} {a b : α}, a ≠ b := fun hc_h => absurd (@hc_h (ℕ) (0) (0)) (by
  decide +kernel)

-- Nat.Prime.odd_of_ne_two, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.odd_of_ne_two.h1 : ¬∀ {p : ℕ}, p ≠ 2 → Odd p := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.odd_of_ne_two, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.odd_of_ne_two.h2 : ¬∀ {p : ℕ}, Nat.Prime p → Odd p := fun hc_h => absurd (@hc_h (2) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_choose_pow_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose_pow_iff.h3 : ¬∀ {p n k : ℕ}, p ∣ (p ^ n).choose k ↔ k ≠ 0 ∧ k ≠ p ^ n := fun hc_h => absurd (@hc_h (1) (0) (0)) (by
  decide +kernel)

-- Function.Embedding.embFinTwo_apply_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Embedding.embFinTwo_apply_one.h3 : ¬∀ {α : Type} {a b : α}, a ≠ b := fun hc_h => absurd (@hc_h (ℕ) (0) (0)) (by
  decide +kernel)

-- Set.encard_union_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_union_eq.h3 : ¬∀ {α : Type} {s t : Set α}, (s ∪ t).encard = s.encard + t.encard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  norm_num)

-- Fin.ofFn_take_get, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.ofFn_take_get.h3 : ¬∀ {α : Type} {m : ℕ} (l : List α), m ≤ l.length := fun hc_h => absurd (@hc_h (ℕ) (1) ([])) (by
  decide +kernel)

-- Fin.get_take_eq_take_get_comp_cast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.get_take_eq_take_get_comp_cast.h3 : ¬∀ {α : Type} {m : ℕ} (l : List α), m ≤ l.length := fun hc_h => absurd (@hc_h (ℕ) (1) ([])) (by
  decide +kernel)

-- Multiset.powerset_aux'_perm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.powerset_aux'_perm.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, (Multiset.powersetAux' l₁).Perm (Multiset.powersetAux' l₂) := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  decide +kernel)

-- Fintype.card_eq_one_of_forall_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_eq_one_of_forall_eq.h3 : ¬∀ {α : Type} [inst : Fintype α] {i : α}, Fintype.card α = 1 := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) (Bool.false)) (by
  decide +kernel)

-- Fintype.exists_ne_of_one_lt_card, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.exists_ne_of_one_lt_card.h2 : ¬∀ {α : Type} [inst : Fintype α] (a : α), ∃ (b : α), b ≠ a := fun hc_h => absurd (@hc_h (Unit) (PUnit.fintype) (PUnit.unit)) (by
  decide +kernel)

-- List.Nodup.of_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.of_cons.h3 : ¬∀ {α : Type} {l : List α} {a : α}, l.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (0)) (by
  decide +kernel)

-- Set.encard_sdiff_singleton_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_sdiff_singleton_of_mem.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, (s \ {a}).encard = s.encard - 1 := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- List.nodup_attachWith, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nodup_attachWith.h3 : ¬∀ {α : Type} {l : List α} {P : α → Prop}, ∀ x ∈ l, P x := fun hc_h => absurd (@hc_h (ℕ) ([1]) (fun n => n = 0 : ℕ → Prop)) (by
  decide +kernel)

-- Set.ncard_le_ncard_diff_add_ncard, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_le_ncard_diff_add_ncard.h3 : ¬∀ {α : Type} (s t : Set α), s.ncard ≤ (s \ t).ncard + t.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | True})) (by
  simp)

-- Set.image_univ_of_surjective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_univ_of_surjective.h3 : ¬∀ {β ι : Type} {f : ι → β}, f '' Set.univ = Set.univ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Set.sigmaToiUnion_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sigmaToiUnion_injective.h3 : ¬∀ {α β : Type} (t : α → Set β), Function.Injective (Set.sigmaToiUnion t) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun (a : Bool) => {n : ℕ | n = 0})) (by
  (simp <;> decide))

-- Set.subsingleton_range, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subsingleton_range.h2 : ¬∀ {β α : Type} (f : α → β), (Set.range f).Subsingleton := fun hc_h => absurd (@hc_h (Bool) (Bool) (not : Bool → Bool)) (by
  decide +kernel)

-- Int.cast_eq_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.cast_eq_one.h2 : Not
      (∀ {α : Type} [inst : AddGroupWithOne α] {n : Int},
        Iff
          (@Eq α (@Int.cast α (@AddGroupWithOne.toIntCast α inst) n)
            (@OfNat.ofNat α (nat_lit 1)
              (@One.toOfNat1 α (@AddMonoidWithOne.toOne α (@AddGroupWithOne.toAddMonoidWithOne α inst)))))
          (@Eq Int n (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := fun hc_h => absurd (@hc_h (Bool) (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool)) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) (by
  decide +kernel)

-- Set.subsingleton_of_subsingleton_inter_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subsingleton_of_subsingleton_inter_right.h3 : ¬∀ {α : Type} {s : Set α} {t : Set α}, t.Subsingleton := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({x : Bool | True})) (by
  decide +kernel)

-- Finset.singleton_ne_univ, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.singleton_ne_univ.h2 : ¬∀ {α : Type} [inst : Fintype α] (a : α), {a} ≠ Finset.univ := fun hc_h => absurd (@hc_h (Unit) (PUnit.fintype) (PUnit.unit)) (by
  decide +kernel)

-- Finset.singleton_eq_univ, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.singleton_eq_univ.h2 : ¬∀ {α : Type} [inst : Fintype α] (a : α), {a} = Finset.univ := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) (Bool.false)) (by
  decide +kernel)

-- Int.cast_eq_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.cast_eq_zero.h2 : Not
      (∀ {α : Type} [inst : AddGroupWithOne α] {n : Int},
        Iff
          (@Eq α (@Int.cast α (@AddGroupWithOne.toIntCast α inst) n)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@NegZeroClass.toZero α
                  (@SubNegZeroMonoid.toNegZeroClass α
                    (@SubtractionMonoid.toSubNegZeroMonoid α
                      (@AddGroup.toSubtractionMonoid α (@AddGroupWithOne.toAddGroup α inst))))))))
          (@Eq Int n (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := fun hc_h => absurd (@hc_h (Bool) (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool)) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))) (by
  decide +kernel)

-- Even.intCast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Even.intCast.h3 : Not
      (∀ {α : Type} [inst : AddGroupWithOne α] {n : Int},
        @Even α
          (@AddSemigroup.toAdd α
            (@AddMonoid.toAddSemigroup α (@AddMonoidWithOne.toAddMonoid α (@AddGroupWithOne.toAddMonoidWithOne α inst))))
          (@Int.cast α (@AddGroupWithOne.toIntCast α inst) n)) := fun hc_h => absurd (@hc_h (Bool) (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool)) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  nofun)

-- Set.subsingleton_of_subset_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subsingleton_of_subset_singleton.h3 : ¬∀ {α : Type} {a : α} {s : Set α}, s.Subsingleton := fun hc_h => absurd (@hc_h (Bool) (Bool.false) ({x : Bool | True})) (by
  decide +kernel)

-- Set.Nonempty.inl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.inl.h3 : ¬∀ {α : Type} {s t : Set α}, (s ∪ t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({x : ℕ | False})) (by
  simp)

-- Nat.clog_le_of_le_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_le_of_le_pow.h3 : ¬∀ {b x y : ℕ}, Nat.clog b x ≤ y := fun hc_h => absurd (@hc_h (2) (2) (0)) (by
  decide +kernel)

-- Set.nontrivial_of_exists_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_of_exists_lt.h3 : ¬∀ {α : Type} {s : Set α} [inst : Preorder α], s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (Nat.instPreorder)) (by
  simp)

-- Int.Ico_filter_dvd_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.Ico_filter_dvd_card.h3 : Not
      (∀ (a b : Int) {r : Int},
        @Eq Int
          (@Nat.cast Int instNatCastInt
            (@Finset.card Int
              ({x ∈ @Finset.Ico Int Int.instPreorder Int.instLocallyFiniteOrder a b | @Dvd.dvd Int Int.instDvd r x})))
          (@Max.max Int Int.instMax
            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
              (@Int.ceil Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing
                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast b)
                  (@Int.cast Rat Rat.instIntCast r)))
              (@Int.ceil Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing
                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast a)
                  (@Int.cast Rat Rat.instIntCast r))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- Set.nontrivial_iff_ne_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_iff_ne_singleton.h3 : ¬∀ {α : Type} {a : α} {s : Set α}, s.Nontrivial ↔ s ≠ {a} := fun hc_h => absurd (@hc_h (ℕ) (1) ({n : ℕ | n = 0})) (by
  simp)

-- Int.Ioc_filter_dvd_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.Ioc_filter_dvd_eq.h3 : ¬∀ (a b : ℤ) {r : ℤ}, 0 < r := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- Nat.count_modEq_card_eq_ceil, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_modEq_card_eq_ceil.h2 : Not
      (∀ (b : Nat) {r : Nat} (v : Nat),
        @Eq Int
          (@Nat.cast Int instNatCastInt
            (@Nat.count (fun (x : Nat) => r.ModEq x v) (fun (a : Nat) => @Nat.instDecidableModEq r a v) b))
          (@Int.ceil Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing
            (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
              (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) (@Nat.cast Rat Rat.instNatCast b)
                (@Nat.cast Rat Rat.instNatCast (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) v r)))
              (@Nat.cast Rat Rat.instNatCast r)))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Subtype.coe_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.coe_mk.h3 : ¬∀ {α : Type} {p : α → Prop} (a : α), p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (1)) (by
  decide +kernel)

-- Set.Infinite.exists_subset_card_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.exists_subset_card_eq.h2 : ¬∀ {α : Type} {s : Set α} (n : ℕ), ∃ (t : Finset α), ↑t ⊆ s ∧ t.card = n := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (1)) (by
  simp)

-- Fin.exists_eq_add_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.exists_eq_add_of_lt.h3 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, ∃ k < b, k + 1 ≤ b ∧ b = a + k + 1 := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.dropWhile_get_zero_not, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dropWhile_get_zero_not.h3 : ¬∀ {α : Type} (p : α → Bool) (l : List α), 0 < (List.dropWhile p l).length := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) ([])) (by
  decide +kernel)

-- List.rdropWhile_last_not, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.rdropWhile_last_not.h3 : ¬∀ {α : Type} (p : α → Bool) (l : List α), List.rdropWhile p l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) ([])) (by
  decide +kernel)

-- Nat.exists_dvd_of_not_prime, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_dvd_of_not_prime.h1 : ¬∀ {n : ℕ}, ¬Nat.Prime n → ∃ (m : ℕ), m ∣ n ∧ m ≠ 1 ∧ m ≠ n := fun hc_h => absurd (@hc_h (1) (by
  decide)) (by
  simp)

-- List.toFinset_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.toFinset_eq.h3 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α}, l.Nodup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0, 0])) (by
  decide +kernel)

-- Fin.succ_ne_last_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succ_ne_last_of_lt.h3 : ¬∀ {n : ℕ} {p : Fin n} {i : Fin n}, i.succ ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Nodup.mem_offDiag, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.mem_offDiag.h2 : ¬∀ {α : Type} {l : List α} {x : α × α}, x ∈ l.offDiag ↔ x.1 ∈ l ∧ x.2 ∈ l ∧ x.1 ≠ x.2 := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) ((0, 0))) (by
  decide +kernel)

-- List.Ico.filter_lt_of_top_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.filter_lt_of_top_le.h3 : ¬∀ {n m l : ℕ}, List.filter (fun (x : ℕ) => Decidable.decide (x < l)) (List.Ico n m) = List.Ico n m := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- List.Ico.filter_le_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.filter_le_of_le.h3 : ¬∀ {n m l : ℕ}, List.filter (fun (x : ℕ) => Decidable.decide (l ≤ x)) (List.Ico n m) = List.Ico l m := fun hc_h => absurd (@hc_h (1) (1) (0)) (by
  decide +kernel)

-- List.Ico.filter_le_of_le_bot, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.filter_le_of_le_bot.h3 : ¬∀ {n m l : ℕ}, List.filter (fun (x : ℕ) => Decidable.decide (l ≤ x)) (List.Ico n m) = List.Ico n m := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- Nat.choose_symm_of_eq_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_symm_of_eq_add.h3 : ¬∀ {n a b : ℕ}, n.choose a = n.choose b := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- Nat.choose_le_choose, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_le_choose.h3 : ¬∀ {a b : ℕ} (c : ℕ), a.choose c ≤ b.choose c := fun hc_h => absurd (@hc_h (1) (0) (1)) (by
  decide +kernel)

-- Fin.exists_succAbove_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.exists_succAbove_eq.h3 : ¬∀ {n : ℕ} {x y : Fin (n + 1)}, ∃ (z : Fin n), y.succAbove z = x := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.getElem_inits, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_inits.h3 : ¬∀ {α : Type} (l : List α) (n : ℕ), n < l.inits.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (1)) (by
  decide +kernel)

-- finCongr_symm_apply_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finCongr_symm_apply_coe.h2 : ¬∀ {n m : ℕ} (k : Fin n), m = n := fun hc_h => absurd (@hc_h (1) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- EReal.toReal_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toReal_pos.h1 : ¬∀ {x : EReal}, x ≠ ⊤ → 0 < x.toReal := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  simp)

-- EReal.toReal_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toReal_pos.h2 : ¬∀ {x : EReal}, 0 < x → 0 < x.toReal := fun hc_h => absurd (@hc_h (⊤) (by
  decide)) (by
  simp)

-- EReal.add_lt_of_lt_sub, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_lt_of_lt_sub.h3 : ¬∀ {a b c : EReal}, a + c < b := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- List.flatten_splitLengths, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.flatten_splitLengths.h3 : ¬∀ {α : Type} (l : List α) (sz : List ℕ), (sz.splitLengths l).flatten = l := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([])) (by
  decide +kernel)

-- List.getLast?_flatten_replicate, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getLast?_flatten_replicate.h2 : ¬∀ {α : Type} {n : ℕ} (l : List α), (List.replicate n l).flatten.getLast? = l.getLast? := fun hc_h => absurd (@hc_h (ℕ) (0) ([0])) (by
  decide +kernel)

-- List.IsSuffix.flatten, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsSuffix.flatten.h3 : ¬∀ {α : Type} {l₁ l₂ : List (List α)}, l₁.flatten <:+ l₂.flatten := fun hc_h => absurd (@hc_h (ℕ) ([[0]]) ([])) (by
  decide +kernel)

-- EReal.sub_le_of_le_add', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.sub_le_of_le_add'.h3 : ¬∀ {a b c : EReal}, a - b ≤ c := fun hc_h => absurd (@hc_h (1) (0) (0)) (by
  simp)

-- List.IsPrefix.flatten, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.flatten.h3 : ¬∀ {α : Type} {l₁ l₂ : List (List α)}, l₁.flatten <+: l₂.flatten := fun hc_h => absurd (@hc_h (ℕ) ([[0]]) ([])) (by
  decide +kernel)

-- List.IsInfix.flatten, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsInfix.flatten.h3 : ¬∀ {α : Type} {l₁ l₂ : List (List α)}, l₁.flatten <:+: l₂.flatten := fun hc_h => absurd (@hc_h (ℕ) ([[0]]) ([])) (by
  decide +kernel)

-- Fin.succAbove_succ_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_succ_of_le.h3 : ¬∀ {n : ℕ} (p i : Fin n), p.succ.succAbove i = i.castSucc := fun hc_h => absurd (@hc_h (2) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- List.getElem_tails, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_tails.h3 : ¬∀ {α : Type} (l : List α) (n : ℕ), n < l.tails.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (1)) (by
  decide +kernel)

-- Fin.castLE_castSucc, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castLE_castSucc.h3 : ¬∀ {n m : ℕ} (i : Fin n), n + 1 ≤ m := fun hc_h => absurd (@hc_h (1) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Sym2.map.injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.map.injective.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Injective (Sym2.map f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ => 0 : Bool → ℕ)) (by
  decide +kernel)

-- Fin.succ_succAbove_predAbove, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succ_succAbove_predAbove.h3 : ¬∀ {n : ℕ} {p : Fin n} {i : Fin (n + 1)}, p.succ.succAbove (p.predAbove i) = i := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Fin.predAbove_of_castSucc_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_of_castSucc_lt.h3 : ¬∀ {n : ℕ} (p : Fin n) (i : Fin (n + 1)), p.castSucc < i := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Fin.succAbove_pred_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_pred_of_lt.h3 : ¬∀ {n : ℕ} (p i : Fin (n + 1)), p < i := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Nat.dvd_iff_dvd_digits_sum, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_iff_dvd_digits_sum.h2 : ¬∀ (b b' n : ℕ), b ∣ n ↔ b ∣ (b'.digits n).sum := fun hc_h => absurd (@hc_h (2) (2) (2)) (by
  decide +kernel)

-- Fin.succAbove_castSucc_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_castSucc_of_le.h3 : ¬∀ {n : ℕ} (p i : Fin n), p.castSucc.succAbove i = i.succ := fun hc_h => absurd (@hc_h (2) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Fin.succAbove_succ_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_succ_of_lt.h3 : ¬∀ {n : ℕ} (p i : Fin n), p.succ.succAbove i = i.succ := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Finset.empty_mem_ssubsets, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.empty_mem_ssubsets.h3.{u_1} : ¬∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset α}, ∅ ∈ s.ssubsets := by
  (simp_all; done)

-- Fin.lt_pred_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.lt_pred_iff.h3 : ¬∀ {n : ℕ} {j : Fin n} {i : Fin (n + 1)}, i ≠ 0 := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Nat.count_nth_of_infinite, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_nth_of_infinite.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] (n : ℕ), Nat.count p (Nat.nth p n) = n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (1)) (by
  simp)

-- Fin.predAbove_succ_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_succ_of_le.h3 : ¬∀ {n : ℕ} (p i : Fin n), p.predAbove i.succ = i := fun hc_h => absurd (@hc_h (2) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Nat.nth_lt_nth, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_lt_nth.h1 : ¬∀ {p : ℕ → Prop} {k n : ℕ}, Nat.nth p k < Nat.nth p n ↔ k < n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (0) (1)) (by
  simp)

-- Nat.filter_range_nth_eq_insert, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.filter_range_nth_eq_insert.h3 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {k : ℕ},
        {n ∈ Finset.range (Nat.nth p (k + 1)) | p n} = Insert.insert (Nat.nth p k) ({n ∈ Finset.range (Nat.nth p k) | p n}) := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (0)) (by
  simp)

-- Int.ModEq.symm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.symm.h3 : ¬∀ {n a b : ℤ}, b ≡ a [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- Nat.count_nth, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_nth.h3 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {n : ℕ}, Nat.count p (Nat.nth p n) = n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (1)) (by
  simp)

-- Fin.succAbove_predAbove, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_predAbove.h3 : ¬∀ {n : ℕ} {p : Fin n} {i : Fin (n + 1)}, p.castSucc.succAbove (p.predAbove i) = i := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Nat.filter_range_nth_eq_insert_of_infinite, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.filter_range_nth_eq_insert_of_infinite.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] (k : ℕ),
        {n ∈ Finset.range (Nat.nth p (k + 1)) | p n} = Insert.insert (Nat.nth p k) ({n ∈ Finset.range (Nat.nth p k) | p n}) := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (0)) (by
  simp)

-- Set.nontrivial_pair, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_pair.h3 : Not
      (∀ {α : Type} {x y : α},
        @Set.Nontrivial α
          (@Insert.insert α (Set α) (@Set.instInsert α) x (@Singleton.singleton α (Set α) (@Set.instSingletonSet α) y))) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  simp)

-- List.head?_append_of_ne_nil, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.head?_append_of_ne_nil.h3 : ¬∀ {α : Type} (l₁ : List α) {l₂ : List α}, (l₁ ++ l₂).head? = l₁.head? := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  decide +kernel)

-- Function.Injective.list_map, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.list_map.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Injective (List.map f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Fin.succAbove_eq_last_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_eq_last_iff.h3 : ¬∀ {n : ℕ} {a : Fin (n + 2)} {b : Fin (n + 1)}, a.succAbove b = Fin.last (n + 1) ↔ b = Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- HasSSubset.SSubset.lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.HasSSubset.SSubset.lt.h3 : ¬∀ {α : Type} {s t : Set α}, s ⊂ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- List.Sublist.flatten, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.flatten.h3 : ¬∀ {α : Type} {l₁ l₂ : List (List α)}, l₁.flatten.Sublist l₂.flatten := fun hc_h => absurd (@hc_h (ℕ) ([[0]]) ([])) (by
  decide +kernel)

-- Ordnode.Raised.add_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Raised.add_left.h3 : ¬∀ (k : ℕ) {n m : ℕ}, Ordnode.Raised (k + n) (k + m) := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  nofun)

-- EReal.bot_div_of_neg_ne_bot, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.bot_div_of_neg_ne_bot.h1 : ¬∀ {a : EReal}, a ≠ ⊥ → ⊥ / a = ⊤ := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  simp)

-- EReal.bot_div_of_neg_ne_bot, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.bot_div_of_neg_ne_bot.h2 : ¬∀ {a : EReal}, a < 0 → ⊥ / a = ⊤ := fun hc_h => absurd (@hc_h (⊥) (by
  decide)) (by
  simp)

-- Nat.digits_lt_base', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_lt_base'.h3 : ¬∀ {b : ℕ} {m : ℕ} {d : ℕ}, d < b + 2 := fun hc_h => absurd (@hc_h (0) (0) (2)) (by
  decide +kernel)

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

-- Function.Injective.image_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.image_injective.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Injective (Set.image f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Set.eq_of_mem_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_mem_singleton.h3 : ¬∀ {α : Type} {x y : α}, x = y := fun hc_h => absurd (@hc_h (ℕ) (0) (1)) (by
  decide +kernel)

-- List.ext_getElem?', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.ext_getElem?'.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  decide +kernel)

-- List.tail_append_singleton_of_ne_nil, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.tail_append_singleton_of_ne_nil.h3 : ¬∀ {α : Type} {a : α} {l : List α}, (l ++ [a]).tail = l.tail ++ [a] := fun hc_h => absurd (@hc_h (ℕ) (0) ([])) (by
  decide +kernel)

-- EReal.inv_pos_of_pos_ne_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.inv_pos_of_pos_ne_top.h1 : ¬∀ {a : EReal}, a ≠ ⊤ → 0 < a⁻¹ := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  simp)

-- EReal.inv_pos_of_pos_ne_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.inv_pos_of_pos_ne_top.h2 : ¬∀ {a : EReal}, 0 < a → 0 < a⁻¹ := fun hc_h => absurd (@hc_h (⊤) (by
  decide)) (by
  simp)

-- Fin.castPred_le_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_le_iff.h3 : ¬∀ {n : ℕ} {j : Fin n} {i : Fin (n + 1)}, i ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- List.getLast_append_of_right_ne_nil, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getLast_append_of_right_ne_nil.h3 : ¬∀ {α : Type} (l₁ l₂ : List α), l₂ ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([]) ([])) (by
  decide +kernel)

-- Ordnode.eraseMin.valid, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.eraseMin.valid.h3 : ¬∀ {α : Type} [inst : Preorder α] {t : Ordnode α}, t.eraseMin.Valid := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 0 (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil))) (by
  nofun)

-- List.mem_getLast?_eq_getLast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_getLast?_eq_getLast.h3 : ¬∀ {α : Type} {l : List α} {x : α}, ∃ (h : l ≠ []), x = l.getLast h := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- List.Vector.toList_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Vector.toList_mk.h3 : ¬∀ {α : Type} {n : ℕ} (v : List α), v.length = n := fun hc_h => absurd (@hc_h (ℕ) (0) ([0])) (by
  decide +kernel)

-- List.head?_flatten_replicate, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.head?_flatten_replicate.h2 : ¬∀ {α : Type} {n : ℕ} (l : List α), (List.replicate n l).flatten.head? = l.head? := fun hc_h => absurd (@hc_h (ℕ) (0) ([0])) (by
  decide +kernel)

-- List.head!_mem_head?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.head!_mem_head?.h3 : ¬∀ {α : Type} [inst : Inhabited α] {l : List α}, l.head! ∈ l.head? := fun hc_h => absurd (@hc_h (ℕ) (instInhabitedNat) ([])) (by
  decide +kernel)

-- Ordnode.Valid.dual, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid.dual.h3 : Not
      (∀ {α : Type} [inst : Preorder α] {t : Ordnode α},
        @Ordnode.Valid (OrderDual α) (@OrderDual.instPreorder α inst) (@Ordnode.dual (OrderDual α) t)) := fun hc_h => absurd (@hc_h (Nat) (Nat.instPreorder) (@Ordnode.node Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Ordnode.nil Nat)
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Ordnode.nil Nat))) (by
  nofun)

-- EReal.bot_div_of_pos_ne_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.bot_div_of_pos_ne_top.h1 : ¬∀ {a : EReal}, a ≠ ⊤ → ⊥ / a = ⊥ := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  simp)

-- EReal.bot_div_of_pos_ne_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.bot_div_of_pos_ne_top.h2 : ¬∀ {a : EReal}, 0 < a → ⊥ / a = ⊥ := fun hc_h => absurd (@hc_h (⊤) (by
  decide)) (by
  simp)

-- Fin.castLEEmb_apply, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castLEEmb_apply.h2 : ¬∀ {n m : ℕ} (i : Fin n), n ≤ m := fun hc_h => absurd (@hc_h (1) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.natAdd_castLEEmb_apply_val, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.natAdd_castLEEmb_apply_val.h2 : ¬∀ {n m : ℕ} (a : Fin n), n ≤ m := fun hc_h => absurd (@hc_h (1) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.prev_head_eq_getLast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_head_eq_getLast.h3 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α), l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([])) (by
  decide +kernel)

-- Nat.ofDigits_monotone, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofDigits_monotone.h3 : ¬∀ {p q : ℕ} (L : List ℕ), Nat.ofDigits p L ≤ Nat.ofDigits q L := fun hc_h => absurd (@hc_h (1) (0) ([0, 1])) (by
  decide +kernel)

-- Int.ModEq.dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.dvd.h3 : ¬∀ {n a b : ℤ}, n ∣ b - a := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- List.get_reverse', hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.get_reverse'.h3.der.{u} : ∀ {α : Type u} (l : List α) (n : Fin l.reverse.length), l.length - 1 - ↑n < l.length := by
  (intros; grind)
theorem HypCheckProof.List.get_reverse'.h3.{u} : ∀ {α : Type u} (l : List α) (n : Fin l.reverse.length),
      l.reverse.get n = l.get (⟨l.length - 1 - ↑n, HypCheckProof.List.get_reverse'.h3.der l n⟩ : Fin l.length) := by
  intro hc_x0 hc_x1 hc_x2
  exact @List.get_reverse' hc_x0 hc_x1 hc_x2 (@HypCheckProof.List.get_reverse'.h3.der hc_x0 hc_x1 hc_x2)

-- Set.Nonempty.exists_const, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.exists_const.h2 : ¬∀ {α : Type} {s : Set α} {p : Prop}, (∃ x ∈ s, p) ↔ p := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (True)) (by
  simp)

-- Function.Surjective.list_map, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.list_map.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Surjective (List.map f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ => true : Bool → Bool)) (by
  (simp <;> decide))

-- Nat.self_mod_pow_eq_ofDigits_take, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.self_mod_pow_eq_ofDigits_take.h3 : ¬∀ {p : ℕ} (i n : ℕ), n % p ^ i = Nat.ofDigits p (List.take i (p.digits n)) := fun hc_h => absurd (@hc_h (1) (1) (1)) (by
  decide +kernel)

-- List.head!_mem_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.head!_mem_self.h3 : ¬∀ {α : Type} [inst : Inhabited α] {l : List α}, l.head! ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instInhabitedNat) ([])) (by
  decide +kernel)

-- Set.singleton_inter_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.singleton_inter_of_mem.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, {a} ∩ s = {a} := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1)) (by
  (simp <;> omega))

-- List.map_mk_disjoint_sym2, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map_mk_disjoint_sym2.h3 : ¬∀ {α : Type} (x : α) (xs : List α), (List.map (fun (y : α) => s(x, y)) xs).Disjoint xs.sym2 := fun hc_h => absurd (@hc_h (ℕ) (0) ([0])) (by
  (simp <;> decide))

-- List.Perm.sym2, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.sym2.h3 : ¬∀ {α : Type} {xs ys : List α}, xs.sym2.Perm ys.sym2 := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  decide +kernel)

-- List.map_mk_sublist_sym2, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map_mk_sublist_sym2.h3 : ¬∀ {α : Type} (x : α) (xs : List α), (List.map (fun (y : α) => s(x, y)) xs).Sublist xs.sym2 := fun hc_h => absurd (@hc_h (ℕ) (0) ([1])) (by
  decide +kernel)

-- Nat.cast_ofNat, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.cast_ofNat.h3 : ¬∀ {R : Type} {n : ℕ} [inst : NatCast R], n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (0) (instNatCastNat)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.singleton_inter_of_notMem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.singleton_inter_of_notMem.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, {a} ∩ s = ∅ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- Nat.findGreatest_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.findGreatest_eq.h3 : ¬∀ {P : ℕ → Prop} [inst : DecidablePred P] {n : ℕ}, Nat.findGreatest P n = n := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (1)) (by
  decide +kernel)

-- Nat.mem_primeFactorsList_mul_of_coprime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mem_primeFactorsList_mul_of_coprime.h2 : ¬∀ {a b : ℕ} (p : ℕ), p ∈ (a * b).primeFactorsList ↔ p ∈ a.primeFactorsList ∪ b.primeFactorsList := fun hc_h => absurd (@hc_h (0) (2) (2)) (by
  decide +kernel)

-- Set.nonempty_of_ssubset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nonempty_of_ssubset.h3 : ¬∀ {α : Type} {s t : Set α}, (t \ s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  nofun)

-- Nat.self_div_pow_eq_ofDigits_drop, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.self_div_pow_eq_ofDigits_drop.h3 : ¬∀ {p : ℕ} (i n : ℕ), n / p ^ i = Nat.ofDigits p (List.drop i (p.digits n)) := fun hc_h => absurd (@hc_h (1) (1) (1)) (by
  decide +kernel)

-- Set.inter_eq_self_of_subset_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_eq_self_of_subset_left.h3 : ¬∀ {α : Type} {s t : Set α}, s ∩ t = s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Nat.minFac_le_div, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.minFac_le_div.h1 : ¬∀ {n : ℕ}, ¬Nat.Prime n → n.minFac ≤ n / n.minFac := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  decide +kernel)

-- Nat.minFac_le_div, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.minFac_le_div.h2 : ¬∀ {n : ℕ}, 0 < n → n.minFac ≤ n / n.minFac := fun hc_h => absurd (@hc_h (2) (by
  decide)) (by
  decide +kernel)

-- Nat.cast_pred, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.cast_pred.h3 : Not
      (∀ {R : Type} [inst : AddGroupWithOne R] {n : Nat},
        @Eq R
          (@Nat.cast R (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R inst))
            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HSub.hSub R R R
            (@instHSub R (@SubNegMonoid.toSub R (@AddGroup.toSubNegMonoid R (@AddGroupWithOne.toAddGroup R inst))))
            (@Nat.cast R (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R inst)) n)
            (@OfNat.ofNat R (nat_lit 1)
              (@One.toOfNat1 R (@AddMonoidWithOne.toOne R (@AddGroupWithOne.toAddMonoidWithOne R inst)))))) := fun hc_h => absurd (@hc_h (Bool) (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Set.ofPred_mem_list_eq_singleton_of_nodup, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ofPred_mem_list_eq_singleton_of_nodup.h2 : ¬∀ {α : Type} {l : List α} {a : α}, {x : α | x ∈ l} = {a} ↔ l = [a] := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (0)) (by
  simp)

-- Int.cast_ofNat, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.cast_ofNat.h3 : ¬∀ {R : Type} [inst : AddGroupWithOne R] (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (Bool) (instBooleanRingBool.toAddGroupWithOne) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.subsingleton_iff_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subsingleton_iff_singleton.h3 : ¬∀ {α : Type} {s : Set α} {x : α}, s.Subsingleton ↔ s = {x} := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- Set.subsingleton_of_subsingleton_inter_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subsingleton_of_subsingleton_inter_left.h3 : ¬∀ {α : Type} {s : Set α} {t : Set α}, s.Subsingleton := fun hc_h => absurd (@hc_h (Bool) ({x : Bool | True}) ({b : Bool | b = Bool.true})) (by
  decide +kernel)

-- Nat.minFac_sq_le_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.minFac_sq_le_self.h1 : ¬∀ {n : ℕ}, ¬Nat.Prime n → n.minFac ^ 2 ≤ n := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  decide +kernel)

-- Nat.minFac_sq_le_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.minFac_sq_le_self.h2 : ¬∀ {n : ℕ}, 0 < n → n.minFac ^ 2 ≤ n := fun hc_h => absurd (@hc_h (2) (by
  decide)) (by
  decide +kernel)

-- Nat.prime_of_coprime, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prime_of_coprime.h1 : ¬∀ (n : ℕ), (∀ m < n, m ≠ 0 → n.Coprime m) → Nat.Prime n := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  decide +kernel)

-- Nat.prime_of_coprime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prime_of_coprime.h2 : ¬∀ (n : ℕ), 1 < n → Nat.Prime n := fun hc_h => absurd (@hc_h (4) (by
  decide)) (by
  decide +kernel)

-- Int.sq_eq_one_of_sq_le_three, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.sq_eq_one_of_sq_le_three.h1 : ¬∀ {x : ℤ}, x ≠ 0 → x ^ 2 = 1 := fun hc_h => absurd (@hc_h (2) (by
  decide)) (by
  decide +kernel)

-- Int.sq_eq_one_of_sq_le_three, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.sq_eq_one_of_sq_le_three.h2 : ¬∀ {x : ℤ}, x ^ 2 ≤ 3 → x ^ 2 = 1 := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  decide +kernel)

-- Finset.filterMap_empty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.filterMap_empty.h3 : ¬∀ {α β : Type} (f : α → Option β) (a a' : α), ∀ b ∈ f a, b ∈ f a' → a = a' := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun (a : Bool) => Option.some 0)) (by
  decide +kernel)

-- Nat.digits_append_digits, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_append_digits.h3 : ¬∀ {b m n : ℕ}, b.digits n ++ b.digits m = b.digits (n + b ^ (b.digits n).length * m) := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- ZMod.cast_descFactorial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.cast_descFactorial.h2 : Not
      (∀ {n p : Nat},
        @Eq (ZMod p)
          (@Nat.cast (ZMod p)
            (@AddMonoidWithOne.toNatCast (ZMod p)
              (@AddGroupWithOne.toAddMonoidWithOne (ZMod p)
                (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p)))))
            ((@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) p
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).descFactorial
              n))
          (@HMul.hMul (ZMod p) (ZMod p) (ZMod p)
            (@instHMul (ZMod p)
              (@Distrib.toMul (ZMod p)
                (@instDistribOfSemiring (ZMod p)
                  (@CommSemiring.toSemiring (ZMod p) (@CommRing.toCommSemiring (ZMod p) (ZMod.commRing p))))))
            (@HPow.hPow (ZMod p) Nat (ZMod p)
              (@instHPow (ZMod p) Nat
                (@NPow.toPow (ZMod p)
                  (@Monoid.toNPow (ZMod p)
                    (@Semiring.toMonoid (ZMod p)
                      (@CommSemiring.toSemiring (ZMod p) (@CommRing.toCommSemiring (ZMod p) (ZMod.commRing p)))))))
              (@Neg.neg (ZMod p)
                (@NegZeroClass.toNeg (ZMod p)
                  (@SubNegZeroMonoid.toNegZeroClass (ZMod p)
                    (@SubtractionMonoid.toSubNegZeroMonoid (ZMod p)
                      (@SubtractionCommMonoid.toSubtractionMonoid (ZMod p)
                        (@AddCommGroup.toDivisionAddCommMonoid (ZMod p)
                          (@Ring.toAddCommGroup (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p))))))))
                (@OfNat.ofNat (ZMod p) (nat_lit 1)
                  (@One.toOfNat1 (ZMod p)
                    (@AddMonoidWithOne.toOne (ZMod p)
                      (@AddGroupWithOne.toAddMonoidWithOne (ZMod p)
                        (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p))))))))
              n)
            (@Nat.cast (ZMod p)
              (@AddMonoidWithOne.toNatCast (ZMod p)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod p)
                  (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p)))))
              n.factorial))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Int.neg_eq_neg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.neg_eq_neg.h2 : ¬∀ {a b : ℤ}, a = b := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Int.natMod_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natMod_lt.h2 : ¬∀ {m : ℤ} {n : ℕ}, m.natMod ↑n < n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- List.Nodup.of_sublists', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.of_sublists'.h2 : ¬∀ {α : Type} {l : List α}, l.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0])) (by
  decide +kernel)

-- List.Nodup.of_sublists, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.of_sublists.h2 : ¬∀ {α : Type} {l : List α}, l.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0])) (by
  decide +kernel)

-- Nat.dvd_of_factorization_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_of_factorization_pos.h2 : ¬∀ {n p : ℕ}, p ∣ n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.ordCompl_eq_self_iff_zero_or_not_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordCompl_eq_self_iff_zero_or_not_dvd.h2 : ¬∀ (n : ℕ) {p : ℕ}, n / p ^ n.factorization p = n ↔ n = 0 ∨ ¬p ∣ n := fun hc_h => absurd (@hc_h (1) (1)) (by
  decide +kernel)

-- Set.subsingleton_of_subsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subsingleton_of_subsingleton.h1 : ¬∀ {α : Type} {s : Set α}, s.Subsingleton := fun hc_h => absurd (@hc_h (Bool) ({x : Bool | True})) (by
  decide +kernel)

-- ZMod.not_isUnit_of_mem_primeFactors, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.not_isUnit_of_mem_primeFactors.h2 : Not
      (∀ {n p : Nat},
        Not
          (@IsUnit (ZMod n)
            (@Semiring.toMonoid (ZMod n)
              (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              p))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  simp)

-- ZMod.coe_unitOfIsCoprime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.coe_unitOfIsCoprime.h2 : ¬∀ {m : ℕ} (n : ℤ), IsCoprime n ↑m := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.ordProj_self_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordProj_self_pow.h2 : ¬∀ {p k : ℕ}, p ^ (p ^ k).factorization p = p ^ k := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.strong_induction_on, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.strong_induction_on.h2 : ¬∀ {motive : ℕ → Prop} (n : ℕ), motive n := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (1)) (by
  decide +kernel)

-- Nat.ordCompl_self_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordCompl_self_pow.h2 : ¬∀ {p k : ℕ}, p ^ k / p ^ (p ^ k).factorization p = 1 := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- PNat.Coprime.symm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.symm.h2 : ¬∀ {m n : ℕ+}, n.Coprime m := fun hc_h => absurd (@hc_h (2) (2)) (by
  nofun)

-- Nat.factorization_le_factorization_mul_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_le_factorization_mul_left.h2 : ¬∀ {a b : ℕ}, a.factorization ≤ (a * b).factorization := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

-- Bool.toNat_le_toNat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.toNat_le_toNat.h2 : ¬∀ {b₀ b₁ : Bool}, b₀.toNat ≤ b₁.toNat := fun hc_h => absurd (@hc_h (Bool.true) (Bool.false)) (by
  decide +kernel)

-- Nat.factorization_factorial_le_div_pred, hypothesis 1: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Nat.factorization_factorial_le_div_pred.h1.gneg : ∀ {p : ℕ}, ¬Nat.Prime p → ∀ (n : ℕ), n.factorial.factorization p ≤ n / (p - 1) := by
  (intros; simp_all; done)
theorem HypCheckProof.Nat.factorization_factorial_le_div_pred.h1 : ∀ {p : ℕ} (n : ℕ), n.factorial.factorization p ≤ n / (p - 1) := by
  intro hc_x0 hc_x2
  exact Classical.byCases (fun hc_h => @Nat.factorization_factorial_le_div_pred hc_x0 hc_h hc_x2) (fun hc_hn => @HypCheckProof.Nat.factorization_factorial_le_div_pred.h1.gneg hc_x0 hc_hn hc_x2)

-- Nat.le_two_mul_of_factorization_centralBinom_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_two_mul_of_factorization_centralBinom_pos.h2 : ¬∀ {p n : ℕ}, p ≤ 2 * n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.factorization_factorial_mul_succ, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_factorial_mul_succ.h2 : ¬∀ {n p : ℕ}, (p * (n + 1)).factorial.factorization p = (p * n).factorial.factorization p + (n + 1).factorization p + 1 := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Part.get_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.get_mem.h2 : ¬∀ {α : Type} {o : Part α}, o.Dom := fun hc_h => absurd (@hc_h (ℕ) (⊥)) (by
  nofun)

-- Set.Nonempty.empty_ssubset, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.empty_ssubset.h2 : ¬∀ {α : Type} {s : Set α}, ∅ ⊂ s := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Nat.factorization_factorial_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_factorial_mul.h2 : ¬∀ {n p : ℕ}, (p * n).factorial.factorization p = n.factorial.factorization p + n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Bool.and_elim_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.and_elim_right.h2 : ¬∀ {a : Bool} {b : Bool}, b = Bool.true := fun hc_h => absurd (@hc_h (Bool.false) (Bool.false)) (by
  decide +kernel)

-- Nat.sub_one_mul_factorization_factorial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.sub_one_mul_factorization_factorial.h2 : ¬∀ {n p : ℕ}, (p - 1) * n.factorial.factorization p = n - (p.digits n).sum := fun hc_h => absurd (@hc_h (4) (4)) (by
  decide +kernel)

-- Nat.Prime.emultiplicity_factorial_le_div_pred, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.emultiplicity_factorial_le_div_pred.h1 : ¬∀ {p : ℕ} (n : ℕ), emultiplicity p n.factorial ≤ ↑(n / (p - 1)) := fun hc_h => absurd (@hc_h (1) (0)) (by
  norm_num)

-- Nat.descFactorial_eq_div, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.descFactorial_eq_div.h2 : ¬∀ {n k : ℕ}, n.descFactorial k = n.factorial / (n - k).factorial := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.Prime.multiplicity_factorial_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.multiplicity_factorial_pow.h2 : ¬∀ {n p : ℕ}, multiplicity p (p ^ n).factorial = ∑ i ∈ Finset.range n, p ^ i := fun hc_h => absurd (@hc_h (1) (1)) (by
  simp)

-- Set.eq_empty_of_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_empty_of_isEmpty.h2 : ¬∀ {α : Type} (s : Set α), s = ∅ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Int.fib_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.fib_dvd.h2 : ¬∀ (m n : ℤ), Int.fib m ∣ Int.fib n := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.Prime.emultiplicity_factorial_mul_succ, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.emultiplicity_factorial_mul_succ.h2 : ¬∀ {n p : ℕ}, emultiplicity p (p * (n + 1)).factorial = emultiplicity p (p * n).factorial + emultiplicity p (n + 1) + 1 := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Nat.Prime.emultiplicity_factorial_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.emultiplicity_factorial_mul.h2 : ¬∀ {n p : ℕ}, emultiplicity p (p * n).factorial = emultiplicity p n.factorial + ↑n := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- Fintype.card_of_isEmpty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_of_isEmpty.h2 : ¬∀ {α : Type} [inst : Fintype α], Fintype.card α = 0 := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype)) (by
  decide +kernel)

-- ENat.sSup_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.sSup_add.h2 : ¬∀ {s : Set ℕ∞} {a : ℕ∞}, SupSet.sSup s + a = ⨆ b ∈ s, b + a := fun hc_h => absurd (@hc_h (∅) (1)) (by
  simp)

-- Nat.sqrt_le_sqrt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.sqrt_le_sqrt.h2 : ¬∀ {m n : ℕ}, m.sqrt ≤ n.sqrt := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- List.Duplicate.elim_nil, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Duplicate.elim_nil.h2 : ¬∀ {α : Type} {x : α}, False := fun hc_h => absurd (@hc_h (ℕ) (0)) (by
  decide +kernel)

-- ENat.toNat_eq_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.toNat_eq_iff.h2 : ¬∀ {m : ℕ∞} {n : ℕ}, m.toNat = n ↔ m = ↑n := fun hc_h => absurd (@hc_h (⊤) (0)) (by
  decide +kernel)

-- Nat.sqrt_add_eq', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.sqrt_add_eq'.h2 : ¬∀ {a : ℕ} (n : ℕ), (n ^ 2 + a).sqrt = n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- ENat.toNat_eq_iff_eq_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.toNat_eq_iff_eq_coe.h2 : ¬∀ (n : ℕ∞) (m : ℕ), n.toNat = m ↔ n = ↑m := fun hc_h => absurd (@hc_h (⊤) (0)) (by
  decide +kernel)

-- ENat.le_lift_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.le_lift_iff.h2 : ¬∀ {x : ℕ} {n : ℕ∞}, n < ⊤ := fun hc_h => absurd (@hc_h (0) (⊤)) (by
  decide +kernel)

-- Int.card_fintype_Ico_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.card_fintype_Ico_of_le.h2 : ¬∀ (a b : ℤ), ↑(Fintype.card ↑(Set.Ico a b)) = b - a := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Int.card_Ico_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.card_Ico_of_le.h2 : ¬∀ (a b : ℤ), ↑(Finset.Ico a b).card = b - a := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Int.card_fintype_Ioc_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.card_fintype_Ioc_of_le.h2 : ¬∀ (a b : ℤ), ↑(Fintype.card ↑(Set.Ioc a b)) = b - a := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Int.image_Ico_emod, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Int.image_Ico_emod.h2.gneg : ∀ (n a : ℤ), ¬0 ≤ a → Finset.image (fun (x : ℤ) => x % a) (Finset.Ico n (n + a)) = Finset.Ico 0 a := by
  (intros; grind)
theorem HypCheckProof.Int.image_Ico_emod.h2 : ∀ (n a : ℤ), Finset.image (fun (x : ℤ) => x % a) (Finset.Ico n (n + a)) = Finset.Ico 0 a := by
  intro hc_x0 hc_x1
  exact Classical.byCases (fun hc_h => @Int.image_Ico_emod hc_x0 hc_x1 hc_h) (fun hc_hn => @HypCheckProof.Int.image_Ico_emod.h2.gneg hc_x0 hc_x1 hc_hn)

-- Nat.factorial_inj', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorial_inj'.h2 : ¬∀ {m n : ℕ}, n.factorial = m.factorial ↔ n = m := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Sym2.fromRel_irrefl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.fromRel_irrefl.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.factorial_mul_ascFactorial', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorial_mul_ascFactorial'.h2 : ¬∀ (n k : ℕ), (n - 1).factorial * n.ascFactorial k = (n + k - 1).factorial := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- ENat.lift_lt_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.lift_lt_iff.h1 : ¬∀ {x : ℕ∞} {n : ℕ}, x < ⊤ := fun hc_h => absurd (@hc_h (⊤) (0)) (by
  decide +kernel)

-- ENat.eq_of_forall_natCast_le_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.eq_of_forall_natCast_le_iff.h2 : ¬∀ {m n : ℕ∞}, m = n := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Sym2.diagSet_subset_fromRel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.diagSet_subset_fromRel.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Sym2.fromRel_bot_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.fromRel_bot_iff.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.symm (0 : ℕ) (1 : ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENat.self_le_mul_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.self_le_mul_right.h2 : ¬∀ {c : ℕ∞} (a : ℕ∞), a ≤ a * c := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- List.Nodup.cyclicPermutations, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.cyclicPermutations.h2 : ¬∀ {α : Type} {l : List α}, l.cyclicPermutations.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0])) (by
  decide +kernel)

-- List.length_cyclicPermutations_of_ne_nil, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_cyclicPermutations_of_ne_nil.h2 : ¬∀ {α : Type} (l : List α), l.cyclicPermutations.length = l.length := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- Nat.exists_mul_mod_eq_gcd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_mul_mod_eq_gcd.h2 : ¬∀ {k n : ℕ}, ∃ m < k, n * m % k = n.gcd k := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Finset.Nonempty.sym2, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.Nonempty.sym2.h2.{u_1} : ¬∀ {α : Type u_1} {s : Finset α}, s.sym2.Nonempty := by
  (simp_all; done)

-- PosNum.cmp_to_nat_lemma, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PosNum.cmp_to_nat_lemma.h2 : Not
      (∀ {m n : PosNum},
        @LT.lt Nat instLTNat (@castPosNum Nat Nat.instOne instAddNat m.bit1)
          (@castPosNum Nat Nat.instOne instAddNat n.bit0)) := fun hc_h => absurd (@hc_h (PosNum.one) (PosNum.one)) (by
  decide +kernel)

-- Fin2.IsLT.h, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin2.IsLT.h.h2 : ¬∀ {m n : ℕ}, m < n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Finset.nonempty_of_ne_empty, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.nonempty_of_ne_empty.h2.{u_1} : ¬∀ {α : Type u_1} {s : Finset α}, s.Nonempty := by
  (simp_all; done)

-- Dvd.dvd.modEq_zero_nat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dvd.dvd.modEq_zero_nat.h2 : ¬∀ {n a : ℕ}, a ≡ 0 [MOD n] := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Bool.decide_true, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.decide_true.h2 : ¬∀ {p : Prop} [inst : Decidable p], Decidable.decide p = Bool.true := fun hc_h => absurd (@hc_h (False) (instDecidableFalse)) (by
  decide +kernel)

-- Bool.or_inr, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.or_inr.h2 : ¬∀ {a b : Bool}, (a || b) = Bool.true := fun hc_h => absurd (@hc_h (Bool.false) (Bool.false)) (by
  decide +kernel)

-- Set.Nonempty.to_subtype, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.to_subtype.h2 : ¬∀ {α : Type} {s : Set α}, Nonempty ↑s := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Nat.mul_le_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mul_le_pow.h1 : ¬∀ {a : ℕ} (b : ℕ), a * b ≤ a ^ b := fun hc_h => absurd (@hc_h (1) (2)) (by
  decide +kernel)

-- Fin.mk_eq_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.mk_eq_one.h2 : ¬∀ {n a : ℕ}, a < n + 2 := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- Set.Nonempty.some_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.some_mem.h2 : ¬∀ {α : Type} {s : Set α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Fin.cast_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.cast_injective.h2 : ¬∀ {k l : ℕ}, k = l := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Set.inclusion_eq_id, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Set.inclusion_eq_id.h2.der.{u_1} : ∀ {α : Type u_1} {s : Set α}, @LE.le (Set α) (@Set.instLE α) s s := by
  (intros; trivial)
theorem HypCheckProof.Set.inclusion_eq_id.h2.{u_1} : ∀ {α : Type u_1} {s : Set α},
      @Eq (@Set.Elem α s → @Set.Elem α s) (@Set.inclusion α s s (@HypCheckProof.Set.inclusion_eq_id.h2.der α s))
        (@id (@Set.Elem α s)) := by
  intro hc_x0 hc_x1
  exact @Set.inclusion_eq_id hc_x0 hc_x1 (@HypCheckProof.Set.inclusion_eq_id.h2.der hc_x0 hc_x1)

-- Dvd.dvd.zero_modEq_nat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dvd.dvd.zero_modEq_nat.h2 : ¬∀ {n a : ℕ}, 0 ≡ a [MOD n] := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Set.subsingleton_coe_of_subsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subsingleton_coe_of_subsingleton.h1 : ¬∀ {α : Type} {s : Set α}, Subsingleton ↑s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n % 2 = 0})) (by
  exact fun hc_c =>
    absurd
      (hc_c.allEq
        ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }) :
          { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} })
        ((⟨2, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }) :
          { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fin.val_sub_one_of_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_sub_one_of_ne_zero.h2 : Not
      (∀ {n : Nat} {i : Fin n},
        @Eq Nat
          (@Fin.val n
            (@HSub.hSub (Fin n) (Fin n) (Fin n) (@instHSub (Fin n) (@Fin.instSub n)) i
              (@OfNat.ofNat (Fin n) (nat_lit 1) (@Fin.instOfNat n (@Fin.neZero n i) (nat_lit 1)))))
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@Fin.val n i)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Nat.totient_prime_pow_succ, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_prime_pow_succ.h1 : ¬∀ {p : ℕ} (n : ℕ), (p ^ (n + 1)).totient = p ^ n * (p - 1) := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.totient_mul_of_prime_of_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_mul_of_prime_of_dvd.h2 : ¬∀ {p n : ℕ}, (p * n).totient = p * n.totient := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- Nat.totient_div_of_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_div_of_dvd.h2 : ¬∀ {n d : ℕ}, (n / d).totient = {k ∈ Finset.range n | n.gcd k = d}.card := fun hc_h => absurd (@hc_h (3) (2)) (by
  decide +kernel)

-- Nat.totient_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_mul.h2 : ¬∀ {m n : ℕ}, (m * n).totient = m.totient * n.totient := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- Nat.prime_pow_pow_totient_ediv_prod, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prime_pow_pow_totient_ediv_prod.h2 : ¬∀ {p : ℕ} (k : ℕ),
        (p ^ k) ^ (p ^ k).totient / ∏ q ∈ (p ^ k).primeFactors, q ^ ((p ^ k).totient / (q - 1)) =
          p ^ (p ^ (k - 1) * ((p - 1) * k - 1)) := fun hc_h => absurd (@hc_h (4) (1)) (by
  decide +kernel)

-- Fin.pos_of_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.pos_of_ne_zero.h2 : ¬∀ {n : ℕ} {a : Fin (n + 1)}, 0 < a := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.one_eq_mk, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.one_eq_mk.h2 : ¬∀ {n a : ℕ}, a < n + 2 := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- Set.countable_iff_exists_surjective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.countable_iff_exists_surjective.h2 : ¬∀ {α : Type} {s : Set α}, s.Countable ↔ ∃ (f : ℕ → ↑s), Function.Surjective f := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Fin.natCast_eq_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.natCast_eq_zero.h2 : ¬∀ {a : ℕ} {n : ℕ}, NeZero n := fun hc_h => absurd (@hc_h (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- FiniteInter.univ_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FiniteInter.univ_mem.h2 : ¬∀ {α : Type} {S : Set (Set α)}, Set.univ ∈ S := fun hc_h => absurd (@hc_h (ℕ) (∅)) (by
  decide +kernel)

-- Fin.val_natCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_natCast.h2 : ¬∀ (a n : ℕ), NeZero n := fun hc_h => absurd (@hc_h (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.Finite.exists_encard_eq_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.exists_encard_eq_coe.h2 : ¬∀ {α : Type} {s : Set α}, ∃ (n : ℕ), s.encard = ↑n := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True})) (by
  simp)

-- Nat.Coprime.divisors_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.divisors_mul.h2 : ¬∀ {m n : ℕ}, m.Coprime n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.Coprime.mul_injOn_divisors, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.mul_injOn_divisors.h2 : ¬∀ {m n : ℕ}, Set.InjOn (fun (p : ℕ × ℕ) => p.1 * p.2) ↑(m.divisors ×ˢ n.divisors) := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- Fin.lt_castPred_succ, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.lt_castPred_succ.h2 : ¬∀ {n : ℕ} {a : Fin (n + 1)}, a.succ ≠ Fin.last (n + 1) := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Rat.divInt_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.divInt_ne_zero.h2 : ¬∀ {a b : ℤ}, Rat.divInt a b ≠ 0 ↔ a ≠ 0 := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Fin.rightInverse_cast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.rightInverse_cast.h2 : ¬∀ {n m : ℕ}, n = m := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Fin.castPred_castSucc, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.castPred_castSucc.h2.der : ∀ {n : ℕ} {i : Fin n}, ¬i.castSucc = Fin.last n := by
  (intros; simp; done)
theorem HypCheckProof.Fin.castPred_castSucc.h2 : ∀ {n : ℕ} {i : Fin n}, i.castSucc.castPred HypCheckProof.Fin.castPred_castSucc.h2.der = i := by
  intro hc_x0 hc_x1
  exact @Fin.castPred_castSucc hc_x0 hc_x1 (@HypCheckProof.Fin.castPred_castSucc.h2.der hc_x0 hc_x1)

-- finCongr_eq_equivCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finCongr_eq_equivCast.h2 : ¬∀ {n m : ℕ}, n = m := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Int.ofNat_lt_ofNat_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ofNat_lt_ofNat_of_lt.h2 : Not (∀ {n m : Nat}, @LT.lt Int Int.instLTInt (@Nat.cast Int instNatCastInt n) (@Nat.cast Int instNatCastInt m)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- List.get_length_sub_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.get_length_sub_one.h2 : ¬∀ {α : Type} {l : List α}, l.length - 1 < l.length := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- Fintype.one_lt_card, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.one_lt_card.h2 : ¬∀ {α : Type} [inst : Fintype α], 1 < Fintype.card α := fun hc_h => absurd (@hc_h (Unit) (PUnit.fintype)) (by
  decide +kernel)

-- Fin.succAbove_castPred_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_castPred_self.h2 : ¬∀ {n : ℕ} (p : Fin (n + 1)), p ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- ExistsUnique.setSubsingleton, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ExistsUnique.setSubsingleton.h2 : ¬∀ {α : Type} {p : α → Prop}, {x : α | p x}.Subsingleton := fun hc_h => absurd (@hc_h (Bool) (fun _ => True : Bool → Prop)) (by
  decide +kernel)

-- Set.Nontrivial.choose_snd_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.choose_snd_mem.h2 : ¬∀ {α : Type} {s : Set α}, s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Set.encard_eq_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_eq_top.h2 : ¬∀ {α : Type} {s : Set α}, s.encard = ⊤ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Fin.succAbove_ne_last_last, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_ne_last_last.h2 : ¬∀ {n : ℕ} {a : Fin (n + 2)}, a.succAbove (Fin.last n) = Fin.last (n + 1) := fun hc_h => absurd (@hc_h (0) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Rat.divInt_eq_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.divInt_eq_zero.h2 : ¬∀ {a b : ℤ}, Rat.divInt a b = 0 ↔ a = 0 := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Set.ncard_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_pos.h2 : ¬∀ {α : Type} {s : Set α}, 0 < s.ncard ↔ s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True})) (by
  simp)

-- Rat.toNNRat_lt_iff_lt_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.toNNRat_lt_iff_lt_coe.h2 : ¬∀ {q : ℚ} {p : ℚ≥0}, q.toNNRat < p ↔ q < ↑p := fun hc_h => absurd (@hc_h (-1) (0)) (by
  decide +kernel)

-- Nat.coprime_of_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_of_dvd.h2 : ¬∀ {m n : ℕ}, m.Coprime n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Set.nonempty_of_encard_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nonempty_of_encard_ne_zero.h2 : ¬∀ {α : Type} {s : Set α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Nat.WithBot.add_one_le_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.WithBot.add_one_le_of_lt.h2 : ¬∀ {n m : WithBot ℕ}, n + 1 ≤ m := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Fin.predAbove_pred_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_pred_self.h2 : ¬∀ {n : ℕ} (p : Fin (n + 1)), p ≠ 0 := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- finCongr_symm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finCongr_symm.h2 : ¬∀ {n m : ℕ}, m = n := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Int.mod_coprime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.mod_coprime.h2 : ¬∀ {a b : ℕ}, ∃ (y : ℤ), ↑a * y ≡ 1 [ZMOD ↑b] := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Finset.exists_card_eq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.exists_card_eq.h1 : ¬∀ {α : Type} (n : ℕ), ∃ (s : Finset α), s.card = n := fun hc_h => absurd (@hc_h (Bool) (3)) (by
  decide +kernel)

-- Rat.toNNRat_le_toNNRat_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.toNNRat_le_toNNRat_iff.h2 : ¬∀ {p q : ℚ}, q.toNNRat ≤ p.toNNRat ↔ q ≤ p := fun hc_h => absurd (@hc_h (-1) (0)) (by
  decide +kernel)

-- Fin.cast_eq_cast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.cast_eq_cast.h2 : ¬∀ {n m : ℕ}, n = m := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- NNRat.coe_sub, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNRat.coe_sub.h2 : Not
      (∀ {p q : NNRat},
        @Eq Rat (@NNRat.cast Rat Rat.instNNRatCast (@HSub.hSub NNRat NNRat NNRat (@instHSub NNRat instSubNNRat) p q))
          (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) (@NNRat.cast Rat Rat.instNNRatCast p)
            (@NNRat.cast Rat Rat.instNNRatCast q))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat NNRat (nat_lit 0)
      (@Zero.toOfNat0 NNRat
        (@MulZeroClass.toZero NNRat
          (@instMulZeroClassOfSemiring NNRat (@CommSemiring.toSemiring NNRat instCommSemiringNNRat))))) (@OfNat.ofNat NNRat (nat_lit 1)
      (@One.toOfNat1 NNRat
        (@AddMonoidWithOne.toOne NNRat
          (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
            (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
              (@Semiring.toNonAssocSemiring NNRat (@CommSemiring.toSemiring NNRat instCommSemiringNNRat)))))))) (by
  decide +kernel)

-- Rat.toNNRat_div, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.toNNRat_div.h2 : ¬∀ {p q : ℚ}, (p / q).toNNRat = p.toNNRat / q.toNNRat := fun hc_h => absurd (@hc_h (-1) (-1)) (by
  decide +kernel)

-- Nat.coprime_factorial_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_factorial_iff.h2 : ¬∀ {m n : ℕ}, m.Coprime n.factorial ↔ n < m.minFac := fun hc_h => absurd (@hc_h (1) (1)) (by
  decide +kernel)

-- Set.Finite.cast_ncard_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.cast_ncard_eq.h2 : ¬∀ {α : Type} {s : Set α}, ↑s.ncard = s.encard := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True})) (by
  simp)

-- EReal.coe_lt_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.coe_lt_coe.h2 : Not (∀ {x y : Real}, @LT.lt EReal (@Preorder.toLT EReal (@PartialOrder.toPreorder EReal instPartialOrderEReal)) ↑x ↑y) := fun hc_h => absurd (@hc_h ({
      cauchy :=
        @OfNat.ofNat
          (@CauSeq.Completion.Cauchy Rat Rat.instField Rat.linearOrder Rat.instIsStrictOrderedRing Rat
            (@DivisionRing.toRing Rat Rat.instDivisionRing) (@abs Rat Rat.instLattice Rat.addGroup)
            (@IsAbsoluteValue.abs_isAbsoluteValue Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder
              Rat.instIsStrictOrderedRing))
          (nat_lit 0)
          (@Zero.toOfNat0
            (@CauSeq.Completion.Cauchy Rat Rat.instField Rat.linearOrder Rat.instIsStrictOrderedRing Rat
              (@DivisionRing.toRing Rat Rat.instDivisionRing) (@abs Rat Rat.instLattice Rat.addGroup)
              (@IsAbsoluteValue.abs_isAbsoluteValue Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder
                Rat.instIsStrictOrderedRing))
            (@CauSeq.Completion.instZeroCauchy Rat Rat.instField Rat.linearOrder Rat.instIsStrictOrderedRing Rat
              (@DivisionRing.toRing Rat Rat.instDivisionRing) (@abs Rat Rat.instLattice Rat.addGroup)
              (@IsAbsoluteValue.abs_isAbsoluteValue Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder
                Rat.instIsStrictOrderedRing))) :
      Real }) ({
      cauchy :=
        @OfNat.ofNat
          (@CauSeq.Completion.Cauchy Rat Rat.instField Rat.linearOrder Rat.instIsStrictOrderedRing Rat
            (@DivisionRing.toRing Rat Rat.instDivisionRing) (@abs Rat Rat.instLattice Rat.addGroup)
            (@IsAbsoluteValue.abs_isAbsoluteValue Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder
              Rat.instIsStrictOrderedRing))
          (nat_lit 0)
          (@Zero.toOfNat0
            (@CauSeq.Completion.Cauchy Rat Rat.instField Rat.linearOrder Rat.instIsStrictOrderedRing Rat
              (@DivisionRing.toRing Rat Rat.instDivisionRing) (@abs Rat Rat.instLattice Rat.addGroup)
              (@IsAbsoluteValue.abs_isAbsoluteValue Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder
                Rat.instIsStrictOrderedRing))
            (@CauSeq.Completion.instZeroCauchy Rat Rat.instField Rat.linearOrder Rat.instIsStrictOrderedRing Rat
              (@DivisionRing.toRing Rat Rat.instDivisionRing) (@abs Rat Rat.instLattice Rat.addGroup)
              (@IsAbsoluteValue.abs_isAbsoluteValue Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder
                Rat.instIsStrictOrderedRing))) :
      Real })) (by
  simp)

-- Nat.dvd_of_forall_prime_mul_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_of_forall_prime_mul_dvd.h2 : ¬∀ {a b : ℕ}, a ∣ b := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.dist_pos_of_ne, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dist_pos_of_ne.h2 : ¬∀ {i j : ℕ}, 0 < i.dist j := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.dist_eq_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dist_eq_zero.h2 : ¬∀ {n m : ℕ}, n.dist m = 0 := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.dist_eq_sub_of_le_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dist_eq_sub_of_le_right.h2 : ¬∀ {n m : ℕ}, n.dist m = n - m := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- EReal.exists_between_coe_real, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.exists_between_coe_real.h2 : ¬∀ {x z : EReal}, ∃ (y : ℝ), x < ↑y ∧ ↑y < z := fun hc_h => absurd (@hc_h (0) (⊥)) (by
  simp)

-- Nat.floorRoot_pow_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.floorRoot_pow_self.h1 : ¬∀ {n : ℕ} (a : ℕ), n.floorRoot (a ^ n) = a := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.dvd_ceilRoot_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_ceilRoot_pow.h2 : ¬∀ {a n : ℕ}, a ∣ n.ceilRoot a ^ n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.ceilRoot_pow_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ceilRoot_pow_self.h1 : ¬∀ {n : ℕ} (a : ℕ), n.ceilRoot (a ^ n) = a := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Set.Finite.encard_eq_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.encard_eq_coe.h2 : ¬∀ {α : Type} {s : Set α}, s.encard = ↑s.encard.toNat := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True})) (by
  simp)

-- Nat.nth_mem_of_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_mem_of_ne_zero.h2 : ¬∀ {p : ℕ → Prop} {n : ℕ}, p (Nat.nth p n) := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (0)) (by
  decide +kernel)

-- EReal.toENNReal_sub, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toENNReal_sub.h2 : ¬∀ {x y : EReal}, (x - y).toENNReal = x.toENNReal - y.toENNReal := fun hc_h => absurd (@hc_h (0) (⊥)) (by
  decide +kernel)

-- Nat.primeFactorsList_subset_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactorsList_subset_right.h2 : ¬∀ {n k : ℕ}, n.primeFactorsList ⊆ (n * k).primeFactorsList := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

-- Nat.dvd_of_mem_primeFactorsList, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_of_mem_primeFactorsList.h2 : ¬∀ {n p : ℕ}, p ∣ n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.isLeast_nth_of_infinite, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.isLeast_nth_of_infinite.h1 : ¬∀ {p : ℕ → Prop} (n : ℕ), IsLeast {i : ℕ | p i ∧ ∀ k < n, Nat.nth p k < i} (Nat.nth p n) := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (0)) (by
  decide +kernel)

-- Nat.mem_primeFactorsList, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mem_primeFactorsList.h2 : ¬∀ {n p : ℕ}, p ∈ n.primeFactorsList ↔ Nat.Prime p ∧ p ∣ n := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- Nat.perm_primeFactorsList_mul_of_coprime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.perm_primeFactorsList_mul_of_coprime.h2 : ¬∀ {a b : ℕ}, (a * b).primeFactorsList.Perm (a.primeFactorsList ++ b.primeFactorsList) := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- Nat.Coprime.primeFactors_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.primeFactors_mul.h2 : ¬∀ {a b : ℕ}, (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- Ordnode.length_toList, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.length_toList.h2 : ¬∀ {α : Type} {t : Ordnode α}, t.toList.length = t.size := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil)) (by
  decide +kernel)

-- Nat.log_two_bit, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_two_bit.h2 : ¬∀ {b : Bool} {n : ℕ}, Nat.log 2 (Nat.bit b n) = Nat.log 2 n + 1 := fun hc_h => absurd (@hc_h (Bool.false) (0)) (by
  decide +kernel)

-- Nat.mem_primeFactors_of_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mem_primeFactors_of_ne_zero.h2 : ¬∀ {n p : ℕ}, p ∈ n.primeFactors ↔ Nat.Prime p ∧ p ∣ n := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- Nat.dvd_of_mem_primeFactors, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_of_mem_primeFactors.h2 : ¬∀ {n p : ℕ}, p ∣ n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.pos_of_mem_primeFactors, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pos_of_mem_primeFactors.h2 : ¬∀ {n : ℕ} {p : ℕ}, 0 < p := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- ZMod.addOrderOf_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.addOrderOf_coe.h2 : Not
      (∀ (a : Nat) {n : Nat},
        @Eq Nat
          (@addOrderOf (ZMod n)
            (@AddMonoidWithOne.toAddMonoid (ZMod n)
              (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              a))
          (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) n (n.gcd a))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  simp)

-- Set.eq_empty_of_forall_notMem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_empty_of_forall_notMem.h2 : ¬∀ {α : Type} {s : Set α}, s = ∅ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- ZMod.val_ofNat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.val_ofNat.h2 : ¬∀ (n a : ℕ), a.AtLeastTwo := fun hc_h => absurd (@hc_h (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.odd_ncard_compl_iff', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.odd_ncard_compl_iff'.h1 : ¬∀ {α : Type} (s : Set α), Odd sᶜ.ncard ↔ Even s.ncard := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true})) (by
  simp)

-- ZMod.coe_unitOfCoprime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.coe_unitOfCoprime.h2 : ¬∀ {n : ℕ} (x : ℕ), x.Coprime n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Set.Finite.toFinset_singleton, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Set.Finite.toFinset_singleton.h2.der.{u} : ∀ {α : Type u} {a : α}, @Set.Finite α (@Singleton.singleton α (Set α) (@Set.instSingletonSet α) a) := by
  (intros; simp; done)
theorem HypCheckProof.Set.Finite.toFinset_singleton.h2.{u} : ∀ {α : Type u} {a : α},
      @Eq (Finset α)
        (@Set.Finite.toFinset α (@Singleton.singleton α (Set α) (@Set.instSingletonSet α) a)
          (@HypCheckProof.Set.Finite.toFinset_singleton.h2.der α a))
        (@Singleton.singleton α (Finset α) (@Finset.instSingleton α) a) := by
  intro hc_x0 hc_x1
  exact @Set.Finite.toFinset_singleton hc_x0 hc_x1 (@HypCheckProof.Set.Finite.toFinset_singleton.h2.der hc_x0 hc_x1)

-- ZMod.val_natCast_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.val_natCast_of_lt.h2 : Not
      (∀ {n a : Nat},
        @Eq Nat
          (@ZMod.val n
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              a))
          a) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Fin.predAbove_last_of_ne_last, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_last_of_ne_last.h2 : ¬∀ {n : ℕ} {i : Fin (n + 2)}, i ≠ Fin.last (n + 1) := fun hc_h => absurd (@hc_h (0) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- ZMod.ringEquivCongr_symm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.ringEquivCongr_symm.h2 : ¬∀ {a b : ℕ}, a = b := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- ZMod.val_cast_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.val_cast_of_lt.h2 : Not
      (∀ {n a : Nat},
        @Eq Nat
          (@ZMod.val n
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              a))
          a) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Rat.den_div_natCast_eq_one_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.den_div_natCast_eq_one_iff.h2 : Not
      (∀ (m n : Nat),
        Iff
          (@Eq Nat
            (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Nat.cast Rat Rat.instNatCast m)
                (@Nat.cast Rat Rat.instNatCast n)).den
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Dvd.dvd Nat Nat.instDvd n m)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Int.natAbs_natCast_sub_natCast_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_natCast_sub_natCast_of_le.h2 : Not
      (∀ {a b : Nat},
        @Eq Nat
          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt a)
              (@Nat.cast Int instNatCastInt b)).natAbs
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) b a)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- ZMod.mul_val_inv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.mul_val_inv.h2 : Not
      (∀ {m n : Nat},
        @Eq (ZMod n)
          (@HMul.hMul (ZMod n) (ZMod n) (ZMod n)
            (@instHMul (ZMod n)
              (@Distrib.toMul (ZMod n)
                (@instDistribOfSemiring (ZMod n)
                  (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))))
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              m)
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              (@ZMod.val n
                (@Inv.inv (ZMod n) (ZMod.instInv n)
                  (@Nat.cast (ZMod n)
                    (@AddMonoidWithOne.toNatCast (ZMod n)
                      (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                        (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
                    m)))))
          (@OfNat.ofNat (ZMod n) (nat_lit 1)
            (@One.toOfNat1 (ZMod n)
              (@AddMonoidWithOne.toOne (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- PNat.one_lt_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.one_lt_of_lt.h2 : ¬∀ {a : ℕ+} {b : ℕ+}, 1 < b := fun hc_h => absurd (@hc_h (1) (1)) (by
  decide +kernel)

-- PNat.pos_of_div_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.pos_of_div_pos.h2 : ¬∀ {n : ℕ+} {a : ℕ}, 0 < a := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- ZMod.castHom_surjective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.castHom_surjective.h2 : ¬∀ {n m : ℕ}, m ∣ n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- PNat.le_of_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.le_of_dvd.h2 : ¬∀ {m n : ℕ+}, m ≤ n := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- List.Nodup.of_offDiag, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.of_offDiag.h2 : ¬∀ {α : Type} {l : List α}, l.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0])) (by
  decide +kernel)

-- Finset.Nat.antidiagonal_filter_snd_le_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nat.antidiagonal_filter_snd_le_of_le.h2 : ¬∀ {n k : ℕ},
        {a ∈ Finset.HasAntidiagonal.antidiagonal n | a.2 ≤ k} =
          Finset.map
            ({ toFun := fun (x : ℕ) => x + (n - k), inj' := add_left_injective (n - k) : ℕ ↪ ℕ }.prodMap
              (Function.Embedding.refl ℕ))
            (Finset.HasAntidiagonal.antidiagonal k) := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- ZMod.coe_mul_inv_eq_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.coe_mul_inv_eq_one.h2 : Not
      (∀ {n : Nat} (x : Nat),
        @Eq (ZMod n)
          (@HMul.hMul (ZMod n) (ZMod n) (ZMod n)
            (@instHMul (ZMod n)
              (@Distrib.toMul (ZMod n)
                (@instDistribOfSemiring (ZMod n)
                  (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))))
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              x)
            (@Inv.inv (ZMod n) (ZMod.instInv n)
              (@Nat.cast (ZMod n)
                (@AddMonoidWithOne.toNatCast (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
                x)))
          (@OfNat.ofNat (ZMod n) (nat_lit 1)
            (@One.toOfNat1 (ZMod n)
              (@AddMonoidWithOne.toOne (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Nat.choose_symm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_symm.h2 : ¬∀ {n k : ℕ}, n.choose (n - k) = n.choose k := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.bit_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bit_ne_zero.h2 : ¬∀ (b : Bool) {n : ℕ}, Nat.bit b n ≠ 0 := fun hc_h => absurd (@hc_h (Bool.false) (0)) (by
  decide +kernel)

-- Nat.choose_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_pos.h2 : ¬∀ {n k : ℕ}, 0 < n.choose k := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.choose_le_succ_of_lt_half_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_le_succ_of_lt_half_left.h2 : ¬∀ {r n : ℕ}, n.choose r ≤ n.choose (r + 1) := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.choose_succ_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_succ_right.h2 : ¬∀ (n k : ℕ), n.choose (k + 1) = (n - 1).choose k + (n - 1).choose (k + 1) := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Int.sign_add_eq_of_sign_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.sign_add_eq_of_sign_eq.h2 : ¬∀ {m n : ℤ}, (m + n).sign = n.sign := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.factorial_mul_factorial_dvd_factorial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorial_mul_factorial_dvd_factorial.h2 : ¬∀ {n k : ℕ}, k.factorial * (n - k).factorial ∣ n.factorial := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- Nat.choose_mul_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_mul_add.h2 : ¬∀ {m n : ℕ}, (m * n + n).choose n = (m + 1) * (m * n + n - 1).choose (n - 1) := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.choose_succ_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_succ_left.h2 : ¬∀ (n k : ℕ), (n + 1).choose k = n.choose (k - 1) + n.choose k := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Int.ofNat_le_ofNat_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ofNat_le_ofNat_of_le.h2 : Not (∀ {m n : Nat}, @LE.le Int Int.instLEInt (@Nat.cast Int instNatCastInt m) (@Nat.cast Int instNatCastInt n)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Nat.clog_lt_clog_succ_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_lt_clog_succ_iff.h2 : ¬∀ {b n : ℕ}, Nat.clog b n < Nat.clog b (n + 1) ↔ b ^ Nat.clog b n = n := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Fin.coe_castLEEmb, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.coe_castLEEmb.h2 : ¬∀ {m n : ℕ}, m ≤ n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.ofDigits_lt_base_pow_length', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofDigits_lt_base_pow_length'.h2 : ¬∀ {b : ℕ} {l : List ℕ}, Nat.ofDigits (b + 2) l < (b + 2) ^ l.length := fun hc_h => absurd (@hc_h (0) ([2])) (by
  decide +kernel)

-- Set.Nontrivial.not_subsingleton, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.not_subsingleton.h2 : ¬∀ {α : Type} {s : Set α}, ¬s.Subsingleton := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Nat.mul_divisors_filter_prime_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mul_divisors_filter_prime_pow.h2 : ¬∀ {a b : ℕ}, {d ∈ (a * b).divisors | IsPrimePow d} = {d ∈ a.divisors ∪ b.divisors | IsPrimePow d} := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- Squarefree.natFactorization_le_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Squarefree.natFactorization_le_one.h2 : ¬∀ {n : ℕ} (p : ℕ), n.factorization p ≤ 1 := fun hc_h => absurd (@hc_h (4) (2)) (by
  decide +kernel)

-- List.fixedLengthDigits_succ_eq_disjiUnion, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.fixedLengthDigits_succ_eq_disjiUnion.h1 : ¬∀ {b : ℕ} (l : ℕ), 1 < b := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.coprime_sub_mul_floor_rat_div_of_coprime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_sub_mul_floor_rat_div_of_coprime.h2 : Not
      (∀ {n d : Nat},
        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt n)
                (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@Nat.cast Int instNatCastInt d)
                  (@Int.floor Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing
                    (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Nat.cast Rat Rat.instNatCast n)
                      (@Nat.cast Rat Rat.instNatCast d))))).natAbs.Coprime
          d) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- List.Lex.trichotomous, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.trichotomous.h2 : ¬∀ {α : Type} (r : α → α → Prop), Std.Trichotomous (List.Lex r) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd
      (hc_c.trichotomous ([0] : List ℕ) ([1] : List ℕ)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.getLast_digit_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.getLast_digit_ne_zero.h2 : ¬∀ (b : ℕ) {m : ℕ}, m ≠ 0 := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.minSqFac_prime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.minSqFac_prime.h2 : ¬∀ {n : ℕ} {d : ℕ}, Nat.Prime d := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.squarefree_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.squarefree_mul.h2 : ¬∀ {m n : ℕ}, Squarefree (m * n) ↔ Squarefree m ∧ Squarefree n := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- Nat.coprime_of_squarefree_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_of_squarefree_mul.h2 : ¬∀ {m n : ℕ}, m.Coprime n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.find_spec, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_spec.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p], ∃ (n : ℕ), p n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse)) (by
  simp)

-- Finset.mem_range_sub_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_range_sub_ne_zero.h2 : ¬∀ {n x : ℕ}, n - x ≠ 0 := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Set.Subsingleton.coe_sort, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subsingleton.coe_sort.h2 : ¬∀ {α : Type} {s : Set α}, Subsingleton ↑s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n % 2 = 0})) (by
  exact fun hc_c =>
    absurd
      (hc_c.allEq
        ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }) :
          { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} })
        ((⟨2, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }) :
          { x : ℕ // x ∈ {n : ℕ | n % 2 = 0} }))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.find_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_pos.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p], ∃ (n : ℕ), p n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse)) (by
  simp)

-- PNat.Prime.not_dvd_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Prime.not_dvd_one.h1 : ¬∀ {p : ℕ+}, ¬p ∣ 1 := fun hc_h => absurd (@hc_h (1)) (by
  simp)

-- PNat.mk_coe, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.mk_coe.h1 : ¬∀ (n : ℕ), 0 < n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.zero_of_testBit_eq_false, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.zero_of_testBit_eq_false.h1 : ¬∀ {n : ℕ}, n = 0 := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- EReal.coe_ennreal_mul_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.coe_ennreal_mul_top.h1 : Not
      (∀ {x : ENNReal},
        @Eq EReal (@HMul.hMul EReal EReal EReal (@instHMul EReal EReal.instMul) (↑x) (@Top.top EReal instTopEReal))
          (@Top.top EReal instTopEReal)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero))) (by
  simp)

-- Nat.factorization_minFac_ne_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_minFac_ne_zero.h1 : ¬∀ {n : ℕ}, n.factorization n.minFac ≠ 0 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.xor_one_of_odd, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.xor_one_of_odd.h1 : ¬∀ {n : ℕ}, n ^^^ 1 = n - 1 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- EReal.mul_bot_of_neg, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.mul_bot_of_neg.h1 : ¬∀ {x : EReal}, x * ⊥ = ⊤ := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- EReal.top_mul_coe_ennreal, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.top_mul_coe_ennreal.h1 : Not
      (∀ {x : ENNReal},
        @Eq EReal (@HMul.hMul EReal EReal EReal (@instHMul EReal EReal.instMul) (@Top.top EReal instTopEReal) ↑x)
          (@Top.top EReal instTopEReal)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat ENNReal (nat_lit 0) (@Zero.toOfNat0 ENNReal ENNReal.instZero))) (by
  simp)

-- Nat.Prime.pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.pos.h1 : ¬∀ {p : ℕ}, 0 < p := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.primeFactorsList_prime, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactorsList_prime.h1 : ¬∀ {p : ℕ}, p.primeFactorsList = [p] := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- ENat.addLECancellable_of_lt_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.addLECancellable_of_lt_top.h1 : ¬∀ {a : ℕ∞}, AddLECancellable a := fun hc_h => absurd (@hc_h (⊤)) (by
  simp)

-- Nat.prod_primeFactorsList, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prod_primeFactorsList.h1 : ¬∀ {n : ℕ}, n.primeFactorsList.prod = n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Fin.castPred_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_zero.h1 : ¬∀ {n : ℕ}, NeZero n := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENat.coe_sInf, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.coe_sInf.h1 : Not
      (∀ {s : Set Nat},
        @Eq ENat (@Nat.cast ENat ENat.instNatCast (@InfSet.sInf Nat Nat.instInfSet s))
          (⨅ (a : Nat),
            ⨅ (_ : @Membership.mem Nat (Set Nat) (@Set.instMembership Nat) s a), @Nat.cast ENat ENat.instNatCast a)) := fun hc_h => absurd (@hc_h (@Set.ofPred Nat fun (x : Nat) => False)) (by
  simp)

-- Ordnode.not_le_delta, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.not_le_delta.h1 : ¬∀ {s : ℕ}, ¬s ≤ Ordnode.delta * 0 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.Prime.prime, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.prime.h1 : ¬∀ {p : ℕ}, Prime p := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.Prime.two_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.two_le.h1 : ¬∀ {p : ℕ}, 2 ≤ p := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt.h1 : ¬∀ {n : ℕ}, 4 ∣ n ∨ ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ Odd p := fun hc_h => absurd (@hc_h (1)) (by
  (simp <;> decide))

-- PosNum.pred_to_nat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PosNum.pred_to_nat.h1 : Not
      (∀ {n : PosNum},
        @Eq Nat (@castPosNum Nat Nat.instOne instAddNat n.pred) (@castPosNum Nat Nat.instOne instAddNat n).pred) := fun hc_h => absurd (@hc_h (PosNum.one)) (by
  decide +kernel)

-- Fin.mk_zero', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.mk_zero'.h1 : ¬∀ (n : ℕ), NeZero n := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fin.instNeZeroHAddNatOfNat_mathlib_1, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.instNeZeroHAddNatOfNat_mathlib_1.h1 : Not
      (∀ (n : Nat),
        @NeZero
          (Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@MulZeroClass.toZero
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@NonUnitalNonAssocSemiring.toMulZeroClass
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Fin.instNonUnitalCommRing
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))))
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
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ULift.instIsEmpty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ULift.instIsEmpty.h1 : ¬∀ {α : Type}, IsEmpty (ULift.{0, 0} α) := fun hc_h => absurd (@hc_h (ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.false ({ down := 0 : ULift.{0, 0} ℕ } : ULift.{0, 0} ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.minFac_prime, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.minFac_prime.h1 : ¬∀ {n : ℕ}, Nat.Prime n.minFac := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- Nat.Prime.not_dvd_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.not_dvd_one.h1 : ¬∀ {p : ℕ}, ¬p ∣ 1 := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- Nat.not_prime_iff_minFac_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_prime_iff_minFac_lt.h1 : ¬∀ {n : ℕ}, ¬Nat.Prime n ↔ n.minFac < n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- ENat.coe_lift, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.coe_lift.h1 : ¬∀ (x : ℕ∞), x < ⊤ := fun hc_h => absurd (@hc_h (⊤)) (by
  decide +kernel)

-- finCongr_refl, hypothesis 1: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.finCongr_refl.h1.der : ∀ {n : ℕ}, n = n := by
  (intros; trivial)
theorem HypCheckProof.finCongr_refl.h1 : ∀ {n : ℕ}, finCongr HypCheckProof.finCongr_refl.h1.der = Equiv.refl (Fin n) := by
  intro hc_x0
  exact @finCongr_refl hc_x0 (@HypCheckProof.finCongr_refl.h1.der hc_x0)

-- ZMod.val_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.val_one.h1 : Not
      (∀ (n : Nat),
        @Eq Nat
          (@ZMod.val n
            (@OfNat.ofNat (ZMod n) (nat_lit 1)
              (@One.toOfNat1 (ZMod n)
                (@AddMonoidWithOne.toOne (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- ENat.lift_eq_toNat_of_lt_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.lift_eq_toNat_of_lt_top.h1 : ¬∀ {x : ℕ∞}, x < ⊤ := fun hc_h => absurd (@hc_h (⊤)) (by
  decide +kernel)

-- Nat.add_one_sqrt_le_of_ne_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_one_sqrt_le_of_ne_zero.h1 : ¬∀ {n : ℕ}, (n + 1).sqrt ≤ n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Fin.natCast_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.natCast_zero.h1 : ¬∀ {n : ℕ}, NeZero n := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Ico.pred_singleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.pred_singleton.h1 : ¬∀ {m : ℕ}, List.Ico (m - 1) m = [m - 1] := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Fin.pred_last, hypothesis 1: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.pred_last.h1.der : ∀ {n : ℕ}, ¬Fin.last (n + 1) = 0 := by
  (intros; simp; done)
theorem HypCheckProof.Fin.pred_last.h1 : ∀ {n : ℕ}, (Fin.last (n + 1)).pred HypCheckProof.Fin.pred_last.h1.der = Fin.last n := by
  intro hc_x0
  exact @Fin.pred_last hc_x0 (@HypCheckProof.Fin.pred_last.h1.der hc_x0)

-- Nat.card_perm, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.card_perm.h1 : ¬∀ {α : Type}, Nat.card (Equiv.Perm α) = (Nat.card α).factorial := fun hc_h => absurd (@hc_h (ℕ)) (by
  simp)

-- Odd.natCast_zmod_two, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Odd.natCast_zmod_two.h1 : Not
      (∀ {n : Nat},
        @Eq (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Nat.cast (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@AddMonoidWithOne.toNatCast (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Ring.toAddGroupWithOne (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@CommRing.toRing (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (ZMod.commRing (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            n)
          (@OfNat.ofNat (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
            (@One.toOfNat1 (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddMonoidWithOne.toOne (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Ring.toAddGroupWithOne (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@CommRing.toRing (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (ZMod.commRing (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- NNRat.num_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNRat.num_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.totient_two_mul_of_even, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_two_mul_of_even.h1 : ¬∀ {n : ℕ}, (2 * n).totient = 2 * n.totient := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- Even.intCast_zmod_two, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Even.intCast_zmod_two.h1 : Not
      (∀ {n : Int},
        @Eq (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Int.cast (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@AddGroupWithOne.toIntCast (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Ring.toAddGroupWithOne (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@CommRing.toRing (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (ZMod.commRing (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            n)
          (@OfNat.ofNat (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
            (@Zero.toOfNat0 (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@MulZeroClass.toZero (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@instMulZeroClassOfSemiring (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@CommSemiring.toSemiring (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@CommRing.toCommSemiring (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (ZMod.commRing (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  decide +kernel)

-- ENat.natCast_toNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.natCast_toNat.h1 : ¬∀ {n : ℕ∞}, ↑n.toNat = n := fun hc_h => absurd (@hc_h (⊤)) (by
  decide +kernel)

-- Nat.totient_two_mul_of_odd, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_two_mul_of_odd.h1 : ¬∀ {n : ℕ}, (2 * n).totient = n.totient := fun hc_h => absurd (@hc_h (2)) (by
  decide +kernel)

-- ZMod.neg_one_ne_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.neg_one_ne_one.h1 : Not
      (∀ {n : Nat},
        @Ne (ZMod n)
          (@Neg.neg (ZMod n)
            (@NegZeroClass.toNeg (ZMod n)
              (@SubNegZeroMonoid.toNegZeroClass (ZMod n)
                (@SubtractionMonoid.toSubNegZeroMonoid (ZMod n)
                  (@SubtractionCommMonoid.toSubtractionMonoid (ZMod n)
                    (@AddCommGroup.toDivisionAddCommMonoid (ZMod n)
                      (@Ring.toAddCommGroup (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))))))
            (@OfNat.ofNat (ZMod n) (nat_lit 1)
              (@One.toOfNat1 (ZMod n)
                (@AddMonoidWithOne.toOne (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))))))
          (@OfNat.ofNat (ZMod n) (nat_lit 1)
            (@One.toOfNat1 (ZMod n)
              (@AddMonoidWithOne.toOne (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Nat.totient_eq_iff_prime, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_eq_iff_prime.h1 : ¬∀ {p : ℕ}, p.totient = p - 1 ↔ Nat.Prime p := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- NeZero.one_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NeZero.one_le.h1 : ¬∀ {n : ℕ}, 1 ≤ n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- EReal.inv_nonpos_of_nonpos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.inv_nonpos_of_nonpos.h1 : ¬∀ {a : EReal}, a⁻¹ ≤ 0 := fun hc_h => absurd (@hc_h (1)) (by
  simp)

-- PNat.val_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.val_ofNat.h1 : ¬∀ (n : ℕ), NeZero n := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Rat.inv_ofNat_num, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.inv_ofNat_num.h1 : Not
      (∀ (a : Nat),
        @Eq Int (@Inv.inv Rat Rat.instInv (@OfNat.ofNat Rat a (@Rat.instOfNat a))).num
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- PNat.mk_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.mk_ofNat.h1 : ¬∀ (n : ℕ), 0 < n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.odd_of_mod_four_eq_three, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.odd_of_mod_four_eq_three.h1 : ¬∀ {n : ℕ}, n % 2 = 1 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- PNat.exists_eq_succ_of_ne_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.exists_eq_succ_of_ne_one.h1 : ¬∀ {n : ℕ+}, ∃ (k : ℕ+), n = k + 1 := fun hc_h => absurd (@hc_h (1)) (by
  nofun)

-- ENat.natCast_lift, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.natCast_lift.h1 : ¬∀ (x : ℕ∞), x < ⊤ := fun hc_h => absurd (@hc_h (⊤)) (by
  decide +kernel)

-- Rat.inv_natCast_num_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.inv_natCast_num_of_pos.h1 : Not
      (∀ {a : Nat},
        @Eq Int (@Inv.inv Rat Rat.instInv (@Nat.cast Rat Rat.instNatCast a)).num
          (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- ZMod.eq_one_of_isUnit_natCast, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.eq_one_of_isUnit_natCast.h1 : ¬∀ {n : ℕ}, n = 1 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- NNRat.den_mk, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNRat.den_mk.h1 : ¬∀ (q : ℚ), 0 ≤ q := fun hc_h => absurd (@hc_h (-1)) (by
  decide +kernel)

-- Nat.binaryRec_decreasing, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.binaryRec_decreasing.h1 : ¬∀ {n : ℕ}, n.div2 < n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Set.subsingleton_of_univ_subsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subsingleton_of_univ_subsingleton.h1 : ¬∀ {α : Type}, Subsingleton α := fun hc_h => absurd (@hc_h (ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Rat.coe_toNNRat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.coe_toNNRat.h1 : ¬∀ (q : ℚ), ↑q.toNNRat = q := fun hc_h => absurd (@hc_h (-1)) (by
  decide +kernel)

-- Nat.lt_factorial_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_factorial_self.h1 : ¬∀ {n : ℕ}, n < n.factorial := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- Nat.succ_pred_prime, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.succ_pred_prime.h1 : ¬∀ {p : ℕ}, p.pred.succ = p := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.AtLeastTwo.neZero_sub_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.AtLeastTwo.neZero_sub_one.h1 : ¬∀ (n : ℕ), NeZero (n - 1) := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.fib_add_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.fib_add_one.h1 : ¬∀ {n : ℕ}, Nat.fib (n + 1) = Nat.fib (n - 1) + Nat.fib n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- PrimeMultiset.prod_ofPNatList, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PrimeMultiset.prod_ofPNatList.h1 : ¬∀ (l : List ℕ+), ∀ p ∈ l, p.Prime := fun hc_h => absurd (@hc_h ([1])) (by
  simp)

-- Nat.le_fib_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_fib_self.h1 : ¬∀ {n : ℕ}, n ≤ Nat.fib n := fun hc_h => absurd (@hc_h (2)) (by
  decide +kernel)

-- PNat.eq_one_of_lt_two, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.eq_one_of_lt_two.h1 : ¬∀ {n : ℕ+}, n = 1 := fun hc_h => absurd (@hc_h (2)) (by
  decide +kernel)

-- Nat.not_prime_iff_exists_dvd_ne, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_prime_iff_exists_dvd_ne.h1 : ¬∀ {n : ℕ}, ¬Nat.Prime n ↔ ∃ (m : ℕ), m ∣ n ∧ m ≠ 1 ∧ m ≠ n := fun hc_h => absurd (@hc_h (1)) (by
  (simp <;> decide))

-- PNat.XgcdType.step_v, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.XgcdType.step_v.h1 : ¬∀ (u : PNat.XgcdType), u.step.v = u.v.swap := fun hc_h => absurd (@hc_h ({ wp := 0, x := 0, y := 0, zp := 0, ap := 0, bp := 0 : PNat.XgcdType })) (by
  decide +kernel)

-- PNat.XgcdType.qp_eq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.XgcdType.qp_eq.h1 : ¬∀ (u : PNat.XgcdType), u.q = u.qp + 1 := fun hc_h => absurd (@hc_h ({ wp := 0, x := 0, y := 0, zp := 0, ap := 0, bp := 1 : PNat.XgcdType })) (by
  decide +kernel)

-- Nat.bit0_bits, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bit0_bits.h1 : ¬∀ (n : ℕ), (2 * n).bits = Bool.false :: n.bits := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Fin.one_pos', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.one_pos'.h1 : Not
      (∀ {n : Nat},
        @LT.lt
          (Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@instLTFin
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

-- ENat.top_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.top_pow.h1 : Not
      (∀ {n : Nat},
        @Eq ENat
          (@HPow.hPow ENat Nat ENat
            (@instHPow ENat Nat
              (@NPow.toPow ENat
                (@Monoid.toNPow ENat (@Semiring.toMonoid ENat (@CommSemiring.toSemiring ENat instCommSemiringENat)))))
            (@Top.top ENat instTopENat) n)
          (@Top.top ENat instTopENat)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- PNat.Prime.one_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Prime.one_lt.h1 : ¬∀ {p : ℕ+}, 1 < p := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- Fin.size_positive', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.size_positive'.h1 : ¬∀ {n : ℕ}, 0 < n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.emultiplicity_two_factorial_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.emultiplicity_two_factorial_lt.h1 : ¬∀ {n : ℕ}, emultiplicity 2 n.factorial < ↑n := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Int.pow_right_injective, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.pow_right_injective.h1 : ¬∀ {a : ℤ}, Function.Injective fun (x : ℕ) => a ^ x := fun hc_h => absurd (@hc_h (1)) (by
  simp)

-- Nat.Prime.factorization_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.factorization_self.h1 : ¬∀ {p : ℕ}, p.factorization p = 1 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- PNat.instFactPrimeValOfPrime, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.instFactPrimeValOfPrime.h1 : ¬∀ {p : ℕ+}, Fact (Nat.Prime ↑p) := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- Choose.gcd_choose_eq_minFac_of_isPrimePow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.gcd_choose_eq_minFac_of_isPrimePow.h1 : ¬∀ {n : ℕ}, (Finset.Icc 1 (n - 1)).gcd n.choose = n.minFac := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.Prime.mod_two_eq_one_iff_ne_two, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.mod_two_eq_one_iff_ne_two.h1 : ¬∀ {p : ℕ}, p % 2 = 1 ↔ p ≠ 2 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.Prime.emultiplicity_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.emultiplicity_one.h1 : ¬∀ {p : ℕ}, emultiplicity p 1 = 0 := fun hc_h => absurd (@hc_h (1)) (by
  simp)

-- ENat.zero_epow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.zero_epow.h1 : Not
      (∀ {y : ENat},
        @Eq ENat
          (@HPow.hPow ENat ENat ENat (@instHPow ENat ENat ENat.instPow)
            (@OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat)) y)
          (@OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat))) (by
  decide +kernel)

-- ENat.epow_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.epow_top.h1 : Not
      (∀ {x : ENat},
        @Eq ENat (@HPow.hPow ENat ENat ENat (@instHPow ENat ENat ENat.instPow) x (@Top.top ENat instTopENat))
          (@Top.top ENat instTopENat)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat))) (by
  decide +kernel)

-- EReal.toReal_nonpos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toReal_nonpos.h1 : ¬∀ {x : EReal}, x.toReal ≤ 0 := fun hc_h => absurd (@hc_h (1)) (by
  simp)

-- Nat.AtLeastTwo.ne_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.AtLeastTwo.ne_one.h1 : ¬∀ {n : ℕ}, n ≠ 1 := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- Int.fib_of_odd, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.fib_of_odd.h1 : ¬∀ {n : ℤ}, Int.fib n = ↑(Nat.fib n.natAbs) := fun hc_h => absurd (@hc_h (-2)) (by
  decide +kernel)

-- Bool.eq_true_of_not_eq_false', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.eq_true_of_not_eq_false'.h1 : ¬∀ {a : Bool}, a = Bool.true := fun hc_h => absurd (@hc_h (Bool.false)) (by
  decide +kernel)

-- Fin.val_rev_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_rev_zero.h1 : ¬∀ {n : ℕ}, NeZero n := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- EReal.coe_toENNReal, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.coe_toENNReal.h1 : ¬∀ {x : EReal}, ↑x.toENNReal = x := fun hc_h => absurd (@hc_h (⊥)) (by
  decide +kernel)

-- Nat.prod_factorization_pow_eq_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prod_factorization_pow_eq_self.h1 : ¬∀ {n : ℕ}, (n.factorization.prod fun (x1 x2 : ℕ) => x1 ^ x2) = n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- IsPrimePow.minFac_pow_factorization_eq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsPrimePow.minFac_pow_factorization_eq.h1 : ¬∀ {n : ℕ}, n.minFac ^ n.factorization n.minFac = n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- IsPrimePow.exists_ordCompl_eq_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsPrimePow.exists_ordCompl_eq_one.h1 : ¬∀ {n : ℕ}, ∃ (p : ℕ), Nat.Prime p ∧ n / p ^ n.factorization p = 1 := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- EReal.toENNReal_of_ne_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toENNReal_of_ne_top.h1 : ¬∀ {x : EReal}, x.toENNReal = ENNReal.ofReal x.toReal := fun hc_h => absurd (@hc_h (⊤)) (by
  decide +kernel)

-- Nat.divisors_eq_map_attach_Iic_factorization_prod_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.divisors_eq_map_attach_Iic_factorization_prod_pow.h1 : Not
      (∀ {n : Nat},
        @Eq (Finset Nat) n.divisors
          (@Finset.map
            (↥(@Finset.Iic (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                (@Finsupp.preorder Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instPreorder)
                (@LocallyFiniteOrder.toLocallyFiniteOrderBot
                  (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                  (@Finsupp.preorder Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instPreorder)
                  (@Finsupp.instLocallyFiniteOrder Nat Nat Nat.instPartialOrder
                    (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instLocallyFiniteOrder instDecidableEqNat
                    instDecidableEqNat)
                  (@Finsupp.orderBot Nat Nat Nat.instAddCommMonoid Nat.instPartialOrder
                    (@LinearOrderedCommMonoidWithZero.toIsBotZeroClass Nat Nat.instLinearOrderedCommMonoidWithZero)))
                n.factorization))
            Nat
            (@Function.Embedding.mk
              (↥(@Finset.Iic (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                  (@Finsupp.preorder Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instPreorder)
                  (@LocallyFiniteOrder.toLocallyFiniteOrderBot
                    (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                    (@Finsupp.preorder Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instPreorder)
                    (@Finsupp.instLocallyFiniteOrder Nat Nat Nat.instPartialOrder
                      (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instLocallyFiniteOrder instDecidableEqNat
                      instDecidableEqNat)
                    (@Finsupp.orderBot Nat Nat Nat.instAddCommMonoid Nat.instPartialOrder
                      (@LinearOrderedCommMonoidWithZero.toIsBotZeroClass Nat Nat.instLinearOrderedCommMonoidWithZero)))
                  n.factorization))
              Nat
              (fun
                  (x :
                    ↥(@Finset.Iic (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                        (@Finsupp.preorder Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instPreorder)
                        (@LocallyFiniteOrder.toLocallyFiniteOrderBot
                          (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                          (@Finsupp.preorder Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instPreorder)
                          (@Finsupp.instLocallyFiniteOrder Nat Nat Nat.instPartialOrder
                            (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instLocallyFiniteOrder instDecidableEqNat
                            instDecidableEqNat)
                          (@Finsupp.orderBot Nat Nat Nat.instAddCommMonoid Nat.instPartialOrder
                            (@LinearOrderedCommMonoidWithZero.toIsBotZeroClass Nat
                              Nat.instLinearOrderedCommMonoidWithZero)))
                        n.factorization)) =>
                @Finsupp.prod Nat Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instCommMonoid
                  (@Subtype.val (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                    (fun (x : @Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) =>
                      @Membership.mem (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                        (Finset (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))
                        (@SetLike.instMembership (Finset (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)))
                          (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                          (@Finset.instSetLike (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))))
                        (@Finset.Iic (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                          (@Finsupp.preorder Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instPreorder)
                          (@LocallyFiniteOrder.toLocallyFiniteOrderBot
                            (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                            (@Finsupp.preorder Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instPreorder)
                            (@Finsupp.instLocallyFiniteOrder Nat Nat Nat.instPartialOrder
                              (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instLocallyFiniteOrder instDecidableEqNat
                              instDecidableEqNat)
                            (@Finsupp.orderBot Nat Nat Nat.instAddCommMonoid Nat.instPartialOrder
                              (@LinearOrderedCommMonoidWithZero.toIsBotZeroClass Nat
                                Nat.instLinearOrderedCommMonoidWithZero)))
                          n.factorization)
                        x)
                    x)
                  fun (x1 x2 : Nat) =>
                  @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) x1 x2)
              (Nat.Iic_factorization_prod_pow_injective n))
            (@Finset.attach (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
              (@Finset.Iic (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                (@Finsupp.preorder Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instPreorder)
                (@LocallyFiniteOrder.toLocallyFiniteOrderBot
                  (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass))
                  (@Finsupp.preorder Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instPreorder)
                  (@Finsupp.instLocallyFiniteOrder Nat Nat Nat.instPartialOrder
                    (@MulZeroClass.toZero Nat Nat.instMulZeroClass) Nat.instLocallyFiniteOrder instDecidableEqNat
                    instDecidableEqNat)
                  (@Finsupp.orderBot Nat Nat Nat.instAddCommMonoid Nat.instPartialOrder
                    (@LinearOrderedCommMonoidWithZero.toIsBotZeroClass Nat Nat.instLinearOrderedCommMonoidWithZero)))
                n.factorization)))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Nat.ceilRoot_one_right, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ceilRoot_one_right.h1 : ¬∀ {n : ℕ}, n.ceilRoot 1 = 1 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- EReal.le_coe_toReal, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.le_coe_toReal.h1 : ¬∀ {x : EReal}, x ≤ ↑x.toReal := fun hc_h => absurd (@hc_h (⊤)) (by
  decide +kernel)

-- ENat.ofNat_ne_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.ofNat_ne_top.h1 : ¬∀ (a : ℕ), a.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.greatestFib_fib, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.greatestFib_fib.h1 : ¬∀ {n : ℕ}, (Nat.fib n).greatestFib = n := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- Nat.ppred_eq_pred, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ppred_eq_pred.h1 : ¬∀ {n : ℕ}, n.ppred = Option.some n.pred := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.divisors_filter_squarefree_of_squarefree, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.divisors_filter_squarefree_of_squarefree.h1 : ¬∀ {n : ℕ}, {d ∈ n.divisors | Squarefree d} = n.divisors := fun hc_h => absurd (@hc_h (4)) (by
  decide +kernel)

-- Nat.range_nth_of_infinite, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.range_nth_of_infinite.h1 : ¬∀ {p : ℕ → Prop}, Set.range (Nat.nth p) = Set.ofPred p := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop)) (by
  simp)

-- Finset.univ_finset_of_isEmpty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.univ_finset_of_isEmpty.h1 : Not
      (∀ {α : Type},
        @Eq (Set (Finset α)) (@Set.univ (Finset α))
          (@Singleton.singleton (Finset α) (Set (Finset α)) (@Set.instSingletonSet (Finset α))
            (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α)))) := fun hc_h => absurd (@hc_h (Nat)) (by
  simp)

-- List.fixedLengthDigits_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.fixedLengthDigits_zero.h1 : ¬∀ {b : ℕ}, 1 < b := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.prime_maxPrimeFac_of_one_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prime_maxPrimeFac_of_one_lt.h1 : ¬∀ {n : ℕ}, Nat.Prime n.maxPrimeFac := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.Prime.maxPrimeFac_eq_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.maxPrimeFac_eq_self.h1 : ¬∀ {p : ℕ}, p.maxPrimeFac = p := fun hc_h => absurd (@hc_h (4)) (by
  decide +kernel)

-- EReal.top_mul_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.top_mul_of_pos.h1 : ¬∀ {x : EReal}, ⊤ * x = ⊤ := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Finset.Aesop.range_nonempty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Aesop.range_nonempty.h1 : ¬∀ {n : ℕ}, (Finset.range n).Nonempty := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Fin.one_lt_last, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.one_lt_last.h1 : ¬∀ {n : ℕ}, 1 < Fin.last (n + 1) := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- EReal.bot_mul_of_neg, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.bot_mul_of_neg.h1 : ¬∀ {x : EReal}, ⊥ * x = ⊤ := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Odd.coprime_two_left, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Odd.coprime_two_left.h1 : ¬∀ {n : ℕ}, Nat.Coprime 2 n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.two_mul_odd_div_two, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.two_mul_odd_div_two.h1 : ¬∀ {n : ℕ}, 2 * (n / 2) = n - 1 := fun hc_h => absurd (@hc_h (2)) (by
  decide +kernel)

-- Finset.range_nontrivial, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.range_nontrivial.h1 : ¬∀ {n : ℕ}, (Finset.range n).Nontrivial := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Fin.succ_one_eq_two', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succ_one_eq_two'.h1 : Not
      (∀ {n : Nat},
        @Eq
          (Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Fin.succ
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
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
                (nat_lit 1))))
          (@OfNat.ofNat
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (nat_lit 2)
            (@Fin.instOfNat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@instNeZeroNatHAdd_1
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (nat_lit 2)))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Rat.eq_num_of_isInt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.eq_num_of_isInt.h1 : ¬∀ {q : ℚ}, q = ↑q.num := fun hc_h => absurd (@hc_h (1 / 2)) (by
  decide +kernel)

-- Nat.prod_pow_primeFactors_factorization, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prod_pow_primeFactors_factorization.h1 : Not
      (∀ {n : Nat},
        @Eq Nat n
          (∏ p : ↥n.primeFactors,
            @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (@Subtype.val Nat
                (fun (x : Nat) =>
                  @Membership.mem Nat (Finset Nat) (@SetLike.instMembership (Finset Nat) Nat (@Finset.instSetLike Nat))
                    n.primeFactors x)
                p)
              (@DFunLike.coe (@Finsupp Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) Nat (fun (x : Nat) => Nat)
                (@Finsupp.instFunLike Nat Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) n.factorization
                (@Subtype.val Nat
                  (fun (x : Nat) =>
                    @Membership.mem Nat (Finset Nat) (@SetLike.instMembership (Finset Nat) Nat (@Finset.instSetLike Nat))
                      n.primeFactors x)
                  p)))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

