import Mathlib

/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- smul_dvd_smul, hypothesis 12: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.smul_dvd_smul.h12 : ¬∀ {α β : Type} [inst : Monoid α] [inst_1 : Monoid β] [inst_2 : SMul α β] [inst_3 : IsScalarTower α β β]
        [inst : IsScalarTower α α β] [inst : SMulCommClass α β β] {a b : α} {c d : β}, c ∣ d → a • c ∣ b • d := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMonoid) (Nat.instMonoid) (instSMulOfMul) _ _ _ (0) (1) (1) (1) (by
  decide)) (by
  decide +kernel)

-- smul_dvd_smul, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.smul_dvd_smul.h13 : ¬∀ {α β : Type} [inst : Monoid α] [inst_1 : Monoid β] [inst_2 : SMul α β] [inst_3 : IsScalarTower α β β]
        [inst_4 : IsScalarTower α α β] [inst_5 : SMulCommClass α β β] {a b : α} {c d : β}, a ∣ b → a • c ∣ b • d := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMonoid) (Nat.instMonoid) (instSMulOfMul) _ _ _ (1) (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Set.PairwiseDisjoint.eq_of_le, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h6.inst : ¬0 = 2 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h6.prem0 : 0 ∈ {n : ℕ | n % 2 = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h6.prem1 : 2 ∈ {n : ℕ | n % 2 = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h6.prem2 : (fun (n : ℕ) => n + 1) 0 ≠ ⊥ := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h6.prem3 : (fun (n : ℕ) => n + 1) 0 ≤ (fun (n : ℕ) => n + 1) 2 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h6 : ¬∀ {α ι : Type} [inst : SemilatticeInf α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α} {i j : ι},
        i ∈ s → j ∈ s → f i ≠ ⊥ → f i ≤ f j → i = j := fun hc_h => HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h6.inst (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) (Nat.instOrderBot) ({n : ℕ | n % 2 = 0}) (fun (n : ℕ) => n + 1) (0) (2) HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h6.prem0 HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h6.prem1 HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h6.prem2 HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h6.prem3)

-- Set.PairwiseDisjoint.eq_of_le, hypothesis 9: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h9.inst : ¬2 = 0 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h9.prem0 : {n : ℕ | n = 0}.PairwiseDisjoint fun (n : ℕ) => n % 2 == 0 := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h9.prem1 : 0 ∈ {n : ℕ | n = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h9.prem2 : (fun (n : ℕ) => n % 2 == 0) 2 ≠ ⊥ := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h9.prem3 : (fun (n : ℕ) => n % 2 == 0) 2 ≤ (fun (n : ℕ) => n % 2 == 0) 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h9 : ¬∀ {α ι : Type} [inst : SemilatticeInf α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},
        s.PairwiseDisjoint f → ∀ {i j : ι}, j ∈ s → f i ≠ ⊥ → f i ≤ f j → i = j := fun hc_h => HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h9.inst (@hc_h (Bool) (ℕ) (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.toSemilatticeInf) (CompleteLattice.toCompletePartialOrder.toOrderBot) ({n : ℕ | n = 0}) (fun (n : ℕ) => n % 2 == 0) HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h9.prem0 (2) (0) HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h9.prem1 HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h9.prem2 HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h9.prem3)

-- Set.PairwiseDisjoint.eq_of_le, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h10.inst : ¬0 = 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h10.prem0 : {n : ℕ | n = 0}.PairwiseDisjoint fun (n : ℕ) => n + 1 := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h10.prem1 : 0 ∈ {n : ℕ | n = 0} := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h10.prem2 : (fun (n : ℕ) => n + 1) 0 ≠ ⊥ := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h10.prem3 : (fun (n : ℕ) => n + 1) 0 ≤ (fun (n : ℕ) => n + 1) 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h10 : ¬∀ {α ι : Type} [inst : SemilatticeInf α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},
        s.PairwiseDisjoint f → ∀ {i j : ι}, i ∈ s → f i ≠ ⊥ → f i ≤ f j → i = j := fun hc_h => HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h10.inst (@hc_h (ℕ) (ℕ) (Nat.instLattice.toSemilatticeInf) (Nat.instOrderBot) ({n : ℕ | n = 0}) (fun (n : ℕ) => n + 1) HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h10.prem0 (0) (1) HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h10.prem1 HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h10.prem2 HypCheckProof.Set.PairwiseDisjoint.eq_of_le.h10.prem3)

-- Set.IsWF.min_vadd, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.IsWF.min_vadd.h5 : ¬∀ {G P : Type} [inst : LinearOrder G] [inst_1 : LinearOrder P] [inst_2 : VAdd G P] {s : Set G} {t : Set P},
        s.IsWF → t.IsWF → s.Nonempty → t.Nonempty → IsOrderedVAdd G P := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.linearOrder) (Bool.linearOrder) (instVAddOfAdd) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  simp) (by
  simp) (by
  simp) (by
  simp)) (by
  exact fun hc_c =>
    absurd
      (hc_c.vadd_le_vadd_left (Bool.false : Bool) (Bool.true : Bool)
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel))
        (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.IsWF.min_vadd, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.IsWF.min_vadd.h10 : ¬∀ {G P : Type} [inst : LinearOrder G] [inst_1 : LinearOrder P] [inst_2 : VAdd G P] [inst_3 : IsOrderedVAdd G P]
        {s : Set G} {t : Set P}, s.IsWF → t.IsWF → t.Nonempty → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instLinearOrder) (instVAddOfAdd) _ ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- Set.IsWF.min_vadd, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.IsWF.min_vadd.h11 : ¬∀ {G P : Type} [inst : LinearOrder G] [inst_1 : LinearOrder P] [inst_2 : VAdd G P] [inst_3 : IsOrderedVAdd G P]
        {s : Set G} {t : Set P}, s.IsWF → t.IsWF → s.Nonempty → t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instLinearOrder) (instVAddOfAdd) _ ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- Finset.addAntidiagonal_mono_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.addAntidiagonal_mono_left.h3 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO} {a : α}
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

-- Finset.mulAntidiagonal_mono_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mulAntidiagonal_mono_left.h3 : ¬∀ {α : Type} [inst : CommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO} {a : α}
        {u : Set α} {hu : u.IsPWO}, u ⊆ s → IsOrderedCancelMonoid α := fun hc_h => absurd (@hc_h (Bool) (BooleanRing.toCommRing.toCommMonoid) (Bool.instPartialOrder) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
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

-- List.IsChain.backwards_cons_induction, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h6.inst : ¬(fun (n : ℕ) => n = 0) 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h6.prem0 : ∀ ⦃x y : ℕ⦄, x < y → y = 0 → (fun (n : ℕ) => n = 0) x := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h6.prem1 : (fun (n : ℕ) => n = 0) ([1, 0].getLast (List.cons_ne_nil 1 [0])) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h6.prem2 : 1 ∈ [1, 0] := by
  decide
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        (a :: l).getLast (List.cons_ne_nil a l) = b → (∀ ⦃x y : α⦄, r x y → p y → p x) → p b → ∀ i ∈ a :: l, p i := fun hc_h => HypCheckProof.List.IsChain.backwards_cons_induction.h6.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (1) ([1, 0].getLast (List.cons_ne_nil 1 [0])) (fun (n : ℕ) => n = 0) ([0]) rfl HypCheckProof.List.IsChain.backwards_cons_induction.h6.prem0 HypCheckProof.List.IsChain.backwards_cons_induction.h6.prem1 (1) HypCheckProof.List.IsChain.backwards_cons_induction.h6.prem2)

-- List.IsChain.backwards_cons_induction, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h7 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        List.IsChain r (a :: l) → (∀ ⦃x y : α⦄, r x y → p y → p x) → p b → ∀ i ∈ a :: l, p i := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) (0) (fun n => n = 0 : ℕ → Prop) ([]) (by
  decide) (by
  omega) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.backwards_cons_induction, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h8.inst : ¬(fun (b : Bool) => b = Bool.true) Bool.false := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h8.prem0 : List.IsChain (fun (x x_1 : Bool) => True) [Bool.false, Bool.true] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h8.prem1 : (fun (b : Bool) => b = Bool.true) ([Bool.false, Bool.true].getLast (List.cons_ne_nil Bool.false [Bool.true])) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h8.prem2 : Bool.false ∈ [Bool.false, Bool.true] := by
  decide
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h8 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        List.IsChain r (a :: l) → (a :: l).getLast (List.cons_ne_nil a l) = b → p b → ∀ i ∈ a :: l, p i := fun hc_h => HypCheckProof.List.IsChain.backwards_cons_induction.h8.inst (@hc_h (Bool) (fun (x x_1 : Bool) => True) (Bool.false) ([Bool.false, Bool.true].getLast (List.cons_ne_nil Bool.false [Bool.true])) (fun (b : Bool) => b = Bool.true) ([Bool.true]) HypCheckProof.List.IsChain.backwards_cons_induction.h8.prem0 rfl HypCheckProof.List.IsChain.backwards_cons_induction.h8.prem1 (Bool.false) HypCheckProof.List.IsChain.backwards_cons_induction.h8.prem2)

-- List.IsChain.backwards_cons_induction, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h9 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        List.IsChain r (a :: l) →
          (a :: l).getLast (List.cons_ne_nil a l) = b → (∀ ⦃x y : α⦄, r x y → p y → p x) → ∀ i ∈ a :: l, p i := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) _ (fun _ => False : ℕ → Prop) ([]) (by
  decide) rfl (by
  simp) (0) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.backwards_cons_induction, hypothesis 11: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h11.inst : ¬(fun (n : ℕ) => n = 0) 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h11.prem0 : List.IsChain (fun (a b : ℕ) => a < b) [0] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h11.prem1 : ∀ ⦃x y : ℕ⦄, x < y → y = 0 → (fun (n : ℕ) => n = 0) x := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h11.prem2 : (fun (n : ℕ) => n = 0) ([0].getLast (List.cons_ne_nil 0 [])) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.IsChain.backwards_cons_induction.h11 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        List.IsChain r (a :: l) →
          (a :: l).getLast (List.cons_ne_nil a l) = b → (∀ ⦃x y : α⦄, r x y → p y → p x) → p b → ∀ (i : α), p i := fun hc_h => HypCheckProof.List.IsChain.backwards_cons_induction.h11.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (0) ([0].getLast (List.cons_ne_nil 0 [])) (fun (n : ℕ) => n = 0) ([]) HypCheckProof.List.IsChain.backwards_cons_induction.h11.prem0 rfl HypCheckProof.List.IsChain.backwards_cons_induction.h11.prem1 HypCheckProof.List.IsChain.backwards_cons_induction.h11.prem2 (1))

-- Set.PairwiseDisjoint.disjoint_of_ne, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.PairwiseDisjoint.disjoint_of_ne.h11 : ¬∀ {α ι : Type} [inst : PartialOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},
        s.PairwiseDisjoint f → ∀ {i j : ι}, i ∈ s → j ∈ s → Disjoint (f i) (f j) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instPartialOrder) (Nat.instOrderBot) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  simp) (0) (0) (by
  decide) (by
  decide)) (by
  simp)

-- Set.PairwiseDisjoint.elim, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim.h9 : ¬∀ {α ι : Type} [inst : PartialOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},
        s.PairwiseDisjoint f → ∀ {i j : ι}, j ∈ s → ¬Disjoint (f i) (f j) → i = j := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.instPartialOrder) (CompleteLattice.toCompletePartialOrder.toOrderBot) ({n : ℕ | n = 0}) (fun n => n % 2 == 0 : ℕ → Bool) (by
  simp) (2) (0) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Set.PairwiseDisjoint.elim, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.PairwiseDisjoint.elim.h10 : ¬∀ {α ι : Type} [inst : PartialOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},
        s.PairwiseDisjoint f → ∀ {i j : ι}, i ∈ s → ¬Disjoint (f i) (f j) → i = j := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.instPartialOrder) (CompleteLattice.toCompletePartialOrder.toOrderBot) ({n : ℕ | n = 0}) (fun n => n % 2 == 0 : ℕ → Bool) (by
  simp) (0) (2) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Finset.antidiagonal_min_add_min, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.antidiagonal_min_add_min.h3 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : LinearOrder α] {s t : Set α},
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

-- Finset.antidiagonal_min_add_min, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.antidiagonal_min_add_min.h8 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : LinearOrder α] [inst : IsOrderedCancelAddMonoid α] {s t : Set α},
        s.IsWF → t.IsWF → t.Nonempty → s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddCommMonoid) (Nat.instLinearOrder) _ ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- Finset.antidiagonal_min_add_min, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.antidiagonal_min_add_min.h9 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : LinearOrder α] [inst : IsOrderedCancelAddMonoid α] {s t : Set α},
        s.IsWF → t.IsWF → s.Nonempty → t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddCommMonoid) (Nat.instLinearOrder) _ ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (by
  simp) (by
  simp)) (by
  simp)

-- List.Pairwise.forall_of_forall, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.forall_of_forall.h4 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} [inst : Std.Symm R],
        List.Pairwise R l → ∀ ⦃x : α⦄, x ∈ l → ∀ ⦃y : α⦄, y ∈ l → R x y := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => False : Bool → Bool → Prop) ([Bool.false]) _ (by
  decide) (Bool.false) (by
  decide) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.forall_of_forall, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.forall_of_forall.h9 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} [inst : Std.Symm R],
        (∀ x ∈ l, R x x) → List.Pairwise R l → ∀ ⦃x : α⦄, x ∈ l → ∀ ⦃y : α⦄, R x y := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) ([0]) _ (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide) (0) (by
  decide) (1)) (by
  decide +kernel)

-- Ordnode.all_balanceR, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.all_balanceR.h7 : ¬∀ {α : Type} {P : α → Prop} {l : Ordnode α} {x : α} {r : Ordnode α},
        l.Balanced →
          r.Balanced →
            r.Sized →
              ((∃ (l' : ℕ), Ordnode.Raised l.size l' ∧ Ordnode.BalancedSz l' r.size) ∨
                  ∃ (r' : ℕ), Ordnode.Raised r' r.size ∧ Ordnode.BalancedSz l.size r') →
                (Ordnode.All P (l.balanceR x r) ↔ Ordnode.All P l ∧ P x ∧ Ordnode.All P r) := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (1) (Ordnode.node 1 Ordnode.nil 0 Ordnode.nil) (by
  decide) (by
  decide) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Ordnode.all_balanceL, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.all_balanceL.h8 : ¬∀ {α : Type} {P : α → Prop} {l : Ordnode α} {x : α} {r : Ordnode α},
        l.Balanced →
          r.Balanced →
            l.Sized →
              ((∃ (l' : ℕ), Ordnode.Raised l' l.size ∧ Ordnode.BalancedSz l' r.size) ∨
                  ∃ (r' : ℕ), Ordnode.Raised r.size r' ∧ Ordnode.BalancedSz l.size r') →
                (Ordnode.All P (l.balanceL x r) ↔ Ordnode.All P l ∧ P x ∧ Ordnode.All P r) := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (Ordnode.node 1 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 1 Ordnode.nil) (by
  decide) (by
  decide) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- List.Subset.antisymm_of_pairwise, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subset.antisymm_of_pairwise.h8 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Std.Antisymm r] [inst : Std.Irrefl r] {l₁ l₂ : List α},
        List.Pairwise r l₁ → List.Pairwise r l₂ → l₂ ⊆ l₁ → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ _ ([0]) ([]) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Subset.antisymm_of_pairwise, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subset.antisymm_of_pairwise.h9 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Std.Antisymm r] [inst : Std.Irrefl r] {l₁ l₂ : List α},
        List.Pairwise r l₁ → List.Pairwise r l₂ → l₁ ⊆ l₂ → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ _ ([]) ([0]) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.concat_induction_head, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.concat_induction_head.h7 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        List.IsChain r (l ++ [b]) → (∀ ⦃x y : α⦄, r x y → p x → p y) → p a → p b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (0) (1) (fun n => n = 0 : ℕ → Prop) ([]) (by
  decide) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- List.IsChain.concat_induction_head, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.concat_induction_head.h8.inst : ¬(fun (n : ℕ) => n = 0) 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.concat_induction_head.h8.prem0 : List.IsChain (fun (a b : ℕ) => a < b) ([0] ++ [1]) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.concat_induction_head.h8.prem1 : (fun (n : ℕ) => n = 0) (([0] ++ [1]).head (List.concat_ne_nil 1 [0])) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.IsChain.concat_induction_head.h8 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        List.IsChain r (l ++ [b]) → (l ++ [b]).head (List.concat_ne_nil b l) = a → p a → p b := fun hc_h => HypCheckProof.List.IsChain.concat_induction_head.h8.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (([0] ++ [1]).head (List.concat_ne_nil 1 [0])) (1) (fun (n : ℕ) => n = 0) ([0]) HypCheckProof.List.IsChain.concat_induction_head.h8.prem0 rfl HypCheckProof.List.IsChain.concat_induction_head.h8.prem1)

-- List.IsChain.concat_induction_head, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.concat_induction_head.h9 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        List.IsChain r (l ++ [b]) → (l ++ [b]).head (List.concat_ne_nil b l) = a → (∀ ⦃x y : α⦄, r x y → p x → p y) → p b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ (0) (fun _ => False : ℕ → Prop) ([]) (by
  decide) rfl (by
  simp)) (by
  decide +kernel)

-- List.IsChain.backwards_cons_induction_head, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction_head.h6.inst : ¬(fun (n : ℕ) => n = 0) 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction_head.h6.prem0 : ∀ ⦃x y : ℕ⦄, x < y → y = 0 → (fun (n : ℕ) => n = 0) x := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction_head.h6.prem1 : (fun (n : ℕ) => n = 0) ([1, 0].getLast (List.cons_ne_nil 1 [0])) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.IsChain.backwards_cons_induction_head.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        (a :: l).getLast (List.cons_ne_nil a l) = b → (∀ ⦃x y : α⦄, r x y → p y → p x) → p b → p a := fun hc_h => HypCheckProof.List.IsChain.backwards_cons_induction_head.h6.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (1) ([1, 0].getLast (List.cons_ne_nil 1 [0])) (fun (n : ℕ) => n = 0) ([0]) rfl HypCheckProof.List.IsChain.backwards_cons_induction_head.h6.prem0 HypCheckProof.List.IsChain.backwards_cons_induction_head.h6.prem1)

-- List.IsChain.backwards_cons_induction_head, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction_head.h7 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        List.IsChain r (a :: l) → (∀ ⦃x y : α⦄, r x y → p y → p x) → p b → p a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) (0) (fun n => n = 0 : ℕ → Prop) ([]) (by
  decide) (by
  omega) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- List.IsChain.backwards_cons_induction_head, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction_head.h8.inst : ¬(fun (b : Bool) => b = Bool.true) Bool.false := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction_head.h8.prem0 : List.IsChain (fun (x x_1 : Bool) => True) [Bool.false, Bool.true] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction_head.h8.prem1 : (fun (b : Bool) => b = Bool.true) ([Bool.false, Bool.true].getLast (List.cons_ne_nil Bool.false [Bool.true])) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.IsChain.backwards_cons_induction_head.h8 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        List.IsChain r (a :: l) → (a :: l).getLast (List.cons_ne_nil a l) = b → p b → p a := fun hc_h => HypCheckProof.List.IsChain.backwards_cons_induction_head.h8.inst (@hc_h (Bool) (fun (x x_1 : Bool) => True) (Bool.false) ([Bool.false, Bool.true].getLast (List.cons_ne_nil Bool.false [Bool.true])) (fun (b : Bool) => b = Bool.true) ([Bool.true]) HypCheckProof.List.IsChain.backwards_cons_induction_head.h8.prem0 rfl HypCheckProof.List.IsChain.backwards_cons_induction_head.h8.prem1)

-- List.IsChain.backwards_cons_induction_head, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.backwards_cons_induction_head.h9 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
        List.IsChain r (a :: l) → (a :: l).getLast (List.cons_ne_nil a l) = b → (∀ ⦃x y : α⦄, r x y → p y → p x) → p a := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) _ (fun n => n = 0 : ℕ → Prop) ([]) (by
  decide) rfl (by
  omega)) (by
  decide +kernel)

-- List.IsChain.cons_induction, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons_induction.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a : α} (p : α → Prop) (l : List α), List.IsChain r (a :: l) → p a → ∀ i ∈ l, p i := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (fun n => n = 0 : ℕ → Prop) ([1]) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.cons_induction, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons_induction.h9 : ¬∀ {α : Type} {r : α → α → Prop} {a : α} (p : α → Prop) (l : List α),
        List.IsChain r (a :: l) → (∀ ⦃x y : α⦄, r x y → p x → p y) → p a → ∀ (i : α), p i := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (0) (fun n => n = 0 : ℕ → Prop) ([]) (by
  decide) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1)) (by
  decide +kernel)

-- Disjoint.image, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.image.h6 : ¬∀ {α β : Type} {s t u : Set α} {f : α → β}, Set.InjOn f u → s ⊆ u → t ⊆ u → Disjoint (f '' s) (f '' t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  simp) (by
  rfl) (by
  rfl)) (by
  simp)

-- Set.InjOn.cancel_left, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.cancel_left.h9 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {f₁ f₂ : α → β} {g : β → γ},
        Set.InjOn g t → Set.MapsTo f₂ s t → (Set.EqOn (g ∘ f₁) (g ∘ f₂) s ↔ Set.EqOn f₁ f₂ s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp) (by
  simp)) (by
  simp)

-- Set.InjOn.cancel_left, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.cancel_left.h10 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {f₁ f₂ : α → β} {g : β → γ},
        Set.InjOn g t → Set.MapsTo f₁ s t → (Set.EqOn (g ∘ f₁) (g ∘ f₂) s ↔ Set.EqOn f₁ f₂ s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp) (by
  simp)) (by
  simp)

-- Equiv.piFinsetUnion_right, hypothesis 10: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Equiv.piFinsetUnion_right.h10.der.{u_3, u_4} : ∀ {ι : Type u_4} [inst : DecidableEq ι] (α : ι → Type u_3) {s t : Finset ι},
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
          @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) t i →
            @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι))
              (@Max.max (Finset ι) (@Finset.instMax ι inst) s t) i := by
  (intros; simp_all; done)
theorem HypCheckProof.Equiv.piFinsetUnion_right.h10.{u_3, u_4} : ∀ {ι : Type u_4} [inst : DecidableEq ι] (α : ι → Type u_3) {s t : Finset ι}
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
      {i : ι} (hi : @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) t i),
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
              i (@HypCheckProof.Equiv.piFinsetUnion_right.h10.der ι inst α s t h f g i hi))))
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
            i (@HypCheckProof.Equiv.piFinsetUnion_right.h10.der ι inst α s t h f g i hi)))
        (g
          (@Subtype.mk ι
            (fun (x : ι) => @Membership.mem ι (Finset ι) (@SetLike.instMembership (Finset ι) ι (@Finset.instSetLike ι)) t x)
            i hi)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9
  exact @Equiv.piFinsetUnion_right hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 (@HypCheckProof.Equiv.piFinsetUnion_right.h10.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9)

-- List.index_of_argmax, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.index_of_argmax.h7.inst : ¬List.idxOf 0 [1] ≤ List.idxOf 1 [1] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.index_of_argmax.h7.prem0 : 1 ∈ [1] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.index_of_argmax.h7.prem1 : (fun (n : ℕ) => n + 1) 0 ≤ (fun (n : ℕ) => n + 1) 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.index_of_argmax.h7 : ¬∀ {α β : Type} [inst : LinearOrder β] {f : α → β} [inst_1 : DecidableEq α] {l : List α} {m a : α},
        a ∈ l → f m ≤ f a → List.idxOf m l ≤ List.idxOf a l := fun hc_h => HypCheckProof.List.index_of_argmax.h7.inst (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (fun (n : ℕ) => n + 1) (instDecidableEqNat) ([1]) (0) (1) HypCheckProof.List.index_of_argmax.h7.prem0 HypCheckProof.List.index_of_argmax.h7.prem1)

-- List.index_of_argmax, hypothesis 9: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.index_of_argmax.h9.gneg.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder β] {f : α → β} [inst_1 : DecidableEq α] {l : List α} {m : α},
      m ∈ List.argmax f l → ∀ {a : α}, a ∉ l → f m ≤ f a → List.idxOf m l ≤ List.idxOf a l := by
  (intros; grind)
theorem HypCheckProof.List.index_of_argmax.h9.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder β] {f : α → β} [inst_1 : DecidableEq α] {l : List α} {m : α},
      m ∈ List.argmax f l → ∀ {a : α}, f m ≤ f a → List.idxOf m l ≤ List.idxOf a l := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x10
  exact Classical.byCases (fun hc_h => @List.index_of_argmax hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_h hc_x10) (fun hc_hn => @HypCheckProof.List.index_of_argmax.h9.gneg hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_hn hc_x10)

-- List.index_of_argmax, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.index_of_argmax.h10 : ¬∀ {α β : Type} [inst : LinearOrder β] {f : α → β} [inst_1 : DecidableEq α] {l : List α} {m : α},
        m ∈ List.argmax f l → ∀ {a : α}, a ∈ l → List.idxOf m l ≤ List.idxOf a l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (fun n => n + 1 : ℕ → ℕ) (instDecidableEqNat) ([0, 1]) (1) (by
  decide) (0) (by
  decide)) (by
  decide +kernel)

-- mem_list_primes_of_dvd_prod, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.mem_list_primes_of_dvd_prod.h5 : ¬∀ {M : Type} [inst : CommMonoidWithZero M] [inst_1 : IsCancelMulZero M] [inst_2 : Subsingleton Mˣ] {p : M}
        {L : List M}, (∀ q ∈ L, Prime q) → p ∣ L.prod → p ∈ L := fun hc_h => absurd (@hc_h (ℕ) (Nat.instCommMonoidWithZero) _ _ (1) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- mem_list_primes_of_dvd_prod, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.mem_list_primes_of_dvd_prod.h7 : ¬∀ {M : Type} [inst : CommMonoidWithZero M] [inst_1 : IsCancelMulZero M] [inst_2 : Subsingleton Mˣ] {p : M},
        Prime p → ∀ {L : List M}, p ∣ L.prod → p ∈ L := fun hc_h => absurd (@hc_h (ℕ) (Nat.instCommMonoidWithZero) _ _ (2) (by
  decide) ([0]) (by
  decide)) (by
  decide +kernel)

-- mem_list_primes_of_dvd_prod, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.mem_list_primes_of_dvd_prod.h8 : ¬∀ {M : Type} [inst : CommMonoidWithZero M] [inst_1 : IsCancelMulZero M] [inst_2 : Subsingleton Mˣ] {p : M},
        Prime p → ∀ {L : List M}, (∀ q ∈ L, Prime q) → p ∈ L := fun hc_h => absurd (@hc_h (ℕ) (Nat.instCommMonoidWithZero) _ _ (2) (by
  decide) ([]) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.eq_of_mem_iff, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.eq_of_mem_iff.h8 : ¬∀ {α : Type} {r : α → α → Prop} [inst : Std.Antisymm r] [inst : Std.Irrefl r] {l₁ l₂ : List α},
        List.Pairwise r l₁ → List.Pairwise r l₂ → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ _ ([]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Ordnode.balanceR_eq_balance', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.balanceR_eq_balance'.h7 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α},
        l.Balanced →
          r.Balanced →
            l.Sized →
              ((∃ (l' : ℕ), Ordnode.Raised l.size l' ∧ Ordnode.BalancedSz l' r.size) ∨
                  ∃ (r' : ℕ), Ordnode.Raised r' r.size ∧ Ordnode.BalancedSz l.size r') →
                l.balanceR x r = l.balance' x r := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  decide) (by
  decide) (by
  (repeat' constructor) <;> done) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- List.toFinset_sort, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.toFinset_sort.h4 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r]
        [inst : DecidableEq α] {l : List α}, l.Nodup → Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (instDecidableEqBool) ([]) (by
  decide)) (by
  exact fun hc_c =>
    absurd
      (hc_c.antisymm (Bool.false : Bool) (Bool.true : Bool)
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

-- List.toFinset_sort, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.toFinset_sort.h5 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r]
        [inst : DecidableEq α] {l : List α}, l.Nodup → Std.Total r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _ (instDecidableEqNat) ([]) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.BijOn.inter, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.inter.h7 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β},
        Set.BijOn f s₂ t₂ → Set.InjOn f (s₁ ∪ s₂) → Set.BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) (fun n => n % 2 == 0 : ℕ → Bool) (by
  simp) (by
  simp)) (by
  simp)

-- Set.BijOn.inter, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.inter.h8 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β},
        Set.BijOn f s₁ t₁ → Set.InjOn f (s₁ ∪ s₂) → Set.BijOn f (s₁ ∩ s₂) (t₁ ∩ t₂) := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (fun n => n % 2 == 0 : ℕ → Bool) (by
  simp) (by
  simp)) (by
  simp)

-- Nat.cast_lt_ofNat, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.cast_lt_ofNat.h8 : ¬∀ {α : Type} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α] [inst_3 : ZeroLEOneClass α]
        [inst : CharZero α] {m : ℕ} {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddMonoidWithOne) (Nat.instPartialOrder) _ _ _ (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.ModEq.sub, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.sub.h7 : ¬∀ {n a b c d : ℕ}, c ≤ a → d ≤ b → c ≡ d [MOD n] → a - c ≡ b - d [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.sub, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.sub.h8 : ¬∀ {n a b c d : ℕ}, c ≤ a → d ≤ b → a ≡ b [MOD n] → a - c ≡ b - d [MOD n] := fun hc_h => absurd (@hc_h (0) (1) (1) (0) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.count_map_of_injective, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.count_map_of_injective.h8 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : LawfulBEq α] [inst_2 : BEq β] [inst_3 : LawfulBEq β] (l : List α) (f : α → β)
        (x : α), List.count (f x) (List.map f l) = List.count x l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instBEqOfDecidableEq) _ (instBEqOfDecidableEq) _ ([0]) (fun _ => 0 : ℕ → ℕ) (1)) (by
  decide +kernel)

-- Directed.finite_set_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Directed.finite_set_le.h6 : ¬∀ {α : Type} {r : α → α → Prop} [inst : IsTrans α r] {γ : Type} [inst : Nonempty γ] {f : γ → α} {s : Set γ},
        s.Finite → ∃ (z : γ), ∀ i ∈ s, r (f i) (f z) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ (ℕ) _ (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- List.IsChain.backwards_induction, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_induction.h5.inst : ¬(fun (b : Bool) => b = Bool.true) Bool.false := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_induction.h5.prem0 : List.IsChain (fun (x x_1 : Bool) => True) [Bool.false, Bool.true] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_induction.h5.prem1 : ∀ (lne : [Bool.false, Bool.true] ≠ []), (fun (b : Bool) => b = Bool.true) ([Bool.false, Bool.true].getLast lne) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_induction.h5.prem2 : Bool.false ∈ [Bool.false, Bool.true] := by
  decide
theorem HypCheckProof.List.IsChain.backwards_induction.h5 : ¬∀ {α : Type} {r : α → α → Prop} (p : α → Prop) (l : List α),
        List.IsChain r l → (∀ (lne : l ≠ []), p (l.getLast lne)) → ∀ i ∈ l, p i := fun hc_h => HypCheckProof.List.IsChain.backwards_induction.h5.inst (@hc_h (Bool) (fun (x x_1 : Bool) => True) (fun (b : Bool) => b = Bool.true) ([Bool.false, Bool.true]) HypCheckProof.List.IsChain.backwards_induction.h5.prem0 HypCheckProof.List.IsChain.backwards_induction.h5.prem1 (Bool.false) HypCheckProof.List.IsChain.backwards_induction.h5.prem2)

-- List.IsChain.backwards_induction, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.backwards_induction.h6 : ¬∀ {α : Type} {r : α → α → Prop} (p : α → Prop) (l : List α),
        List.IsChain r l → (∀ ⦃x y : α⦄, r x y → p y → p x) → ∀ i ∈ l, p i := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun n => n = 0 : ℕ → Prop) ([1]) (by
  decide) (by
  omega) (1) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.backwards_induction, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_induction.h8.inst : ¬(fun (n : ℕ) => n = 0) 1 := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_induction.h8.prem0 : List.IsChain (fun (a b : ℕ) => a < b) [] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_induction.h8.prem1 : ∀ ⦃x y : ℕ⦄, x < y → y = 0 → (fun (n : ℕ) => n = 0) x := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.backwards_induction.h8.prem2 : ∀ (lne : [] ≠ []), (fun (n : ℕ) => n = 0) ([].getLast lne) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.IsChain.backwards_induction.h8 : ¬∀ {α : Type} {r : α → α → Prop} (p : α → Prop) (l : List α),
        List.IsChain r l → (∀ ⦃x y : α⦄, r x y → p y → p x) → (∀ (lne : l ≠ []), p (l.getLast lne)) → ∀ (i : α), p i := fun hc_h => HypCheckProof.List.IsChain.backwards_induction.h8.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (fun (n : ℕ) => n = 0) ([]) HypCheckProof.List.IsChain.backwards_induction.h8.prem0 HypCheckProof.List.IsChain.backwards_induction.h8.prem1 HypCheckProof.List.IsChain.backwards_induction.h8.prem2 (1))

-- Nat.ofNat_lt_cast, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofNat_lt_cast.h8 : ¬∀ {α : Type} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α] [inst_3 : ZeroLEOneClass α]
        [inst : CharZero α] {m : ℕ} {n : ℕ}, m.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddMonoidWithOne) (Nat.instPartialOrder) _ _ _ (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.cast_le_ofNat, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.cast_le_ofNat.h8 : ¬∀ {α : Type} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α] [inst_3 : ZeroLEOneClass α]
        [inst : CharZero α] {m : ℕ} {n : ℕ}, n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddMonoidWithOne) (Nat.instPartialOrder) _ _ _ (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.swap_mem_antidiagonal, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.swap_mem_antidiagonal.h3 : ¬∀ {α : Type} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] {s t : Set α} {hs : s.IsPWO} {ht : t.IsPWO} {a : α}
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

-- Int.lt_zpow_iff_log_lt, hypothesis 6: necessary
/- FAILED: 4:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 46:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 4:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 46:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 2:74: failed to synthesize instance of type class
  Semifield ℕ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 51:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 2:74: failed to synthesize instance of type class
  Semifield ℕ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 51:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.lt_zpow_iff_log_lt.h6 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ} {x : ℤ} {r : R}, 0 < r → (r < ↑b ^ x ↔ Int.log b r < x) := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (0) (0) (1 / 2) (by
  decide)) (by
  decide +kernel)
-/

-- Int.lt_zpow_iff_log_lt, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.lt_zpow_iff_log_lt.h9 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ}, 1 < b → ∀ {x : ℤ} {r : R}, r < ↑b ^ x ↔ Int.log b r < x := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (2) (by
  decide) (0) (0)) (by
  decide +kernel)

-- Int.log_mono_right, hypothesis 8: necessary
/- FAILED: 4:2: Tactic `decide` failed to reduce
  @decide (0 ≤ 1 / 2) (Rat.instDecidableLe 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, `Int.decLt`, `Int.decNonneg`, and `Rat.instDecidableLe`, reduction got stuck at
  match 0 - ((1 / 2).num + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 21:2: Tactic `decide` failed to reduce
  @decide (0 ≤ 1 / 2) (Rat.instDecidableLe 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, `Int.decLt`, `Int.decNonneg`, and `Rat.instDecidableLe`, reduction got stuck at
  match 0 - ((1 / 2).num + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 4:2: Tactic `decide` failed to reduce
  @decide (0 ≤ 1 / 2) (Rat.instDecidableLe 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, `Int.decLt`, `Int.decNonneg`, and `Rat.instDecidableLe`, reduction got stuck at
  match 0 - ((1 / 2).num + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 21:2: Tactic `decide` failed to reduce
  @decide (0 ≤ 1 / 2) (Rat.instDecidableLe 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, `Int.decLt`, `Int.decNonneg`, and `Rat.instDecidableLe`, reduction got stuck at
  match 0 - ((1 / 2).num + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 2:52: failed to synthesize instance of type class
  Semifield ℕ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 24:2: Tactic `decide` failed to reduce
  @decide (0 ≤ 1 / 2) (Rat.instDecidableLe 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, `Int.decLt`, `Int.decNonneg`, and `Rat.instDecidableLe`, reduction got stuck at
  match 0 - ((1 / 2).num + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 2:52: failed to synthesize instance of type class
  Semifield ℕ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 24:2: Tactic `decide` failed to reduce
  @decide (0 ≤ 1 / 2) (Rat.instDecidableLe 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, `Int.decLt`, `Int.decNonneg`, and `Rat.instDecidableLe`, reduction got stuck at
  match 0 - ((1 / 2).num + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.log_mono_right.h8 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ} {r₁ r₂ : R}, r₁ ≤ r₂ → Int.log b r₁ ≤ Int.log b r₂ := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (2) (0) (1 / 2) (by
  decide)) (by
  decide +kernel)
-/

-- List.sublist_dlookup, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.sublist_dlookup.h8.inst : @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) ∉
      @List.dlookup Nat (fun (a : Nat) => Nat) instDecidableEqNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.sublist_dlookup.h8.prem0 : @List.NodupKeys Nat (fun (a : Nat) => Nat) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.sublist_dlookup.h8.prem1 : @Membership.mem ((fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Option ((fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@Option.instMembership ((fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@List.dlookup Nat (fun (a : Nat) => Nat) instDecidableEqNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
          (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@List.nil (@Sigma Nat fun (a : Nat) => Nat))))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.sublist_dlookup.h8 : Not
      (∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {l₁ l₂ : List (@Sigma α β)} {a : α} {b : β a},
        @List.NodupKeys α β l₂ →
          @Membership.mem (β a) (Option (β a)) (@Option.instMembership (β a)) (@List.dlookup α β inst a l₁) b →
            @Membership.mem (β a) (Option (β a)) (@Option.instMembership (β a)) (@List.dlookup α β inst a l₂) b) := fun hc_h => HypCheckProof.List.sublist_dlookup.h8.inst (@hc_h (Nat) (fun (a : Nat) => Nat) (instDecidableEqNat) (@List.cons (@Sigma Nat fun (a : Nat) => Nat)
      (@Sigma.mk Nat (fun (a : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (a : Nat) => Nat))) (@List.nil (@Sigma Nat fun (a : Nat) => Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.List.sublist_dlookup.h8.prem0 HypCheckProof.List.sublist_dlookup.h8.prem1)

-- List.sublist_dlookup, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sublist_dlookup.h9 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {l₁ l₂ : List (Sigma β)} {a : α} {b : β a},
        l₂.NodupKeys → l₁.Sublist l₂ → b ∈ List.dlookup a l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) ([]) ([]) (0) (0) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- List.SortedLT.getElem_lt_getElem_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.getElem_lt_getElem_of_lt.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α] ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, i < j → l[i] < l[j] := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) ([1, 0]) (Nat.instPreorder) (0) (1) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- List.SortedLT.getElem_lt_getElem_of_lt, hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.SortedLT.getElem_lt_getElem_of_lt.h6.der.{u_1} : ∀ {α : Type u_1} {l : List α} [inst : Preorder α], l.SortedLT → ∀ ⦃i j : ℕ⦄ ⦃hj : j < l.length⦄, i < j → i < l.length := by
  (intros; lia)
theorem HypCheckProof.List.SortedLT.getElem_lt_getElem_of_lt.h6.{u_1} : ∀ {α : Type u_1} {l : List α} [inst : Preorder α] (a : l.SortedLT) ⦃i j : ℕ⦄ ⦃hj : j < l.length⦄ (a_1 : i < j),
      l[i] < l[j] := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7
  exact @List.SortedLT.getElem_lt_getElem_of_lt hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.List.SortedLT.getElem_lt_getElem_of_lt.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7) hc_x6 hc_x7

-- List.SortedLT.getElem_lt_getElem_of_lt, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.getElem_lt_getElem_of_lt.h7 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedLT → ∀ ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄, i < j → j < l.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) (Nat.instPreorder) (by
  decide) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.SortedLT.getElem_lt_getElem_of_lt, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.getElem_lt_getElem_of_lt.h8 : ¬∀ {α : Type} {l : List α} [inst : Preorder α],
        l.SortedLT → ∀ ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, l[i] < l[j] := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) ([0]) (Nat.instPreorder) hc_k0 (0) (0) hc_k1 hc_k2) (by
  decide +kernel)

-- List.SortedLE.getElem_le_getElem_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLE.getElem_le_getElem_of_le.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α] ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, i ≤ j → l[i] ≤ l[j] := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) ([1, 0]) (Nat.instPreorder) (0) (1) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- List.SortedLE.getElem_le_getElem_of_le, hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.SortedLE.getElem_le_getElem_of_le.h6.der.{u_1} : ∀ {α : Type u_1} {l : List α} [inst : Preorder α], l.SortedLE → ∀ ⦃i j : ℕ⦄ ⦃hj : j < l.length⦄, i ≤ j → i < l.length := by
  (intros; lia)
theorem HypCheckProof.List.SortedLE.getElem_le_getElem_of_le.h6.{u_1} : ∀ {α : Type u_1} {l : List α} [inst : Preorder α] (a : l.SortedLE) ⦃i j : ℕ⦄ ⦃hj : j < l.length⦄ (a_1 : i ≤ j),
      l[i] ≤ l[j] := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7
  exact @List.SortedLE.getElem_le_getElem_of_le hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.List.SortedLE.getElem_le_getElem_of_le.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7) hc_x6 hc_x7

-- List.SortedLE.getElem_le_getElem_of_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLE.getElem_le_getElem_of_le.h7 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedLE → ∀ ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄, i ≤ j → j < l.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) (Nat.instPreorder) (by
  decide) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.SortedLE.getElem_le_getElem_of_le, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLE.getElem_le_getElem_of_le.h8 : ¬∀ {α : Type} {l : List α} [inst : Preorder α],
        l.SortedLE → ∀ ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, l[i] ≤ l[j] := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) ([0, 1]) (Nat.instPreorder) hc_k0 (1) (0) hc_k1 hc_k2) (by
  decide +kernel)

-- List.Pairwise.merge, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.merge.h3 : ¬∀ {α : Type} {r : α → α → Prop} [inst : DecidableRel r] [inst_1 : IsTrans α r] {l l' : List α},
        List.Pairwise r l → List.Pairwise r l' → List.Pairwise r (l.merge l' fun (x1 x2 : α) => Decidable.decide (r x1 x2)) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ ([0]) ([0]) (by
  decide) (by
  decide)) (by
  simp)

-- Set.EqOn.prodMap, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.prodMap.h10 : ¬∀ {α β γ δ : Type} {s : Set α} {t : Set β} {f f' : α → γ} {g g' : β → δ},
        Set.EqOn g g' t → Set.EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.EqOn.prodMap, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.prodMap.h11 : ¬∀ {α β γ δ : Type} {s : Set α} {t : Set β} {f f' : α → γ} {g g' : β → δ},
        Set.EqOn f f' s → Set.EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- MvQPF.liftR_map_last, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.MvQPF.liftR_map_last.h3.gneg.{u} : ∀ {n : ℕ} {F : TypeVec.{u} (n + 1) → Type u} [q : MvQPF F],
      ¬LawfulMvFunctor F →
        ∀ {α : TypeVec.{u} n} {ι ι' : Type u} (R : ι' → ι' → Prop) (x : F (α ::: ι)) (f g : ι → ι'),
          (∀ (x : ι), R (f x) (g x)) →
            MvFunctor.LiftR' (α.RelLast' R) (MvFunctor.map (TypeVec.id ::: f) x) (MvFunctor.map (TypeVec.id ::: g) x) := by
  (intros; solve_by_elim)
theorem HypCheckProof.MvQPF.liftR_map_last.h3.{u} : ∀ {n : ℕ} {F : TypeVec.{u} (n + 1) → Type u} [q : MvQPF F] {α : TypeVec.{u} n} {ι ι' : Type u} (R : ι' → ι' → Prop)
      (x : F (α ::: ι)) (f g : ι → ι'),
      (∀ (x : ι), R (f x) (g x)) →
        MvFunctor.LiftR' (α.RelLast' R) (MvFunctor.map (TypeVec.id ::: f) x) (MvFunctor.map (TypeVec.id ::: g) x) := by
  intro hc_x0 hc_x1 hc_x2 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11
  exact Classical.byCases (fun hc_h => @MvQPF.liftR_map_last hc_x0 hc_x1 hc_x2 hc_h hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11) (fun hc_hn => @HypCheckProof.MvQPF.liftR_map_last.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11)
set_option maxHeartbeats 1000 in
theorem HypCheckProof.MvQPF.liftR_map_last.h3.derivable.{u} : ∀ {n : ℕ} {F : TypeVec.{u} (n + 1) → Type u} [q : MvQPF F] {α : TypeVec.{u} n} {ι ι' : Type u} (R : ι' → ι' → Prop)
      (x : F (α ::: ι)) (f g : ι → ι'), (∀ (x : ι), R (f x) (g x)) → LawfulMvFunctor F := by
  (intros; infer_instance)

-- List.Forall₂.get, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Forall₂.get.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {x : List α} {y : List β} ⦃i : ℕ⦄ (hx : i < x.length) (hy : i < y.length),
        R (x.get (⟨i, hx⟩ : Fin x.length)) (y.get (⟨i, hy⟩ : Fin y.length)) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) ([0]) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- List.Perm.insertIdx_of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.insertIdx_of_le.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} {m n : ℕ},
        n ≤ l₂.length → ∀ (a : α), l₁.Perm l₂ → (l₁.insertIdx m a).Perm (l₂.insertIdx n a) := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (1) (0) (by
  decide) (0) (by
  decide)) (by
  decide +kernel)

-- List.Perm.insertIdx_of_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.insertIdx_of_le.h6 : ¬∀ {α : Type} {l₁ l₂ : List α} {m n : ℕ},
        m ≤ l₁.length → ∀ (a : α), l₁.Perm l₂ → (l₁.insertIdx m a).Perm (l₂.insertIdx n a) := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (0) (1) (by
  decide) (0) (by
  decide)) (by
  decide +kernel)

-- List.Perm.insertIdx_of_le, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.insertIdx_of_le.h8 : ¬∀ {α : Type} {l₁ l₂ : List α} {m n : ℕ},
        m ≤ l₁.length → n ≤ l₂.length → ∀ (a : α), (l₁.insertIdx m a).Perm (l₂.insertIdx n a) := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (0) (0) (by
  decide) (by
  decide) (0)) (by
  decide +kernel)

-- Int.zpow_log_le_self, hypothesis 7: necessary
/- FAILED: 4:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 43:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 4:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 43:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 2:59: failed to synthesize instance of type class
  Semifield ℕ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 47:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯ | 2:59: failed to synthesize instance of type class
  Semifield ℕ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 47:2: Tactic `decide` failed to reduce
  @decide (0 < 1 / 2) (Rat.instDecidableLt 0 (1 / 2))
to `true` or `false`.

After unfolding the instances `decEq`, `instDecidableEqBool`, `instDecidableEqNat`, `Bool.decEq`, `isFalse`, `isTrue`, `Int.decEq`, `Int.decLt`, `Int.decNonneg`, `Int.instDecidableEq`, `Nat.decEq`, and `Rat.instDecidableLt`, reduction got stuck at
  match (1 / 2).num - (0 + 1) with
  | Int.ofNat m => isTrue ⋯
  | Int.negSucc i => isFalse ⋯
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.zpow_log_le_self.h7 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ} {r : R}, 0 < r → ↑b ^ Int.log b r ≤ r := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (0) (1 / 2) (by
  decide)) (by
  decide +kernel)
-/

-- Int.zpow_log_le_self, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.zpow_log_le_self.h8 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        {b : ℕ} {r : R}, 1 < b → ↑b ^ Int.log b r ≤ r := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (2) (0) (by
  decide)) (by
  decide +kernel)

-- Flag.mem_rangeFin, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Flag.mem_rangeFin.h6.inst : ¬(fun (a : Fin (0 + 1)) => Bool.true) 0 = ⊥ := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Flag.mem_rangeFin.h6.prem0 : (fun (a : Fin (0 + 1)) => Bool.true) (Fin.last 0) = ⊤ := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Flag.mem_rangeFin.h6.prem1 : ∀ (k : Fin 0), (fun (a : Fin (0 + 1)) => Bool.true) k.castSucc ⩿ (fun (a : Fin (0 + 1)) => Bool.true) k.succ := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Flag.mem_rangeFin.h6 : ¬∀ {α : Type} [inst : PartialOrder α] [inst_1 : BoundedOrder α] {n : ℕ} {f : Fin (n + 1) → α} {x : α}
        {hlast : f (Fin.last n) = ⊤} {hcovBy : ∀ (k : Fin n), f k.castSucc ⩿ f k.succ}, f 0 = ⊥ := fun hc_h => HypCheckProof.Flag.mem_rangeFin.h6.inst (@hc_h (Bool) (Bool.instPartialOrder) (Bool.instBoundedOrder) (0) (fun (a : Fin (0 + 1)) => Bool.true) (Bool.false) HypCheckProof.Flag.mem_rangeFin.h6.prem0 HypCheckProof.Flag.mem_rangeFin.h6.prem1)

-- Flag.mem_rangeFin, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Flag.mem_rangeFin.h7.inst : ¬(fun (a : Fin (0 + 1)) => Bool.false) (Fin.last 0) = ⊤ := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Flag.mem_rangeFin.h7.prem0 : (fun (a : Fin (0 + 1)) => Bool.false) 0 = ⊥ := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Flag.mem_rangeFin.h7.prem1 : ∀ (k : Fin 0), (fun (a : Fin (0 + 1)) => Bool.false) k.castSucc ⩿ (fun (a : Fin (0 + 1)) => Bool.false) k.succ := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Flag.mem_rangeFin.h7 : ¬∀ {α : Type} [inst : PartialOrder α] [inst_1 : BoundedOrder α] {n : ℕ} {f : Fin (n + 1) → α} {x : α} {h0 : f 0 = ⊥}
        {hcovBy : ∀ (k : Fin n), f k.castSucc ⩿ f k.succ}, f (Fin.last n) = ⊤ := fun hc_h => HypCheckProof.Flag.mem_rangeFin.h7.inst (@hc_h (Bool) (Bool.instPartialOrder) (Bool.instBoundedOrder) (0) (fun (a : Fin (0 + 1)) => Bool.false) (Bool.false) HypCheckProof.Flag.mem_rangeFin.h7.prem0 HypCheckProof.Flag.mem_rangeFin.h7.prem1)

-- List.orderedInsert_erase, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.orderedInsert_erase.h7 : ¬∀ {α : Type} {r : α → α → Prop} [inst : DecidableRel r] [inst_1 : DecidableEq α] [inst_2 : Std.Antisymm r] (x : α)
        (xs : List α), List.Pairwise r xs → List.orderedInsert r x (xs.erase x) = xs := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) (instDecidableEqNat) _ (0) ([]) (by
  decide)) (by
  decide +kernel)

-- List.orderedInsert_erase, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.orderedInsert_erase.h8 : ¬∀ {α : Type} {r : α → α → Prop} [inst : DecidableRel r] [inst_1 : DecidableEq α] [inst_2 : Std.Antisymm r] (x : α)
        (xs : List α), x ∈ xs → List.orderedInsert r x (xs.erase x) = xs := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) (instDecidableEqNat) _ (0) ([1, 0]) (by
  decide)) (by
  decide +kernel)

-- Ordnode.insertWith.valid, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.insertWith.valid.h8 : ¬∀ {α : Type} [inst : Preorder α] [inst_1 : Std.Total fun (x1 x2 : α) => x1 ≤ x2] [inst_2 : DecidableLE α] (f : α → α)
        (x : α), (∀ (y : α), x ≤ y ∧ y ≤ x → x ≤ f y ∧ f y ≤ x) → ∀ {t : Ordnode α}, (Ordnode.insertWith f x t).Valid := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) _ (Nat.decLe) (fun _ => 0 : ℕ → ℕ) (0) (by
  simp) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil)) (by
  nofun)

-- Set.enumerate_inj, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.enumerate_inj.h6 : ¬∀ {α : Type} (sel : Set α → Option α) {n₁ n₂ : ℕ} {a : α} {s : Set α},
        Set.enumerate sel s n₁ = Option.some a → Set.enumerate sel s n₂ = Option.some a → n₁ = n₂ := fun hc_h => absurd (@hc_h (ℕ) (fun (a : Set ℕ) => Option.some 0) (0) (1) (0) ({n : ℕ | n = 0}) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.eq_of_head_mem_of_getLast_mem_of_infix, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.eq_of_head_mem_of_getLast_mem_of_infix.h3 : ¬∀ {α : Type} {l₁ l₂ : List α} {hne : l₂ ≠ []}, l₂.head hne ∈ l₁ → l₂.getLast hne ∈ l₁ → l₂.Nodup → l₁ = l₂ := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (ℕ) ([0, 1]) ([0]) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- List.Nodup.eq_of_head_mem_of_getLast_mem_of_infix, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.eq_of_head_mem_of_getLast_mem_of_infix.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <:+: l₂ → l₂.Nodup → l₂ ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.eq_of_head_mem_of_getLast_mem_of_infix, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.eq_of_head_mem_of_getLast_mem_of_infix.h5 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <:+: l₂ → ∀ {hne : l₂ ≠ []}, l₂.getLast hne ∈ l₁ → l₂.Nodup → l₁ = l₂ := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (ℕ) ([0]) ([1, 0]) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- List.Nodup.eq_of_head_mem_of_getLast_mem_of_infix, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.eq_of_head_mem_of_getLast_mem_of_infix.h6 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <:+: l₂ → ∀ {hne : l₂ ≠ []}, l₂.head hne ∈ l₁ → l₂.Nodup → l₁ = l₂ := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (ℕ) ([0]) ([0, 1]) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- List.Nodup.eq_of_head_mem_of_getLast_mem_of_infix, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.eq_of_head_mem_of_getLast_mem_of_infix.h7 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <:+: l₂ → ∀ {hne : l₂ ≠ []}, l₂.head hne ∈ l₁ → l₂.getLast hne ∈ l₁ → l₁ = l₂ := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 hc_k3 => @hc_h (ℕ) ([0]) ([0, 0]) hc_k0 hc_k1 hc_k2 hc_k3) (by
  decide +kernel)

-- Int.div_lt_div_iff_of_dvd_of_neg_of_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_div_iff_of_dvd_of_neg_of_neg.h4 : ¬∀ {a b c d : ℤ}, d < 0 → b ∣ a → d ∣ c → (a / b < c / d ↔ d * a < c * b) := fun hc_h => absurd (@hc_h (0) (0) (-1) (-1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_lt_div_iff_of_dvd_of_neg_of_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_div_iff_of_dvd_of_neg_of_neg.h5 : ¬∀ {a b c d : ℤ}, b < 0 → b ∣ a → d ∣ c → (a / b < c / d ↔ d * a < c * b) := fun hc_h => absurd (@hc_h (1) (-1) (0) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_lt_div_iff_of_dvd_of_neg_of_neg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_div_iff_of_dvd_of_neg_of_neg.h6 : ¬∀ {a b c d : ℤ}, b < 0 → d < 0 → d ∣ c → (a / b < c / d ↔ d * a < c * b) := fun hc_h => absurd (@hc_h (1) (-2) (0) (-1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.ofNat_pos', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofNat_pos'.h3 : Not
      (∀ {α : Type} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α]
        [inst_2 :
          @ZeroLEOneClass α
            (@AddZero.toZero α
              (@AddZeroClass.toAddZero α (@AddMonoid.toAddZeroClass α (@AddMonoidWithOne.toAddMonoid α inst))))
            (@AddMonoidWithOne.toOne α inst) (@Preorder.toLE α (@PartialOrder.toPreorder α inst_1))]
        [inst_3 :
          @NeZero α
            (@AddZero.toZero α
              (@AddZeroClass.toAddZero α (@AddMonoid.toAddZeroClass α (@AddMonoidWithOne.toAddMonoid α inst))))
            (@OfNat.ofNat α (nat_lit 1) (@One.toOfNat1 α (@AddMonoidWithOne.toOne α inst)))]
        {n : Nat} [inst_4 : n.AtLeastTwo],
        @LT.lt α (@Preorder.toLT α (@PartialOrder.toPreorder α inst_1))
          (@OfNat.ofNat α (nat_lit 0)
            (@Zero.toOfNat0 α
              (@AddZero.toZero α
                (@AddZeroClass.toAddZero α (@AddMonoid.toAddZeroClass α (@AddMonoidWithOne.toAddMonoid α inst))))))
          (@OfNat.ofNat α n (@instOfNatAtLeastTwo α n (@AddMonoidWithOne.toNatCast α inst) inst_4))) := fun hc_h => absurd (@hc_h (Bool) (@AddGroupWithOne.toAddMonoidWithOne Bool (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool))) (Bool.instPartialOrder) (@ZeroLEOneClass.mk (Bool) (@AddZero.toZero Bool
      (@AddZeroClass.toAddZero Bool
        (@AddMonoid.toAddZeroClass Bool
          (@AddMonoidWithOne.toAddMonoid Bool
            (@AddGroupWithOne.toAddMonoidWithOne Bool
              (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool))))))) (@AddMonoidWithOne.toOne Bool
      (@AddGroupWithOne.toAddMonoidWithOne Bool
        (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool)))) (@Preorder.toLE Bool (@PartialOrder.toPreorder Bool Bool.instPartialOrder)) (by (try dsimp only);   decide)) _ (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) _) (by
  decide +kernel)

-- Nat.ofNat_pos', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofNat_pos'.h7 : Not
      (∀ {α : Type} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α]
        [inst_2 :
          @AddLeftMono α (@AddSemigroup.toAdd α (@AddMonoid.toAddSemigroup α (@AddMonoidWithOne.toAddMonoid α inst)))
            (@Preorder.toLE α (@PartialOrder.toPreorder α inst_1))]
        [inst_3 :
          @ZeroLEOneClass α
            (@AddZero.toZero α
              (@AddZeroClass.toAddZero α (@AddMonoid.toAddZeroClass α (@AddMonoidWithOne.toAddMonoid α inst))))
            (@AddMonoidWithOne.toOne α inst) (@Preorder.toLE α (@PartialOrder.toPreorder α inst_1))]
        [inst :
          @NeZero α
            (@AddZero.toZero α
              (@AddZeroClass.toAddZero α (@AddMonoid.toAddZeroClass α (@AddMonoidWithOne.toAddMonoid α inst))))
            (@OfNat.ofNat α (nat_lit 1) (@One.toOfNat1 α (@AddMonoidWithOne.toOne α inst)))]
        {n : Nat}, n.AtLeastTwo) := fun hc_h => absurd (@hc_h (Nat) (Nat.instAddMonoidWithOne) (Nat.instPartialOrder) _ _ _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Matrix.submatrix_ofNat, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.submatrix_ofNat.h10 : ¬∀ {l m α : Type} [inst : Zero α] [inst : NatCast α] [inst : DecidableEq m] [inst : DecidableEq l] (e : l → m),
        Function.Injective e → ∀ (k : ℕ), k.AtLeastTwo := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (instNatCastNat) (instDecidableEqNat) (instDecidableEqBool) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.EqOn.piecewise_ite, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.piecewise_ite.h9 : ¬∀ {α β : Type} (s : Set α) [inst : (j : α) → Decidable (j ∈ s)] {f f' g : α → β} {t t' : Set α},
        Set.EqOn f' g t' → Set.EqOn (s.piecewise f f') g (s.ite t t') := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun (j : ℕ) => Set.decidableOfPred j fun (n : ℕ) => n = 0) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  (simp <;> decide))

-- Int.div_lt_div_iff_of_dvd_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_div_iff_of_dvd_of_pos.h4 : ¬∀ {a b c d : ℤ}, 0 < d → b ∣ a → d ∣ c → (a / b < c / d ↔ d * a < c * b) := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_lt_div_iff_of_dvd_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_div_iff_of_dvd_of_pos.h5 : ¬∀ {a b c d : ℤ}, 0 < b → b ∣ a → d ∣ c → (a / b < c / d ↔ d * a < c * b) := fun hc_h => absurd (@hc_h (-1) (1) (0) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_lt_div_iff_of_dvd_of_pos, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_div_iff_of_dvd_of_pos.h7 : ¬∀ {a b c d : ℤ}, 0 < b → 0 < d → b ∣ a → (a / b < c / d ↔ d * a < c * b) := fun hc_h => absurd (@hc_h (0) (1) (1) (2) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- EReal.sub_lt_sub_of_le_of_gt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.sub_lt_sub_of_le_of_gt.h5 : ¬∀ {x y z t : EReal}, x ≤ y → x ≠ ⊤ → y ≠ ⊥ → x - t < y - z := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (by
  rfl) (by
  decide) (by
  decide)) (by
  simp)

-- Int.ModEq.of_div, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.of_div.h4 : ¬∀ {m a b c : ℤ}, c ∣ a → c ∣ b → c ∣ m → a ≡ b [ZMOD m] := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.of_div, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.of_div.h5 : ¬∀ {m a b c : ℤ}, a / c ≡ b / c [ZMOD m / c] → c ∣ b → c ∣ m → a ≡ b [ZMOD m] := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.of_div, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.of_div.h6 : ¬∀ {m a b c : ℤ}, a / c ≡ b / c [ZMOD m / c] → c ∣ a → c ∣ m → a ≡ b [ZMOD m] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_le_div_iff_of_dvd_of_pos_of_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_le_div_iff_of_dvd_of_pos_of_neg.h4 : ¬∀ {a b c d : ℤ}, d < 0 → b ∣ a → d ∣ c → (a / b ≤ c / d ↔ c * b ≤ d * a) := fun hc_h => absurd (@hc_h (0) (0) (1) (-1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_le_div_iff_of_dvd_of_pos_of_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_le_div_iff_of_dvd_of_pos_of_neg.h5 : ¬∀ {a b c d : ℤ}, 0 < b → b ∣ a → d ∣ c → (a / b ≤ c / d ↔ c * b ≤ d * a) := fun hc_h => absurd (@hc_h (1) (1) (0) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_le_div_iff_of_dvd_of_pos_of_neg, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_le_div_iff_of_dvd_of_pos_of_neg.h6 : ¬∀ {a b c d : ℤ}, 0 < b → d < 0 → d ∣ c → (a / b ≤ c / d ↔ c * b ≤ d * a) := fun hc_h => absurd (@hc_h (1) (2) (0) (-1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_le_div_iff_of_dvd_of_pos_of_neg, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_le_div_iff_of_dvd_of_pos_of_neg.h7 : ¬∀ {a b c d : ℤ}, 0 < b → d < 0 → b ∣ a → (a / b ≤ c / d ↔ c * b ≤ d * a) := fun hc_h => absurd (@hc_h (0) (1) (1) (-2) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- EReal.add_lt_add_of_lt_of_le', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_lt_add_of_lt_of_le'.h4 : ¬∀ {x y z t : EReal}, z ≤ t → t ≠ ⊥ → (t = ⊤ → z = ⊤ → x = ⊥) → x + z < y + t := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (by
  rfl) (by
  decide) (by
  decide)) (by
  simp)

-- Int.div_le_div_iff_of_dvd_of_neg_of_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_le_div_iff_of_dvd_of_neg_of_neg.h4 : ¬∀ {a b c d : ℤ}, d < 0 → b ∣ a → d ∣ c → (a / b ≤ c / d ↔ d * a ≤ c * b) := fun hc_h => absurd (@hc_h (0) (0) (1) (-1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_le_div_iff_of_dvd_of_neg_of_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_le_div_iff_of_dvd_of_neg_of_neg.h5 : ¬∀ {a b c d : ℤ}, b < 0 → b ∣ a → d ∣ c → (a / b ≤ c / d ↔ d * a ≤ c * b) := fun hc_h => absurd (@hc_h (0) (-1) (1) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.div_le_div_iff_of_dvd_of_neg_of_neg, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_le_div_iff_of_dvd_of_neg_of_neg.h7 : ¬∀ {a b c d : ℤ}, b < 0 → d < 0 → b ∣ a → (a / b ≤ c / d ↔ d * a ≤ c * b) := fun hc_h => absurd (@hc_h (0) (-1) (1) (-2) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Fin.find_congr', hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.find_congr'.h5.der : ∀ {n : Nat} {p q : Fin n → Prop} [inst : @DecidablePred (Fin n) p] [inst : @DecidablePred (Fin n) q]
      {hq : ∃ (i : Fin n), q i}, (∀ {i : Fin n}, Iff (p i) (q i)) → ∃ (i : Fin n), p i := by
  (intros; simp_all; done)
theorem HypCheckProof.Fin.find_congr'.h5 : ∀ {n : Nat} {p q : Fin n → Prop} [inst : @DecidablePred (Fin n) p] [inst_1 : @DecidablePred (Fin n) q]
      {hq : ∃ (i : Fin n), q i} (hpq : ∀ {i : Fin n}, Iff (p i) (q i)),
      @Eq (Fin n) (@Fin.find n p inst (@HypCheckProof.Fin.find_congr'.h5.der n p q inst inst_1 hq hpq))
        (@Fin.find n q inst_1 hq) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Fin.find_congr' hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Fin.find_congr'.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6) hc_x5 hc_x6

-- Fin.find_congr', hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.find_congr'.h6.der : ∀ {n : Nat} {p q : Fin n → Prop} [inst : @DecidablePred (Fin n) p] [inst : @DecidablePred (Fin n) q]
      {hp : ∃ (i : Fin n), p i}, (∀ {i : Fin n}, Iff (p i) (q i)) → ∃ (i : Fin n), q i := by
  (intros; simp_all; done)
theorem HypCheckProof.Fin.find_congr'.h6 : ∀ {n : Nat} {p q : Fin n → Prop} [inst : @DecidablePred (Fin n) p] [inst_1 : @DecidablePred (Fin n) q]
      {hp : ∃ (i : Fin n), p i} (hpq : ∀ {i : Fin n}, Iff (p i) (q i)),
      @Eq (Fin n) (@Fin.find n p inst hp)
        (@Fin.find n q inst_1 (@HypCheckProof.Fin.find_congr'.h6.der n p q inst inst_1 hp hpq)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Fin.find_congr' hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Fin.find_congr'.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6) hc_x6

-- Fin.find_mono, hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.find_mono.h6.der : ∀ {n : Nat} {p q : Fin n → Prop} [inst : @DecidablePred (Fin n) p] [inst : @DecidablePred (Fin n) q],
      (∀ (i : Fin n), q i → p i) → ∀ {hq : ∃ (i : Fin n), q i}, ∃ (i : Fin n), p i := by
  (intros; grind)
theorem HypCheckProof.Fin.find_mono.h6 : ∀ {n : Nat} {p q : Fin n → Prop} [inst : @DecidablePred (Fin n) p] [inst_1 : @DecidablePred (Fin n) q]
      (h : ∀ (i : Fin n), q i → p i) {hq : ∃ (i : Fin n), q i},
      @LE.le (Fin n) (@instLEFin n) (@Fin.find n p inst (@HypCheckProof.Fin.find_mono.h6.der n p q inst inst_1 h hq))
        (@Fin.find n q inst_1 hq) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Fin.find_mono hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Fin.find_mono.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6) hc_x6

-- Set.disjoint_of_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.disjoint_of_subset.h5 : ¬∀ {α : Type} {s₁ s₂ t₁ t₂ : Set α}, t₁ ⊆ t₂ → Disjoint s₂ t₂ → Disjoint s₁ t₁ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl) (by
  simp)) (by
  simp)

-- Set.disjoint_of_subset, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.disjoint_of_subset.h6 : ¬∀ {α : Type} {s₁ s₂ t₁ t₂ : Set α}, s₁ ⊆ s₂ → Disjoint s₂ t₂ → Disjoint s₁ t₁ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  rfl) (by
  simp)) (by
  simp)

-- Set.disjoint_of_subset, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.disjoint_of_subset.h7 : ¬∀ {α : Type} {s₁ s₂ t₁ t₂ : Set α}, s₁ ⊆ s₂ → t₁ ⊆ t₂ → Disjoint s₁ t₁ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl) (by
  rfl)) (by
  simp)

-- List.SortedLT.getElem_lt_getElem_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.getElem_lt_getElem_iff.h3 : ¬∀ {α : Type} {l : List α} [inst : LinearOrder α] {i j : ℕ} {hi : i < l.length} {hj : j < l.length}, l[i] < l[j] ↔ i < j := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) ([1, 0]) (Nat.instLinearOrder) (0) (1) hc_k0 hc_k1) (by
  decide +kernel)

-- List.SortedLT.getElem_lt_getElem_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.getElem_lt_getElem_iff.h6 : ¬∀ {α : Type} {l : List α} [inst : LinearOrder α], l.SortedLT → ∀ {i j : ℕ} {hj : j < l.length}, i < l.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) (Nat.instLinearOrder) (by
  decide) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.SortedLT.getElem_lt_getElem_iff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.getElem_lt_getElem_iff.h7 : ¬∀ {α : Type} {l : List α} [inst : LinearOrder α], l.SortedLT → ∀ {i j : ℕ} {hi : i < l.length}, j < l.length := fun hc_h => absurd (@hc_h (ℕ) ([0]) (Nat.instLinearOrder) (by
  decide) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Set.infinite_of_injOn_mapsTo, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infinite_of_injOn_mapsTo.h7 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.InjOn f s → Set.MapsTo f s t → t.Infinite := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (by
  simp) (by
  simp)) (by
  simp)

-- Nat.chineseRemainder_modEq_unique, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.chineseRemainder_modEq_unique.h2 : ¬∀ {m n a b z : ℕ}, z ≡ a [MOD n] → z ≡ b [MOD m] → n.Coprime m := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.chineseRemainder_modEq_unique, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.chineseRemainder_modEq_unique.h6 : ¬∀ {m n : ℕ} (co : n.Coprime m) {a b z : ℕ}, z ≡ b [MOD m] → z ≡ ↑(Nat.chineseRemainder co a b) [MOD n * m] := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (1) (0) hc_k0 (0) (0) (1) hc_k1) (by
  decide +kernel)

-- Nat.chineseRemainder_modEq_unique, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.chineseRemainder_modEq_unique.h7 : ¬∀ {m n : ℕ} (co : n.Coprime m) {a b z : ℕ}, z ≡ a [MOD n] → z ≡ ↑(Nat.chineseRemainder co a b) [MOD n * m] := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (0) (1) hc_k0 (0) (0) (1) hc_k1) (by
  decide +kernel)

-- Set.exists_ne_map_eq_of_ncard_lt_of_maps_to, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_ne_map_eq_of_ncard_lt_of_maps_to.h4 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β},
        (∀ a ∈ s, f a ∈ t) →
          autoParam t.Finite Set.exists_ne_map_eq_of_ncard_lt_of_maps_to._auto_1 → ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (by
  simp) (by
  simp)) (by
  simp)

-- Set.exists_ne_map_eq_of_ncard_lt_of_maps_to, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_ne_map_eq_of_ncard_lt_of_maps_to.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β},
        t.ncard < s.ncard →
          ∀ {f : α → β},
            autoParam t.Finite Set.exists_ne_map_eq_of_ncard_lt_of_maps_to._auto_1 → ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.exists_ne_map_eq_of_ncard_lt_of_maps_to, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_ne_map_eq_of_ncard_lt_of_maps_to.h7 : ¬∀ {α β : Type} {s : Set α} {t : Set β},
        t.ncard < s.ncard → ∀ {f : α → β}, (∀ a ∈ s, f a ∈ t) → ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | True}) (by
  simp) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Equiv.Finset.disjUnionEquiv_symm_right, hypothesis 7: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Equiv.Finset.disjUnionEquiv_symm_right.h7.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} (h : Disjoint s t) {i : α}, i ∈ t → i ∈ s.disjUnion t h := by
  (intros; simp_all; done)
theorem HypCheckProof.Equiv.Finset.disjUnionEquiv_symm_right.h7.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} (h : Disjoint s t) {i : α} (hi : i ∈ t),
      (Equiv.Finset.disjUnionEquiv s t h).symm
          (⟨i, HypCheckProof.Equiv.Finset.disjUnionEquiv_symm_right.h7.der h hi⟩ : ↥(s.disjUnion t h)) =
        Sum.inr (⟨i, hi⟩ : ↥t) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @Equiv.Finset.disjUnionEquiv_symm_right hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.Equiv.Finset.disjUnionEquiv_symm_right.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6)

-- Set.MapsTo.comp, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.comp.h8 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ}, Set.MapsTo f s t → Set.MapsTo (g ∘ f) s p := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.MapsTo.comp, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.comp.h9 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ}, Set.MapsTo g t p → Set.MapsTo (g ∘ f) s p := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.true}) (fun n => n + 1 : ℕ → ℕ) (fun n => n % 2 == 0 : ℕ → Bool) (by
  simp)) (by
  simp)

-- Subtype.map_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.map_ne.h6 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} {f g : α → β},
        (∀ (a : α), p a → q (g a)) → ∀ {x y : Subtype p} (a : α), p a → q (f a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n = 0 })) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n = 0 }))) (by
  simp)

-- Subtype.map_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.map_ne.h7 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} {f g : α → β},
        (∀ (a : α), p a → q (f a)) → ∀ {x y : Subtype p} (a : α), p a → q (g a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n = 0 })) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { n : ℕ // n = 0 }))) (by
  simp)

-- Set.image2_subset, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_subset.h8 : ¬∀ {α β γ : Type} {f : α → β → γ} {s s' : Set α} {t t' : Set β}, t ⊆ t' → Set.image2 f s t ⊆ Set.image2 f s' t' := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Set.image2_subset, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_subset.h9 : ¬∀ {α β γ : Type} {f : α → β → γ} {s s' : Set α} {t t' : Set β}, s ⊆ s' → Set.image2 f s t ⊆ Set.image2 f s' t' := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  rfl)) (by
  simp)

-- Matrix.map_ofNat, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.map_ofNat.h9 : ¬∀ {n α β : Type} [inst : DecidableEq n] [inst : AddMonoidWithOne α] [inst_1 : Zero β] {f : α → β},
        f 0 = 0 → ∀ (d : ℕ), d.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (instDecidableEqNat) (Nat.instAddMonoidWithOne) (Nat.instMulZeroClass.toZero) (fun _ => 0 : ℕ → ℕ) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.lookup_ext, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lookup_ext.h7 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {l₀ l₁ : List (Sigma β)}, l₀.NodupKeys → l₁.NodupKeys → l₀.Perm l₁ := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) ([]) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)]) (by
  simp) (by
  simp)) (by
  decide +kernel)

-- List.IsChain.rel_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.rel_cons.h6 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a b : α} [inst : IsTrans α R], b ∈ l → R a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (0) (0) _ (by
  decide)) (by
  decide +kernel)

-- List.IsChain.rel_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.rel_cons.h7 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a b : α} [inst : IsTrans α R], List.IsChain R (a :: l) → R a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (0) (0) _ (by
  decide)) (by
  decide +kernel)

-- Sum.LiftRel.exists_of_isLeft_left, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sum.LiftRel.exists_of_isLeft_left.h8 : ¬∀ {α β γ δ : Type} {r : α → γ → Prop} {s : β → δ → Prop} {x : α ⊕ β} {y : γ ⊕ δ},
        x.isLeft = Bool.true → ∃ (a : α) (c : γ), r a c ∧ x = Sum.inl a ∧ y = Sum.inl c := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (Sum.inl 0) (Sum.inl 0) (by
  decide)) (by
  simp)

-- Sum.LiftRel.exists_of_isRight_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sum.LiftRel.exists_of_isRight_right.h8 : ¬∀ {α β γ δ : Type} {r : α → γ → Prop} {s : β → δ → Prop} {x : α ⊕ β} {y : γ ⊕ δ},
        y.isRight = Bool.true → ∃ (b : β) (d : δ), s b d ∧ x = Sum.inr b ∧ y = Sum.inr d := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (Sum.inl 0) (Sum.inr 0) (by
  decide)) (by
  simp)

-- Sum.LiftRel.exists_of_isRight_right, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sum.LiftRel.exists_of_isRight_right.h9 : ¬∀ {α β γ δ : Type} {r : α → γ → Prop} {s : β → δ → Prop} {x : α ⊕ β} {y : γ ⊕ δ},
        Sum.LiftRel r s x y → ∃ (b : β) (d : δ), s b d ∧ x = Sum.inr b ∧ y = Sum.inr d := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (Sum.inl 0) (Sum.inl 0) (by
  decide)) (by
  simp)

-- List.not_lt_of_mem_argmax, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_lt_of_mem_argmax.h8 : ¬∀ {α β : Type} [inst : Preorder β] [inst_1 : DecidableLT β] {f : α → β} {l : List α} {a m : α},
        m ∈ List.argmax f l → ¬f m < f a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instPreorder) (Nat.decLt) (fun n => n + 1 : ℕ → ℕ) ([0]) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.not_lt_of_mem_argmax, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_lt_of_mem_argmax.h9 : ¬∀ {α β : Type} [inst : Preorder β] [inst_1 : DecidableLT β] {f : α → β} {l : List α} {a m : α}, a ∈ l → ¬f m < f a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instPreorder) (Nat.decLt) (fun n => n + 1 : ℕ → ℕ) ([1]) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.not_lt_of_mem_argmin, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_lt_of_mem_argmin.h8 : ¬∀ {α β : Type} [inst : Preorder β] [inst_1 : DecidableLT β] {f : α → β} {l : List α} {a m : α},
        m ∈ List.argmin f l → ¬f a < f m := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instPreorder) (Nat.decLt) (fun n => n + 1 : ℕ → ℕ) ([1]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.not_lt_of_mem_argmin, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_lt_of_mem_argmin.h9 : ¬∀ {α β : Type} [inst : Preorder β] [inst_1 : DecidableLT β] {f : α → β} {l : List α} {a m : α}, a ∈ l → ¬f a < f m := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instPreorder) (Nat.decLt) (fun n => n + 1 : ℕ → ℕ) ([0]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.isRotated_next_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isRotated_next_eq.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l l' : List α}, l.Nodup → ∀ {x : α}, x ∈ l → l ~r l' := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([]) (by
  decide) (0) (by
  decide)) (by
  decide +kernel)

-- List.isRotated_next_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isRotated_next_eq.h7 : ¬∀ {α : Type} [inst : DecidableEq α] {l l' : List α}, l ~r l' → l.Nodup → ∀ {x : α}, x ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([]) (by
  decide) (by
  decide) (0)) (by
  decide +kernel)

-- List.Pairwise.cons_cons_of_trans, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.cons_cons_of_trans.h6 : ¬∀ {α : Type} {R : α → α → Prop} [inst : IsTrans α R] {l : List α} {a b : α},
        List.Pairwise R (b :: l) → List.Pairwise R (a :: b :: l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) _ ([]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.cons_cons_of_trans, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Pairwise.cons_cons_of_trans.h7.inst : ¬List.Pairwise (fun (a b : ℕ) => a < b) [0, 1, 0] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Pairwise.cons_cons_of_trans.h7.prem0 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.Pairwise.cons_cons_of_trans.h7 : ¬∀ {α : Type} {R : α → α → Prop} [inst : IsTrans α R] {l : List α} {a b : α}, R a b → List.Pairwise R (a :: b :: l) := fun hc_h => HypCheckProof.List.Pairwise.cons_cons_of_trans.h7.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) _ ([0]) (0) (1) HypCheckProof.List.Pairwise.cons_cons_of_trans.h7.prem0)

-- Set.SurjOn.comp, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.comp.h8 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ}, Set.SurjOn f s t → Set.SurjOn (g ∘ f) s p := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.SurjOn.comp, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.comp.h9 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ}, Set.SurjOn g t p → Set.SurjOn (g ∘ f) s p := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Bool) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.true}) (fun n => n + 1 : ℕ → ℕ) (fun n => n % 2 == 0 : ℕ → Bool) (by
  simp)) (by
  simp)

-- Set.EqOn.cancel_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.cancel_right.h8 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {f : α → β} {g₁ g₂ : β → γ}, Set.SurjOn f s t → Set.EqOn g₁ g₂ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Finsupp.NonTorsionWeight.ne_zero, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.NonTorsionWeight.ne_zero.h8 : ¬∀ {σ M : Type} (R : Type) [inst : Semiring R] (w : σ → M) [inst_1 : AddCommMonoid M] [inst : Module R M]
        [inst : Nontrivial R] (s : σ), w s ≠ 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instSemiring) (fun _ => 0 : ℕ → ℕ) (Nat.instAddCommMonoid) (Semiring.toModule) _ (0)) (by
  decide +kernel)

-- Finsupp.comapDomain_single_of_not_mem_range, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.comapDomain_single_of_not_mem_range.h6 : ¬∀ {α β M : Type} [inst : Zero M] {f : α → β} {b : β} (m : M) (hf : Set.InjOn f (f ⁻¹' ↑(fun₀ | b => m).support)),
        Finsupp.comapDomain f (fun₀ | b => m) hf = 0 := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (fun n => n + 1 : ℕ → ℕ) (1) (1) hc_k0) (by
  simp)

-- DFinsupp.lex_lt_of_lt, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.lex_lt_of_lt.h8 : ¬∀ {ι : Type} {α : ι → Type} [inst : (i : ι) → Zero (α i)] [inst_1 : (i : ι) → PartialOrder (α i)] (r : ι → ι → Prop)
        [inst_2 : IsStrictOrder ι r] {x y : Π₀ (i : ι), α i}, Pi.Lex r (fun {i : ι} (x1 x2 : α i) => x1 < x2) ⇑x ⇑y := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (fun (i : ℕ) => Nat.instMulZeroClass.toZero) (fun (i : ℕ) => Nat.instPartialOrder) (fun a b => a < b : ℕ → ℕ → Prop) _ (0) (0)) (by
  nofun)

-- Int.gcd_greatest, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.gcd_greatest.h3 : ¬∀ {a b d : ℤ}, d ∣ a → d ∣ b → (∀ (e : ℤ), e ∣ a → e ∣ b → e ∣ d) → d = ↑(a.gcd b) := fun hc_h => absurd (@hc_h (0) (1) (-1) (by
  decide) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Int.gcd_greatest, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.gcd_greatest.h4 : ¬∀ {a b d : ℤ}, 0 ≤ d → d ∣ b → (∀ (e : ℤ), e ∣ a → e ∣ b → e ∣ d) → d = ↑(a.gcd b) := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Int.gcd_greatest, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.gcd_greatest.h5 : ¬∀ {a b d : ℤ}, 0 ≤ d → d ∣ a → (∀ (e : ℤ), e ∣ a → e ∣ b → e ∣ d) → d = ↑(a.gcd b) := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Int.gcd_greatest, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.gcd_greatest.h6 : ¬∀ {a b d : ℤ}, 0 ≤ d → d ∣ a → d ∣ b → d = ↑(a.gcd b) := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Fintype.prod_eq_mul, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Fintype.prod_eq_mul.h7.inst : ¬∏ x : Unit, (fun (a : Unit) => 2) x = (fun (a : Unit) => 2) PUnit.unit * (fun (a : Unit) => 2) PUnit.unit := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Fintype.prod_eq_mul.h7.prem0 : ∀ (x : Unit), x ≠ PUnit.unit ∧ x ≠ PUnit.unit → (fun (a : Unit) => 2) x = 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Fintype.prod_eq_mul.h7 : ¬∀ {α M : Type} [inst : Fintype α] [inst_1 : CommMonoid M] {f : α → M} (a b : α),
        (∀ (x : α), x ≠ a ∧ x ≠ b → f x = 1) → ∏ x : α, f x = f a * f b := fun hc_h => HypCheckProof.Fintype.prod_eq_mul.h7.inst (@hc_h (Unit) (ℕ) (PUnit.fintype) (Nat.instCommMonoid) (fun (a : Unit) => 2) (PUnit.unit) (PUnit.unit) HypCheckProof.Fintype.prod_eq_mul.h7.prem0)

-- Fintype.prod_eq_mul, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.prod_eq_mul.h8 : ¬∀ {α M : Type} [inst : Fintype α] [inst_1 : CommMonoid M] {f : α → M} (a b : α), a ≠ b → ∏ x : α, f x = f a * f b := fun hc_h => absurd (@hc_h (Fin 3) (ℕ) (Fin.fintype 3) (Nat.instCommMonoid) (fun (a : Fin 3) => 2) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3)) (by
  decide)) (by
  decide +kernel)

-- Fintype.sum_eq_add, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.sum_eq_add.h7 : ¬∀ {α M : Type} [inst : Fintype α] [inst_1 : AddCommMonoid M] {f : α → M} (a b : α),
        (∀ (x : α), x ≠ a ∧ x ≠ b → f x = 0) → ∑ x : α, f x = f a + f b := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (CommRing.toCommSemiring.toAddCommMonoid) (not : Bool → Bool) (Bool.false) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Fintype.sum_eq_add, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.sum_eq_add.h8 : ¬∀ {α M : Type} [inst : Fintype α] [inst_1 : AddCommMonoid M] {f : α → M} (a b : α), a ≠ b → ∑ x : α, f x = f a + f b := fun hc_h => absurd (@hc_h (Fin 3) (ℕ) (Fin.fintype 3) (Nat.instAddCommMonoid) (fun (a : Fin 3) => 1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3)) (by
  decide)) (by
  decide +kernel)

-- StrictAntiOn.mono, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictAntiOn.mono.h8 : ¬∀ {α β : Type} {s s₂ : Set α} {f : α → β} [inst : Preorder α] [inst_1 : Preorder β],
        StrictAntiOn f s → StrictAntiOn f s₂ := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({b : Bool | b = Bool.true}) ({x : Bool | True}) (fun b => if b then 1 else 0 : Bool → ℕ) (Bool.instPartialOrder.toPreorder) (Nat.instPreorder) (by
  decide)) (by
  decide +kernel)

-- Set.MapsTo.inter_inter, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.inter_inter.h7 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {f : α → β}, Set.MapsTo f s₂ t₂ → Set.MapsTo f (s₁ ∩ s₂) (t₁ ∩ t₂) := fun hc_h => absurd (@hc_h (ℕ) (Bool) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) (fun n => n % 2 == 0 : ℕ → Bool) (by
  simp)) (by
  simp)

-- Function.Semiconj.mapsTo_image_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Semiconj.mapsTo_image_right.h7 : ¬∀ {α β : Type} {fa : α → α} {fb : β → β} {f : α → β} {s : Set α} {t : Set β},
        Set.MapsTo f s t → Set.MapsTo f (fa '' s) (fb '' t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Rat.isInt_intCeil_ofIsRat_neg, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.isInt_intCeil_ofIsRat_neg.h8 : ¬∀ {α : Type} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStrictOrderedRing α] [inst_3 : FloorRing α] (r : α)
        (n d : ℕ), Mathlib.Meta.NormNum.IsInt ⌈r⌉ (Int.negOfNat (n / d)) := fun hc_h => absurd (@hc_h (ℚ) (Rat.instField) (Rat.linearOrder) _ (Rat.instFloorRing) (1) (0) (0)) (by
  nofun)

-- List.le_of_mem_argmax, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_of_mem_argmax.h7 : ¬∀ {α β : Type} [inst : LinearOrder β] {f : α → β} {l : List α} {a m : α}, m ∈ List.argmax f l → f a ≤ f m := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (fun n => n + 1 : ℕ → ℕ) ([0]) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.le_of_mem_argmax, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_of_mem_argmax.h8 : ¬∀ {α β : Type} [inst : LinearOrder β] {f : α → β} {l : List α} {a m : α}, a ∈ l → f a ≤ f m := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (fun n => n + 1 : ℕ → ℕ) ([1]) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.suffix_of_getLast_mem_of_infix, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.suffix_of_getLast_mem_of_infix.h3 : ¬∀ {α : Type} {l₁ l₂ : List α} {hne : l₂ ≠ []}, l₂.getLast hne ∈ l₁ → l₂.Nodup → l₁ <:+ l₂ := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) ([0, 1]) ([0]) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- List.Nodup.suffix_of_getLast_mem_of_infix, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.suffix_of_getLast_mem_of_infix.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <:+: l₂ → l₂.Nodup → l₂ ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.suffix_of_getLast_mem_of_infix, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.suffix_of_getLast_mem_of_infix.h5 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <:+: l₂ → ∀ {hne : l₂ ≠ []}, l₂.Nodup → l₁ <:+ l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([0, 1]) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.eq_of_getLast_mem_of_prefix, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.eq_of_getLast_mem_of_prefix.h3 : ¬∀ {α : Type} {l₁ l₂ : List α} {hne : l₂ ≠ []}, l₂.getLast hne ∈ l₁ → l₂.Nodup → l₁ = l₂ := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) ([0, 1]) ([0]) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- List.Nodup.eq_of_getLast_mem_of_prefix, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.eq_of_getLast_mem_of_prefix.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <+: l₂ → l₂.Nodup → l₂ ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.eq_of_getLast_mem_of_prefix, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.eq_of_getLast_mem_of_prefix.h5 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <+: l₂ → ∀ {hne : l₂ ≠ []}, l₂.Nodup → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.eq_of_getLast_mem_of_prefix, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.eq_of_getLast_mem_of_prefix.h6 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <+: l₂ → ∀ {hne : l₂ ≠ []}, l₂.getLast hne ∈ l₁ → l₁ = l₂ := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) ([0]) ([0, 0]) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- List.Nodup.eq_of_head_mem_of_suffix, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.eq_of_head_mem_of_suffix.h3 : ¬∀ {α : Type} {l₁ l₂ : List α} {hne : l₂ ≠ []}, l₂.head hne ∈ l₁ → l₂.Nodup → l₁ = l₂ := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) ([0]) ([0, 1]) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- List.Nodup.eq_of_head_mem_of_suffix, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.eq_of_head_mem_of_suffix.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <:+ l₂ → l₂.Nodup → l₂ ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.eq_of_head_mem_of_suffix, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.eq_of_head_mem_of_suffix.h5 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <:+ l₂ → ∀ {hne : l₂ ≠ []}, l₂.Nodup → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.eq_of_head_mem_of_suffix, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.eq_of_head_mem_of_suffix.h6 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <:+ l₂ → ∀ {hne : l₂ ≠ []}, l₂.head hne ∈ l₁ → l₁ = l₂ := fun hc_h => absurd (fun hc_k0 hc_k1 hc_k2 => @hc_h (ℕ) ([0]) ([0, 0]) hc_k0 hc_k1 hc_k2) (by
  decide +kernel)

-- CFilter.coe_mk, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.CFilter.coe_mk.h6.inst : ¬∀ (a b : Bool), (!(fun (a b : Bool) => !a || b) a b) ≤ !a := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.CFilter.coe_mk.h6.prem0 : ∀ (a b : Bool), (!(fun (a b : Bool) => !a || b) a b) ≤ !b := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.CFilter.coe_mk.h6 : ¬∀ {α σ : Type} [inst : PartialOrder α] (f : σ → α) (pt : σ) (inf : σ → σ → σ),
        (∀ (a b : σ), f (inf a b) ≤ f b) → ∀ (a a b : σ), f (inf a b) ≤ f a := fun hc_h => HypCheckProof.CFilter.coe_mk.h6.inst (@hc_h (Bool) (Bool) (Bool.instPartialOrder) (Bool.not) (Bool.false) (fun (a b : Bool) => !a || b) HypCheckProof.CFilter.coe_mk.h6.prem0 (Bool.false))

-- CFilter.coe_mk, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.CFilter.coe_mk.h7.inst : ¬∀ (a b : Bool),
        (fun (b : Bool) => if b = Bool.true then 1 else 0) ((fun (a x : Bool) => a) a b) ≤
          (fun (b : Bool) => if b = Bool.true then 1 else 0) b := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.CFilter.coe_mk.h7.prem0 : ∀ (a b : Bool),
      (fun (b : Bool) => if b = Bool.true then 1 else 0) ((fun (a x : Bool) => a) a b) ≤
        (fun (b : Bool) => if b = Bool.true then 1 else 0) a := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.CFilter.coe_mk.h7 : ¬∀ {α σ : Type} [inst : PartialOrder α] (f : σ → α) (pt : σ) (inf : σ → σ → σ),
        (∀ (a b : σ), f (inf a b) ≤ f a) → ∀ (a a b : σ), f (inf a b) ≤ f b := fun hc_h => HypCheckProof.CFilter.coe_mk.h7.inst (@hc_h (ℕ) (Bool) (Nat.instPartialOrder) (fun (b : Bool) => if b = Bool.true then 1 else 0) (Bool.false) (fun (a x : Bool) => a) HypCheckProof.CFilter.coe_mk.h7.prem0 (Bool.false))

-- Nat.diag_induction, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.diag_induction.h2 : ¬∀ (motive : ℕ → ℕ → Prop),
        (∀ (a : ℕ), motive (a + 1) (a + 1)) →
          (∀ (a b : ℕ), a < b → motive (a + 1) b → motive a (b + 1) → motive (a + 1) (b + 1)) →
            ∀ (a b : ℕ), a < b → motive a b := fun hc_h => absurd (@hc_h (fun a b => a = b : ℕ → ℕ → Prop) (by
  simp) (by
  omega) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.diag_induction, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.diag_induction.h6 : ¬∀ (motive : ℕ → ℕ → Prop),
        (∀ (a : ℕ), motive (a + 1) (a + 1)) →
          (∀ (b : ℕ), motive 0 (b + 1)) →
            (∀ (a b : ℕ), a < b → motive (a + 1) b → motive a (b + 1) → motive (a + 1) (b + 1)) → ∀ (a b : ℕ), motive a b := fun hc_h => absurd (@hc_h (fun a b => a ≤ b : ℕ → ℕ → Prop) (by
  simp) (by
  simp) (by
  omega) (1) (0)) (by
  decide +kernel)

-- List.Perm.kinsert, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.kinsert.h8 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {b : β a} {l₁ l₂ : List (Sigma β)},
        l₁.NodupKeys → (List.kinsert a b l₁).Perm (List.kinsert a b l₂) := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) (0) ([]) ([(⟨1, 0⟩ : (_ : ℕ) × ℕ)]) (by
  simp)) (by
  decide +kernel)

-- Nat.Prime.dvd_choose_add, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose_add.h4 : ¬∀ {p a b : ℕ}, Nat.Prime p → b < p → p ≤ a + b → p ∣ (a + b).choose a := fun hc_h => absurd (@hc_h (2) (2) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_choose_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose_add.h5 : ¬∀ {p a b : ℕ}, Nat.Prime p → a < p → p ≤ a + b → p ∣ (a + b).choose a := fun hc_h => absurd (@hc_h (2) (0) (2) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_choose_add, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose_add.h6 : ¬∀ {p a b : ℕ}, Nat.Prime p → a < p → b < p → p ∣ (a + b).choose a := fun hc_h => absurd (@hc_h (2) (0) (0) (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Equiv.ofLeftInverseOfCardLE_symm_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofLeftInverseOfCardLE_symm_apply.h4 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] (f : α → β) (g : β → α),
        Function.LeftInverse g f → ∀ (a : β), Fintype.card β ≤ Fintype.card α := fun hc_h => absurd (@hc_h (Unit) (Bool) (PUnit.fintype) (Bool.fintype) (fun (a : Unit) => Bool.false) (fun (a : Bool) => PUnit.unit) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- Equiv.ofLeftInverseOfCardLE_symm_apply, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofLeftInverseOfCardLE_symm_apply.h7 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β],
        Fintype.card β ≤ Fintype.card α → ∀ (f : α → β) (g : β → α) (a : β), Function.LeftInverse g f := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype) (by
  decide) (not : Bool → Bool) (fun _ => true : Bool → Bool) (Bool.false)) (by
  decide +kernel)

-- Equiv.ofLeftInverseOfCardLE_apply, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofLeftInverseOfCardLE_apply.h4 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] (f : α → β) (g : β → α),
        Function.LeftInverse g f → ∀ (a : α), Fintype.card β ≤ Fintype.card α := fun hc_h => absurd (@hc_h (Unit) (Bool) (PUnit.fintype) (Bool.fintype) (fun (a : Unit) => Bool.false) (fun (a : Bool) => PUnit.unit) (by
  decide) (PUnit.unit)) (by
  decide +kernel)

-- Equiv.ofLeftInverseOfCardLE_apply, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.ofLeftInverseOfCardLE_apply.h7 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β],
        Fintype.card β ≤ Fintype.card α → ∀ (f : α → β) (g : β → α) (a : α), Function.LeftInverse g f := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype) (by
  decide) (not : Bool → Bool) (fun _ => true : Bool → Bool) (Bool.false)) (by
  decide +kernel)

-- Function.Semiconj.mapsTo_image, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Semiconj.mapsTo_image.h7 : ¬∀ {α β : Type} {fa : α → α} {fb : β → β} {f : α → β} {s t : Set α}, Set.MapsTo fa s t → Set.MapsTo fb (f '' s) (f '' t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- PNat.Coprime.factor_eq_gcd_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.factor_eq_gcd_right.h4 : ¬∀ {a b m n : ℕ+}, a ∣ m → b ∣ n → a = (b * a).gcd m := fun hc_h => absurd (@hc_h (1) (2) (2) (2) (by
  simp) (by
  rfl)) (by
  decide +kernel)

-- PNat.Coprime.factor_eq_gcd_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.factor_eq_gcd_right.h5 : ¬∀ {a b m n : ℕ+}, m.Coprime n → b ∣ n → a = (b * a).gcd m := fun hc_h => absurd (@hc_h (2) (1) (1) (1) (by
  rfl) (by
  rfl)) (by
  decide +kernel)

-- PNat.Coprime.factor_eq_gcd_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.factor_eq_gcd_right.h6 : ¬∀ {a b m n : ℕ+}, m.Coprime n → a ∣ m → a = (b * a).gcd m := fun hc_h => absurd (@hc_h (1) (2) (2) (1) (by
  rfl) (by
  simp)) (by
  decide +kernel)

-- PNat.Coprime.factor_eq_gcd_left_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.factor_eq_gcd_left_right.h4 : ¬∀ {a b m n : ℕ+}, a ∣ m → b ∣ n → a = m.gcd (a * b) := fun hc_h => absurd (@hc_h (1) (2) (2) (2) (by
  simp) (by
  rfl)) (by
  decide +kernel)

-- PNat.Coprime.factor_eq_gcd_left_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.factor_eq_gcd_left_right.h5 : ¬∀ {a b m n : ℕ+}, m.Coprime n → b ∣ n → a = m.gcd (a * b) := fun hc_h => absurd (@hc_h (2) (1) (1) (1) (by
  rfl) (by
  rfl)) (by
  decide +kernel)

-- PNat.Coprime.factor_eq_gcd_left_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.factor_eq_gcd_left_right.h6 : ¬∀ {a b m n : ℕ+}, m.Coprime n → a ∣ m → a = m.gcd (a * b) := fun hc_h => absurd (@hc_h (1) (2) (2) (1) (by
  rfl) (by
  simp)) (by
  decide +kernel)

-- List.idxOf_tail_of_head_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_tail_of_head_ne.h3 : ¬∀ {α : Type} {l : List α} [inst : BEq α] {a : α} (hl : l ≠ []),
        l.head hl ≠ a → List.idxOf a l.tail = List.idxOf a l - 1 := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) ([0, 1]) (⟨fun a b => a != b⟩ : BEq ℕ) (1) hc_k0 hc_k1) (by
  decide +kernel)

-- List.idxOf_tail_of_head_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_tail_of_head_ne.h5 : ¬∀ {α : Type} {l : List α} [inst : BEq α] [inst : LawfulBEq α] {a : α}, l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([]) (instBEqOfDecidableEq) _ (0)) (by
  decide +kernel)

-- List.idxOf_tail_of_head_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_tail_of_head_ne.h6 : ¬∀ {α : Type} {l : List α} [inst : BEq α] [inst_1 : LawfulBEq α] {a : α},
        l ≠ [] → List.idxOf a l.tail = List.idxOf a l - 1 := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (instBEqOfDecidableEq) _ (0) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.erase_getElem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.erase_getElem.h2 : ¬∀ {α : Type} [inst : BEq α] {l : List α}, l.Nodup → ∀ (i : ℕ) (h : i < l.length), l.erase l[i] = l.eraseIdx i := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (⟨fun a b => a != b⟩ : BEq ℕ) ([0]) hc_k0 (0) hc_k1) (by
  decide +kernel)

-- List.Nodup.erase_getElem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.erase_getElem.h6 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {l : List α}, l.Nodup → ∀ (i : ℕ), i < l.length := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ ([]) (by
  decide) (0)) (by
  decide +kernel)

-- Set.sep_of_ncard_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sep_of_ncard_eq.h4 : ¬∀ {α : Type} {s : Set α} {a : α} {P : α → Prop}, a ∈ s → autoParam s.Finite Set.sep_of_ncard_eq._auto_1 → P a := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0) (fun _ => False : ℕ → Prop) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Set.sep_of_ncard_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sep_of_ncard_eq.h5 : ¬∀ {α : Type} {s : Set α} {a : α} {P : α → Prop},
        {x : α | x ∈ s ∧ P x}.ncard = s.ncard → autoParam s.Finite Set.sep_of_ncard_eq._auto_1 → P a := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1) (fun n => n = 0 : ℕ → Prop) (by
  simp) (by
  simp)) (by
  decide +kernel)

-- List.Pairwise.rel_head_of_rel_head_head, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_head_of_rel_head_head.h4 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α} (ha : a ∈ l),
        R (l.head (List.ne_nil_of_mem ha)) (l.head (List.ne_nil_of_mem ha)) → R (l.head (List.ne_nil_of_mem ha)) a := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ([1, 0]) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- List.Pairwise.rel_head_of_rel_head_head, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_head_of_rel_head_head.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α}, List.Pairwise R l → a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (0) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.rel_head_of_rel_head_head, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_head_of_rel_head_head.h6 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α},
        List.Pairwise R l → ∀ (ha : a ∈ l), R (l.head (List.ne_nil_of_mem ha)) a := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- Set.exists_superset_subset_encard_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_superset_subset_encard_eq.h5 : ¬∀ {α : Type} {s t : Set α} {k : ℕ∞}, s ⊆ t → k ≤ t.encard → ∃ (r : Set α), s ⊆ r ∧ r ⊆ t ∧ r.encard = k := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n % 2 = 0}) (0) (by
  simp) (by
  simp)) (by
  simp)

-- Finite.bddAbove_range, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finite.bddAbove_range.h2 : ¬∀ {ι α : Type} [inst : Nonempty α] [inst : Preorder α] [inst_1 : IsDirectedOrder α] (f : ι → α), BddAbove (Set.range f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _ (Nat.instPreorder) _ (fun n => n : ℕ → ℕ)) (by
  simp)

-- Nat.cast_pos', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.cast_pos'.h3 : Not
      (∀ {α : Type} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α]
        [inst_2 :
          @ZeroLEOneClass α
            (@AddZero.toZero α
              (@AddZeroClass.toAddZero α (@AddMonoid.toAddZeroClass α (@AddMonoidWithOne.toAddMonoid α inst))))
            (@AddMonoidWithOne.toOne α inst) (@Preorder.toLE α (@PartialOrder.toPreorder α inst_1))]
        [inst_3 :
          @NeZero α
            (@AddZero.toZero α
              (@AddZeroClass.toAddZero α (@AddMonoid.toAddZeroClass α (@AddMonoidWithOne.toAddMonoid α inst))))
            (@OfNat.ofNat α (nat_lit 1) (@One.toOfNat1 α (@AddMonoidWithOne.toOne α inst)))]
        {n : Nat},
        Iff
          (@LT.lt α (@Preorder.toLT α (@PartialOrder.toPreorder α inst_1))
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@AddZero.toZero α
                  (@AddZeroClass.toAddZero α (@AddMonoid.toAddZeroClass α (@AddMonoidWithOne.toAddMonoid α inst))))))
            (@Nat.cast α (@AddMonoidWithOne.toNatCast α inst) n))
          (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)) := fun hc_h => absurd (@hc_h (Bool) (@AddGroupWithOne.toAddMonoidWithOne Bool (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool))) (Bool.instPartialOrder) (@ZeroLEOneClass.mk (Bool) (@AddZero.toZero Bool
      (@AddZeroClass.toAddZero Bool
        (@AddMonoid.toAddZeroClass Bool
          (@AddMonoidWithOne.toAddMonoid Bool
            (@AddGroupWithOne.toAddMonoidWithOne Bool
              (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool))))))) (@AddMonoidWithOne.toOne Bool
      (@AddGroupWithOne.toAddMonoidWithOne Bool
        (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool)))) (@Preorder.toLE Bool (@PartialOrder.toPreorder Bool Bool.instPartialOrder)) (by (try dsimp only);   decide)) _ (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (by
  decide +kernel)

-- Nat.ofNat_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofNat_pos.h3 : Not
      (∀ {α : Type} [inst : Semiring α] [inst_1 : PartialOrder α] [inst_2 : Nontrivial α] {n : Nat} [inst_3 : n.AtLeastTwo],
        @LT.lt α (@Preorder.toLT α (@PartialOrder.toPreorder α inst_1))
          (@OfNat.ofNat α (nat_lit 0) (@Zero.toOfNat0 α (@MulZeroClass.toZero α (@instMulZeroClassOfSemiring α inst))))
          (@OfNat.ofNat α n
            (@instOfNatAtLeastTwo α n
              (@AddMonoidWithOne.toNatCast α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
              inst_3))) := fun hc_h => absurd (@hc_h (Bool) (@CommSemiring.toSemiring Bool (@CommRing.toCommSemiring Bool (@BooleanRing.toCommRing Bool instBooleanRingBool))) (Bool.instPartialOrder) _ (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) _) (by
  decide +kernel)

-- Nat.ofNat_pos, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofNat_pos.h6 : ¬∀ {α : Type} [inst : Semiring α] [inst_1 : PartialOrder α] [inst : IsOrderedRing α] [inst : Nontrivial α] {n : ℕ},
        n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (Nat.instSemiring) (Nat.instPartialOrder) _ _ (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.find_mono, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Nat.find_mono.h5.der : ∀ {p q : Nat → Prop} [inst : @DecidablePred Nat p] [inst : @DecidablePred Nat q],
      (∀ (n : Nat), q n → p n) → ∀ {hq : ∃ (n : Nat), q n}, ∃ (n : Nat), p n := by
  (intros; grind)
theorem HypCheckProof.Nat.find_mono.h5 : ∀ {p q : Nat → Prop} [inst : @DecidablePred Nat p] [inst_1 : @DecidablePred Nat q] (h : ∀ (n : Nat), q n → p n)
      {hq : ∃ (n : Nat), q n},
      @LE.le Nat instLENat (@Nat.find p inst (@HypCheckProof.Nat.find_mono.h5.der p q inst inst_1 h hq))
        (@Nat.find q inst_1 hq) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Nat.find_mono hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Nat.find_mono.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x5

-- Nat.find_mono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_mono.h6 : ¬∀ {p q : ℕ → Prop} [inst : DecidablePred p] [inst : DecidablePred q],
        (∀ (n : ℕ), q n → p n) → ∀ {hp : ∃ (n : ℕ), p n}, ∃ (n : ℕ), q n := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (fun (a : ℕ) => instDecidableFalse) (by
  simp) (by
  simp)) (by
  simp)

-- Nat.multiplicative_factorization, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.multiplicative_factorization.h4 : ¬∀ {β : Type} [inst : CommMonoid β] (f : ℕ → β),
        (∀ (x y : ℕ), x.Coprime y → f (x * y) = f x * f y) →
          ∀ {n : ℕ}, n ≠ 0 → f n = n.factorization.prod fun (p k : ℕ) => f (p ^ k) := fun hc_h => absurd (@hc_h (ℕ) (Nat.instCommMonoid) (fun _ => 0 : ℕ → ℕ) (by
  simp) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.multiplicative_factorization, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.multiplicative_factorization.h6 : ¬∀ {β : Type} [inst : CommMonoid β] (f : ℕ → β),
        (∀ (x y : ℕ), x.Coprime y → f (x * y) = f x * f y) →
          f 1 = 1 → ∀ {n : ℕ}, f n = n.factorization.prod fun (p k : ℕ) => f (p ^ k) := fun hc_h => absurd (@hc_h (ℕ) (Nat.instCommMonoid) (fun n => n : ℕ → ℕ) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (0)) (by
  decide +kernel)

-- List.SortedGT.eq_reverse_of_mem_iff_of_sortedLT, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.eq_reverse_of_mem_iff_of_sortedLT.h4 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁.SortedGT → l₂.SortedLT → l₁ = l₂.reverse := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.rel_head, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_head.h4 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α},
        List.Pairwise R l → ∀ (ha : a ∈ l), R (l.head (List.ne_nil_of_mem ha)) a := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- List.Pairwise.rel_head, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_head.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α} [inst : Std.Refl R] (ha : a ∈ l),
        R (l.head (List.ne_nil_of_mem ha)) a := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ([1, 0]) (0) _ hc_k0) (by
  decide +kernel)

-- List.Pairwise.rel_head, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_head.h6 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α} [inst : Std.Refl R], List.Pairwise R l → a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ([]) (0) _ (by
  decide)) (by
  decide +kernel)

-- Nat.multiplicative_factorization', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.multiplicative_factorization'.h5 : ¬∀ {n : ℕ} {β : Type} [inst : CommMonoid β] (f : ℕ → β),
        (∀ (x y : ℕ), x.Coprime y → f (x * y) = f x * f y) → f 1 = 1 → f n = n.factorization.prod fun (p k : ℕ) => f (p ^ k) := fun hc_h => absurd (@hc_h (0) (ℕ) (Nat.instCommMonoid) (fun n => n : ℕ → ℕ) (by
  simp) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- List.HasPeriod.take_append, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.HasPeriod.take_append.h6 : ¬∀ {α : Type} (p n : ℕ) (w : List α), p ∣ n → n ≤ w.length → (List.take n w ++ w).HasPeriod p := fun hc_h => absurd (@hc_h (ℕ) (1) (0) ([0, 1]) (by
  decide) (by
  decide)) (by
  nofun)

-- List.IsChain.sublist, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.sublist.h6 : ¬∀ {α : Type} {R : α → α → Prop} {l₁ l₂ : List α} [inst : IsTrans α R], List.IsChain R l₂ → List.IsChain R l₁ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0]) ([]) _ (by
  decide)) (by
  decide +kernel)

-- Choose.lucas_theorem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.lucas_theorem.h6 : ¬∀ {n k p : ℕ} [inst : Fact (Nat.Prime p)] {a : ℕ},
        n < p ^ a → ↑(n.choose k) ≡ ∏ i ∈ Finset.range a, ↑((n / p ^ i % p).choose (k / p ^ i % p)) [ZMOD ↑p] := fun hc_h => absurd (@hc_h (0) (1) (2) _ (0) (by
  decide)) (by
  decide +kernel)

-- ENat.add_lt_add_of_le_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.add_lt_add_of_le_of_lt.h5 : ¬∀ {a b c d : ℕ∞}, a ≠ ⊤ → c < d → a + c < b + d := fun hc_h => absurd (@hc_h (1) (0) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- ENat.add_lt_add_of_le_of_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.add_lt_add_of_le_of_lt.h6 : ¬∀ {a b c d : ℕ∞}, a ≠ ⊤ → a ≤ b → a + c < b + d := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.sublist_of_subperm_of_sortedGE, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sublist_of_subperm_of_sortedGE.h4 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁.SortedGE → l₂.SortedGE → l₁.Sublist l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0]) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.SortedGT.eq_of_mem_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.eq_of_mem_iff.h4 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₂.SortedGT → (∀ (a : α), a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0, 0]) ([0]) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- List.SortedGT.eq_of_mem_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.eq_of_mem_iff.h5 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁.SortedGT → (∀ (a : α), a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0]) ([0, 0]) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- List.SortedGT.eq_of_mem_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.eq_of_mem_iff.h6 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁.SortedGT → l₂.SortedGT → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.append, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.append.h4.inst : ¬List.IsChain (fun (a b : ℕ) => a < b) ([1, 0] ++ []) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.append.h4.prem0 : List.IsChain (fun (a b : ℕ) => a < b) [] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.append.h4.prem1 : ∀ x ∈ [1, 0].getLast?, ∀ y ∈ [].head?, (fun (a b : ℕ) => a < b) x y := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.IsChain.append.h4 : ¬∀ {α : Type} {R : α → α → Prop} {l₁ l₂ : List α},
        List.IsChain R l₂ → (∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y) → List.IsChain R (l₁ ++ l₂) := fun hc_h => HypCheckProof.List.IsChain.append.h4.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) ([1, 0]) ([]) HypCheckProof.List.IsChain.append.h4.prem0 HypCheckProof.List.IsChain.append.h4.prem1)

-- List.IsChain.append, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.append.h5.inst : ¬List.IsChain (fun (a b : ℕ) => a < b) ([] ++ [1, 0]) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.append.h5.prem0 : List.IsChain (fun (a b : ℕ) => a < b) [] := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.append.h5.prem1 : ∀ x ∈ [].getLast?, ∀ y ∈ [1, 0].head?, (fun (a b : ℕ) => a < b) x y := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.IsChain.append.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l₁ l₂ : List α},
        List.IsChain R l₁ → (∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y) → List.IsChain R (l₁ ++ l₂) := fun hc_h => HypCheckProof.List.IsChain.append.h5.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) ([]) ([1, 0]) HypCheckProof.List.IsChain.append.h5.prem0 HypCheckProof.List.IsChain.append.h5.prem1)

-- List.IsChain.append, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.append.h6 : ¬∀ {α : Type} {R : α → α → Prop} {l₁ l₂ : List α}, List.IsChain R l₁ → List.IsChain R l₂ → List.IsChain R (l₁ ++ l₂) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Coprime.of_dvd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.of_dvd.h4 : ¬∀ {a₁ a₂ b₁ b₂ : ℕ}, b₁ ∣ b₂ → a₂.Coprime b₂ → a₁.Coprime b₁ := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Coprime.of_dvd, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.of_dvd.h5 : ¬∀ {a₁ a₂ b₁ b₂ : ℕ}, a₁ ∣ a₂ → a₂.Coprime b₂ → a₁.Coprime b₁ := fun hc_h => absurd (@hc_h (0) (0) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Coprime.of_dvd, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.of_dvd.h6 : ¬∀ {a₁ a₂ b₁ b₂ : ℕ}, a₁ ∣ a₂ → b₁ ∣ b₂ → a₁.Coprime b₁ := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.rel_getLast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_getLast.h4 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α},
        List.Pairwise R l → ∀ (ha : a ∈ l), R a (l.getLast (List.ne_nil_of_mem ha)) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) (0) hc_k0 hc_k1) (by
  decide +kernel)

-- List.Pairwise.rel_getLast, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_getLast.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α} [inst : Std.Refl R] (ha : a ∈ l),
        R a (l.getLast (List.ne_nil_of_mem ha)) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) ([0, 1]) (0) _ hc_k0) (by
  decide +kernel)

-- List.Pairwise.rel_getLast, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_getLast.h6 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α} [inst : Std.Refl R], List.Pairwise R l → a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ([]) (0) _ (by
  decide)) (by
  decide +kernel)

-- Nat.cast_add_one_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.cast_add_one_pos.h3 : Not
      (∀ {α : Type} [inst : AddMonoidWithOne α] [inst_1 : PartialOrder α]
        [inst_2 :
          @ZeroLEOneClass α
            (@AddZero.toZero α
              (@AddZeroClass.toAddZero α (@AddMonoid.toAddZeroClass α (@AddMonoidWithOne.toAddMonoid α inst))))
            (@AddMonoidWithOne.toOne α inst) (@Preorder.toLE α (@PartialOrder.toPreorder α inst_1))]
        [inst_3 :
          @NeZero α
            (@AddZero.toZero α
              (@AddZeroClass.toAddZero α (@AddMonoid.toAddZeroClass α (@AddMonoidWithOne.toAddMonoid α inst))))
            (@OfNat.ofNat α (nat_lit 1) (@One.toOfNat1 α (@AddMonoidWithOne.toOne α inst)))]
        (n : Nat),
        @LT.lt α (@Preorder.toLT α (@PartialOrder.toPreorder α inst_1))
          (@OfNat.ofNat α (nat_lit 0)
            (@Zero.toOfNat0 α
              (@AddZero.toZero α
                (@AddZeroClass.toAddZero α (@AddMonoid.toAddZeroClass α (@AddMonoidWithOne.toAddMonoid α inst))))))
          (@HAdd.hAdd α α α
            (@instHAdd α (@AddSemigroup.toAdd α (@AddMonoid.toAddSemigroup α (@AddMonoidWithOne.toAddMonoid α inst))))
            (@Nat.cast α (@AddMonoidWithOne.toNatCast α inst) n)
            (@OfNat.ofNat α (nat_lit 1) (@One.toOfNat1 α (@AddMonoidWithOne.toOne α inst))))) := fun hc_h => absurd (@hc_h (Bool) (@AddGroupWithOne.toAddMonoidWithOne Bool (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool))) (Bool.instPartialOrder) (@ZeroLEOneClass.mk (Bool) (@AddZero.toZero Bool
      (@AddZeroClass.toAddZero Bool
        (@AddMonoid.toAddZeroClass Bool
          (@AddMonoidWithOne.toAddMonoid Bool
            (@AddGroupWithOne.toAddMonoidWithOne Bool
              (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool))))))) (@AddMonoidWithOne.toOne Bool
      (@AddGroupWithOne.toAddMonoidWithOne Bool
        (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool)))) (@Preorder.toLE Bool (@PartialOrder.toPreorder Bool Bool.instPartialOrder)) (by (try dsimp only);   decide)) _ (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Int.eq_mul_div_of_mul_eq_mul_of_dvd_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.eq_mul_div_of_mul_eq_mul_of_dvd_left.h4 : ¬∀ {a b c d : ℤ}, b ∣ c → b * a = c * d → a = c / b * d := fun hc_h => absurd (@hc_h (1) (0) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.eq_mul_div_of_mul_eq_mul_of_dvd_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.eq_mul_div_of_mul_eq_mul_of_dvd_left.h6 : ¬∀ {a b c d : ℤ}, b ≠ 0 → b ∣ c → a = c / b * d := fun hc_h => absurd (@hc_h (1) (1) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.SortedLT.eq_reverse_of_mem_iff_of_sortedGT, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.eq_reverse_of_mem_iff_of_sortedGT.h4 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁.SortedLT → l₂.SortedGT → l₁ = l₂.reverse := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.SortedLT.eq_reverse_of_mem_iff_of_sortedGT, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.eq_reverse_of_mem_iff_of_sortedGT.h5 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, (∀ (a : α), a ∈ l₁ ↔ a ∈ l₂) → l₂.SortedGT → l₁ = l₂.reverse := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0, 0]) ([0]) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- List.SortedLT.eq_reverse_of_mem_iff_of_sortedGT, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.eq_reverse_of_mem_iff_of_sortedGT.h6 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, (∀ (a : α), a ∈ l₁ ↔ a ∈ l₂) → l₁.SortedLT → l₁ = l₂.reverse := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0]) ([0, 0]) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- List.SortedLT.eq_of_mem_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.eq_of_mem_iff.h4 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₂.SortedLT → (∀ (a : α), a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0, 0]) ([0]) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- List.SortedLT.eq_of_mem_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.eq_of_mem_iff.h5 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁.SortedLT → (∀ (a : α), a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([0]) ([0, 0]) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- List.SortedLT.eq_of_mem_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.eq_of_mem_iff.h6 : ¬∀ {α : Type} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁.SortedLT → l₂.SortedLT → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPartialOrder) ([]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.find_congr', hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Nat.find_congr'.h4.der : ∀ {p q : Nat → Prop} [inst : @DecidablePred Nat p] [inst : @DecidablePred Nat q] {hq : ∃ (n : Nat), q n},
      (∀ {n : Nat}, Iff (p n) (q n)) → ∃ (n : Nat), p n := by
  (intros; simp_all; done)
theorem HypCheckProof.Nat.find_congr'.h4 : ∀ {p q : Nat → Prop} [inst : @DecidablePred Nat p] [inst_1 : @DecidablePred Nat q] {hq : ∃ (n : Nat), q n}
      (hpq : ∀ {n : Nat}, Iff (p n) (q n)),
      @Eq Nat (@Nat.find p inst (@HypCheckProof.Nat.find_congr'.h4.der p q inst inst_1 hq hpq)) (@Nat.find q inst_1 hq) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Nat.find_congr' hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Nat.find_congr'.h4.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x4 hc_x5

-- Nat.find_congr', hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Nat.find_congr'.h5.der : ∀ {p q : Nat → Prop} [inst : @DecidablePred Nat p] [inst : @DecidablePred Nat q] {hp : ∃ (n : Nat), p n},
      (∀ {n : Nat}, Iff (p n) (q n)) → ∃ (n : Nat), q n := by
  (intros; simp_all; done)
theorem HypCheckProof.Nat.find_congr'.h5 : ∀ {p q : Nat → Prop} [inst : @DecidablePred Nat p] [inst_1 : @DecidablePred Nat q] {hp : ∃ (n : Nat), p n}
      (hpq : ∀ {n : Nat}, Iff (p n) (q n)),
      @Eq Nat (@Nat.find p inst hp) (@Nat.find q inst_1 (@HypCheckProof.Nat.find_congr'.h5.der p q inst inst_1 hp hpq)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Nat.find_congr' hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Nat.find_congr'.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x5

-- List.IsChain.rel_getLast_head_of_append, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.rel_getLast_head_of_append.h4 : ¬∀ {α : Type} {R : α → α → Prop} {l₁ l₂ : List α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []), R (l₁.getLast h₁) (l₂.head h₂) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) ([0]) hc_k0 hc_k1) (by
  decide +kernel)

-- List.IsChain.rel_getLast_head_of_append, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.rel_getLast_head_of_append.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l₁ l₂ : List α}, List.IsChain R (l₁ ++ l₂) → l₂ ≠ [] → l₁ ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.rel_getLast_head_of_append, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.rel_getLast_head_of_append.h6 : ¬∀ {α : Type} {R : α → α → Prop} {l₁ l₂ : List α}, List.IsChain R (l₁ ++ l₂) → l₁ ≠ [] → l₂ ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Valid.merge, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid.merge.h4 : ¬∀ {α : Type} [inst : Preorder α] {l r : Ordnode α},
        r.Valid → Ordnode.All (fun (x : α) => Ordnode.All (fun (y : α) => x < y) r) l → (l.merge r).Valid := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (Ordnode.nil) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- Ordnode.Valid.merge, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid.merge.h5 : ¬∀ {α : Type} [inst : Preorder α] {l r : Ordnode α},
        l.Valid → Ordnode.All (fun (x : α) => Ordnode.All (fun (y : α) => x < y) r) l → (l.merge r).Valid := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Ordnode.nil) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  (repeat' constructor) <;> done) (by
  decide)) (by
  nofun)

-- HasSubset.Subset.ssubset_of_mem_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.HasSubset.Subset.ssubset_of_mem_notMem.h5 : ¬∀ {α : Type} {s t : Set α} {a : α}, s ⊆ t → a ∉ s → s ⊂ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (1) (by
  rfl) (by
  decide)) (by
  simp)

-- HasSubset.Subset.ssubset_of_mem_notMem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.HasSubset.Subset.ssubset_of_mem_notMem.h6 : ¬∀ {α : Type} {s t : Set α} {a : α}, s ⊆ t → a ∈ t → s ⊂ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (0) (by
  rfl) (by
  decide)) (by
  simp)

-- Nat.coprime_pow_primes, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_pow_primes.h4 : ¬∀ {p q : ℕ} (n m : ℕ), Nat.Prime q → p ≠ q → (p ^ n).Coprime (q ^ m) := fun hc_h => absurd (@hc_h (0) (2) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.coprime_pow_primes, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_pow_primes.h5 : ¬∀ {p q : ℕ} (n m : ℕ), Nat.Prime p → p ≠ q → (p ^ n).Coprime (q ^ m) := fun hc_h => absurd (@hc_h (2) (0) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.coprime_pow_primes, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_pow_primes.h6 : ¬∀ {p q : ℕ} (n m : ℕ), Nat.Prime p → Nat.Prime q → (p ^ n).Coprime (q ^ m) := fun hc_h => absurd (@hc_h (2) (2) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Finset.fold_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_singleton.h3 : ¬∀ {α β : Type} {op : β → β → β} [ha : Std.Associative op] {f : α → β} {b : β} {a : α}, Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (fun n => n + 1 : ℕ → ℕ) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.fold_singleton, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.fold_singleton.h4 : ¬∀ {α β : Type} {op : β → β → β} [hc : Std.Commutative op] {f : α → β} {b : β} {a : α}, Std.Associative op := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (fun n => n % 2 == 0 : ℕ → Bool) (Bool.false) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Option.bind_congr', hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Option.bind_congr'.h6.inst : ¬(Option.some 0).bind Option.some = Option.none.bind fun (x : ℕ) => Option.none := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Option.bind_congr'.h6.prem0 : ∀ a ∈ Option.none, Option.some a = (fun (x : ℕ) => Option.none) a := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Option.bind_congr'.h6 : ¬∀ {α β : Type} {f g : α → Option β} {x y : Option α}, (∀ a ∈ y, f a = g a) → x.bind f = y.bind g := fun hc_h => HypCheckProof.Option.bind_congr'.h6.inst (@hc_h (ℕ) (ℕ) (Option.some) (fun (x : ℕ) => Option.none) (Option.some 0) (Option.none) HypCheckProof.Option.bind_congr'.h6.prem0)

-- Option.bind_congr', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.bind_congr'.h7 : ¬∀ {α β : Type} {f g : α → Option β} {x y : Option α}, x = y → x.bind f = y.bind g := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => none : ℕ → Option ℕ) (some : ℕ → Option ℕ) _ (Option.some 0) rfl) (by
  decide +kernel)

-- Finite.le_ciSup_of_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finite.le_ciSup_of_le.h7 : ¬∀ {α ι : Type} [inst : Finite ι] [inst : ConditionallyCompleteLattice α] {a : α} {f : ι → α} (c : ι), a ≤ iSup f := fun hc_h => absurd (@hc_h (ℕ) (Bool) _ (Nat.instConditionallyCompleteLinearOrderBot.toConditionallyCompleteLattice) (1) (fun _ => 0 : Bool → ℕ) (Bool.false)) (by
  simp)

-- List.not_lt_minimum_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_lt_minimum_of_mem.h6 : ¬∀ {α : Type} [inst : Preorder α] [inst_1 : DecidableLT α] {l : List α} {a m : α}, l.minimum = ↑m → ¬a < m := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Nat.decLt) ([1]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.not_lt_minimum_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_lt_minimum_of_mem.h7 : ¬∀ {α : Type} [inst : Preorder α] [inst_1 : DecidableLT α] {l : List α} {a m : α}, a ∈ l → ¬a < m := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (Nat.decLt) ([0]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.pair_sublist_insertionSort, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.pair_sublist_insertionSort.h7.inst : ¬[0, 1].Sublist (List.insertionSort (fun (a b : ℕ) => a < b) []) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.pair_sublist_insertionSort.h7.prem0 : (fun (a b : ℕ) => a < b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.pair_sublist_insertionSort.h7 : ¬∀ {α : Type} {r : α → α → Prop} [inst : DecidableRel r] {a b : α} {l : List α},
        r a b → [a, b].Sublist (List.insertionSort r l) := fun hc_h => HypCheckProof.List.pair_sublist_insertionSort.h7.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (Nat.decLt) (0) (1) ([]) HypCheckProof.List.pair_sublist_insertionSort.h7.prem0)

-- Set.LeftInvOn.surjOn, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.LeftInvOn.surjOn.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} {f' : β → α}, Set.MapsTo f s t → Set.SurjOn f' t s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Function.RightInverse.leftInverse_of_card_le, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.RightInverse.leftInverse_of_card_le.h6 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] {f : α → β} {g : β → α},
        Fintype.card β ≤ Fintype.card α → Function.LeftInverse f g := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.fintype) (Bool.fintype) (not : Bool → Bool) (fun _ => true : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Function.RightInverse.leftInverse_of_card_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.RightInverse.leftInverse_of_card_le.h7 : ¬∀ {α β : Type} [inst : Fintype α] [inst : Fintype β] {f : α → β} {g : β → α},
        Function.RightInverse f g → Function.LeftInverse f g := fun hc_h => absurd (@hc_h (Unit) (Bool) (PUnit.fintype) (Bool.fintype) (fun (a : Unit) => Bool.false) (fun (a : Bool) => PUnit.unit) (by
  decide)) (by
  decide +kernel)

-- List.prev_cons_cons_eq', hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.prev_cons_cons_eq'.h6.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y z : α), x = y → x ∈ y :: z :: l := by
  (intros; simp_all; done)
theorem HypCheckProof.List.prev_cons_cons_eq'.h6.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y z : α) (hx : x = y),
      (y :: z :: l).prev x (HypCheckProof.List.prev_cons_cons_eq'.h6.der l x y z hx) =
        (z :: l).getLast (List.cons_ne_nil z l) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @List.prev_cons_cons_eq' hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.List.prev_cons_cons_eq'.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6) hc_x6

-- List.prev_cons_cons_eq', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_cons_cons_eq'.h7 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (x y z : α) (h : x ∈ y :: z :: l),
        (y :: z :: l).prev x h = (z :: l).getLast (List.cons_ne_nil z l) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (instDecidableEqNat) ([]) (0) (1) (0) hc_k0) (by
  decide +kernel)

-- Commute.pow_eq_pow_iff_of_coprime, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Commute.pow_eq_pow_iff_of_coprime.h7 : ¬∀ {α : Type} [inst : GroupWithZero α] {a b : α} {m n : ℕ},
        Commute a b → (a ^ m = b ^ n ↔ ∃ (c : α), a = c ^ n ∧ b = c ^ m) := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield.toDivisionSemiring.toGroupWithZero) (0) (0) (0) (0) (by
  rfl)) (by
  simp)

-- Function.strictAnti_of_rightInverse, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.strictAnti_of_rightInverse.h6 : ¬∀ {α β : Type} [inst : Preorder α] [inst_1 : LinearOrder β] {φ : β → α} {ψ : α → β},
        Function.RightInverse ψ φ → StrictAnti ψ := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.instPartialOrder.toPreorder) (Nat.instLinearOrder) (fun n => n == 1 : ℕ → Bool) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  decide +kernel)

-- Function.strictAnti_of_rightInverse, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.strictAnti_of_rightInverse.h7 : ¬∀ {α β : Type} [inst : Preorder α] [inst_1 : LinearOrder β] {φ : β → α} {ψ : α → β}, StrictAnti φ → StrictAnti ψ := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.instPartialOrder.toPreorder) (Bool.linearOrder) (not : Bool → Bool) (fun _ => true : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Set.RightInvOn.eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.RightInvOn.eq.h5 : ¬∀ {α β : Type} {t : Set β} {f : α → β} {f' : β → α} {y : β}, y ∈ t → f (f' y) = y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- Function.strictMono_of_rightInverse, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.strictMono_of_rightInverse.h6 : ¬∀ {α β : Type} [inst : Preorder α] [inst_1 : LinearOrder β] {φ : β → α} {ψ : α → β},
        Function.RightInverse ψ φ → StrictMono ψ := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.instPartialOrder.toPreorder) (Bool.linearOrder) (not : Bool → Bool) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Function.strictMono_of_rightInverse, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.strictMono_of_rightInverse.h7 : ¬∀ {α β : Type} [inst : Preorder α] [inst_1 : LinearOrder β] {φ : β → α} {ψ : α → β}, StrictMono φ → StrictMono ψ := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool.instPartialOrder.toPreorder) (Bool.linearOrder) (fun b => b : Bool → Bool) (not : Bool → Bool) (by
  decide)) (by
  decide +kernel)

-- Set.MapsTo.congr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.congr.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f₁ f₂ : α → β}, Set.EqOn f₁ f₂ s → Set.MapsTo f₂ s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.MapsTo.congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.congr.h7 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f₁ f₂ : α → β}, Set.MapsTo f₁ s t → Set.MapsTo f₂ s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.bijOn_iUnion, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.bijOn_iUnion.h6 : ¬∀ {α β ι : Type} {s : ι → Set α} {t : ι → Set β} {f : α → β},
        Set.InjOn f (⋃ (i : ι), s i) → Set.BijOn f (⋃ (i : ι), s i) (⋃ (i : ι), t i) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- List.Perm.flatMap, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Perm.flatMap.h6.inst : ¬(List.flatMap (fun (x : ℕ) => []) []).Perm (List.flatMap (fun (n : ℕ) => [n]) [0]) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Perm.flatMap.h6.prem0 : ∀ a ∈ [], ((fun (x : ℕ) => []) a).Perm ((fun (n : ℕ) => [n]) a) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.Perm.flatMap.h6 : ¬∀ {α β : Type} {l₁ l₂ : List α} {f g : α → List β},
        (∀ a ∈ l₁, (f a).Perm (g a)) → (List.flatMap f l₁).Perm (List.flatMap g l₂) := fun hc_h => HypCheckProof.List.Perm.flatMap.h6.inst (@hc_h (ℕ) (ℕ) ([]) ([0]) (fun (x : ℕ) => []) (fun (n : ℕ) => [n]) HypCheckProof.List.Perm.flatMap.h6.prem0)

-- List.Perm.foldl_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.foldl_eq.h6 : ¬∀ {α β : Type} {f : β → α → β} {l₁ l₂ : List α} [rcomm : RightCommutative f] (b : β),
        List.foldl f b l₁ = List.foldl f b l₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ([]) ([1]) (@RightCommutative.mk (Nat) (Nat) (fun (a b : Nat) => @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) a b) (by (try dsimp only);   grind)) (1)) (by
  decide +kernel)

-- Set.RightInvOn.surjOn, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.RightInvOn.surjOn.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} {f' : β → α}, Set.MapsTo f' t s → Set.SurjOn f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.mk_mem_prod, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mk_mem_prod.h6 : ¬∀ {α β : Type} {a : α} {b : β} {s : Set α} {t : Set β}, b ∈ t → (a, b) ∈ s ×ˢ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (1) (0) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  decide)) (by
  decide +kernel)

-- Set.mk_mem_prod, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mk_mem_prod.h7 : ¬∀ {α β : Type} {a : α} {b : β} {s : Set α} {t : Set β}, a ∈ s → (a, b) ∈ s ×ˢ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) (1) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  decide)) (by
  decide +kernel)

-- List.le_max_of_le', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_max_of_le'.h6 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {a x : α} (b : α), a ≤ x → a ≤ List.foldr Max.max b l := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([]) (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.le_max_of_le', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_max_of_le'.h7 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {a x : α} (b : α), x ∈ l → a ≤ List.foldr Max.max b l := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([0]) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- List.Perm.kunion_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.kunion_left.h7 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] (l : List (Sigma β)) {l₁ l₂ : List (Sigma β)},
        l₁.NodupKeys → (l.kunion l₁).Perm (l.kunion l₂) := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) ([]) ([]) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)]) (by
  simp)) (by
  decide +kernel)

-- Set.EqOn.eq_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.eq_of_mem.h6 : ¬∀ {α β : Type} {s : Set α} {f₁ f₂ : α → β} {a : α}, a ∈ s → f₁ a = f₂ a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (0) (by
  decide)) (by
  decide +kernel)

-- Set.EqOn.eq_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.eq_of_mem.h7 : ¬∀ {α β : Type} {s : Set α} {f₁ f₂ : α → β} {a : α}, Set.EqOn f₁ f₂ s → f₁ a = f₂ a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (0) (by
  simp)) (by
  decide +kernel)

-- Set.MapsTo.mem_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.mem_iff.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.MapsTo f sᶜ tᶜ → ∀ {x : α}, f x ∈ t ↔ x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ) (by
  simp) (0)) (by
  decide +kernel)

-- Set.MapsTo.mem_iff, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.mem_iff.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.MapsTo f s t → ∀ {x : α}, f x ∈ t ↔ x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (by
  simp) (1)) (by
  decide +kernel)

-- List.length_destutter'_cotrans_ge, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.length_destutter'_cotrans_ge.h4.inst : ¬(List.destutter' (fun (a b : ℕ) => a = b) 0 [0]).length ≤ (List.destutter' (fun (a b : ℕ) => a = b) 1 [0]).length := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.length_destutter'_cotrans_ge.h4.prem0 : ¬(fun (a b : ℕ) => a = b) 0 1 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.length_destutter'_cotrans_ge.h4 : ¬∀ {α : Type} {R : α → α → Prop} [inst : DecidableRel R] {b a : α} {l : List α},
        ¬R b a → (List.destutter' R b l).length ≤ (List.destutter' R a l).length := fun hc_h => HypCheckProof.List.length_destutter'_cotrans_ge.h4.inst (@hc_h (ℕ) (fun (a b : ℕ) => a = b) (instDecidableEqNat) (0) (1) ([0]) HypCheckProof.List.length_destutter'_cotrans_ge.h4.prem0)

-- List.length_destutter'_cotrans_ge, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_destutter'_cotrans_ge.h7 : ¬∀ {α : Type} {R : α → α → Prop} [inst : DecidableRel R] {b : α} [i : IsTrans α Rᶜ] {a : α} {l : List α},
        (List.destutter' R b l).length ≤ (List.destutter' R a l).length := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) (0) (@IsTrans.mk (Nat) (@Compl.compl (Nat → Nat → Prop)
      (@Pi.instCompl Nat (fun (a : Nat) => Nat → Prop) fun (i : Nat) =>
        @Pi.instCompl Nat (fun (a : Nat) => Prop) fun (i : Nat) => «Prop».instCompl)
      fun (a b : Nat) => @LT.lt Nat instLTNat a b) (by (try dsimp only);   (intros; simp_all <;> omega))) (1) ([1])) (by
  decide +kernel)

-- Set.SurjOn.congr, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.congr.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f₁ f₂ : α → β}, Set.EqOn f₁ f₂ s → Set.SurjOn f₂ s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.SurjOn.congr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.congr.h7 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f₁ f₂ : α → β}, Set.SurjOn f₁ s t → Set.SurjOn f₂ s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- List.signVariations_cons_cons_of_ne_zero, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.signVariations_cons_cons_of_ne_zero.h6 : ¬∀ {α : Type} [inst : Zero α] [inst_1 : LinearOrder α] {a b : α} (as : List α),
        b ≠ 0 →
          (a :: b :: as).signVariations = (b :: as).signVariations + if SignType.sign a = SignType.sign b then 0 else 1 := fun hc_h => absurd (@hc_h (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instLinearOrder) (0) (1) ([]) (by
  decide)) (by
  decide +kernel)

-- List.signVariations_cons_cons_of_ne_zero, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.signVariations_cons_cons_of_ne_zero.h7 : ¬∀ {α : Type} [inst : Zero α] [inst_1 : LinearOrder α] {a b : α} (as : List α),
        a ≠ 0 →
          (a :: b :: as).signVariations = (b :: as).signVariations + if SignType.sign a = SignType.sign b then 0 else 1 := fun hc_h => absurd (@hc_h (ℕ) (Nat.instMulZeroClass.toZero) (Nat.instLinearOrder) (1) (0) ([]) (by
  decide)) (by
  decide +kernel)

-- PEquiv.single_mul_single_of_ne, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PEquiv.single_mul_single_of_ne.h11 : Not
      (∀ {k m n α : Type} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : DecidableEq k] [inst_3 : DecidableEq m]
        [inst_4 : NonAssocSemiring α] {b₁ b₂ : n} (a : m) (c : k),
        @Eq (Matrix m k α)
          (@HMul.hMul (Matrix m n α) (Matrix n k α) (Matrix m k α)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid m n k α inst
              (@Distrib.toMul α
                (@NonUnitalNonAssocSemiring.toDistrib α (@NonAssocSemiring.toNonUnitalNonAssocSemiring α inst_4)))
              (@NonUnitalNonAssocSemiring.toAddCommMonoid α (@NonAssocSemiring.toNonUnitalNonAssocSemiring α inst_4)))
            (@PEquiv.toMatrix m n α inst_1
              (@MulZeroClass.toZero α
                (@NonUnitalNonAssocSemiring.toMulZeroClass α (@NonAssocSemiring.toNonUnitalNonAssocSemiring α inst_4)))
              (@AddMonoidWithOne.toOne α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α (@NonAssocSemiring.toAddCommMonoidWithOne α inst_4)))
              (@PEquiv.single m n inst_3 inst_1 a b₁))
            (@PEquiv.toMatrix n k α inst_2
              (@MulZeroClass.toZero α
                (@NonUnitalNonAssocSemiring.toMulZeroClass α (@NonAssocSemiring.toNonUnitalNonAssocSemiring α inst_4)))
              (@AddMonoidWithOne.toOne α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α (@NonAssocSemiring.toAddCommMonoidWithOne α inst_4)))
              (@PEquiv.single n k inst_1 inst_2 b₂ c)))
          (@OfNat.ofNat (Matrix m k α) (nat_lit 0)
            (@Zero.toOfNat0 (Matrix m k α)
              (@Matrix.zero m k α
                (@MulZeroClass.toZero α
                  (@NonUnitalNonAssocSemiring.toMulZeroClass α
                    (@NonAssocSemiring.toNonUnitalNonAssocSemiring α inst_4))))))) := fun hc_h => absurd (@hc_h (Bool) (Bool) (Bool) (Nat) (Bool.fintype) (instDecidableEqBool) (instDecidableEqBool) (instDecidableEqBool) (Nat.instNonAssocSemiring) (Bool.false) (Bool.false) (Bool.false) (Bool.false)) (by
  decide +kernel)

-- Int.log_zpow, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.log_zpow.h6 : Not
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
          (@Int.log R inst inst_1 inst_2 b
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

-- Int.clog_of_right_le_zero, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.clog_of_right_le_zero.h7 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] [inst_3 : IsStrictOrderedRing R]
        (b : ℕ) {r : R}, Int.clog b r = 0 := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) _ (2) (1 / 2)) (by
  decide +kernel)

-- Set.sups_subset, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sups_subset.h6 : Not
      (∀ {α : Type} [inst : SemilatticeSup α] {s₁ s₂ t₁ t₂ : Set α},
        @LE.le (Set α) (@Set.instLE α) t₁ t₂ →
          @LE.le (Set α) (@Set.instLE α) (@HasSups.sups (Set α) (@Set.hasSups α inst) s₁ t₁)
            (@HasSups.sups (Set α) (@Set.hasSups α inst) s₂ t₂)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (x : Nat) => False) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  rfl)) (by
  simp)

-- Set.sups_subset, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sups_subset.h7 : Not
      (∀ {α : Type} [inst : SemilatticeSup α] {s₁ s₂ t₁ t₂ : Set α},
        @LE.le (Set α) (@Set.instLE α) s₁ s₂ →
          @LE.le (Set α) (@Set.instLE α) (@HasSups.sups (Set α) (@Set.hasSups α inst) s₁ t₁)
            (@HasSups.sups (Set α) (@Set.hasSups α inst) s₂ t₂)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (x : Nat) => False) (by
  rfl)) (by
  simp)

-- Set.LeftInvOn.image_image', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.LeftInvOn.image_image'.h6 : ¬∀ {α β : Type} {s s₁ : Set α} {f : α → β} {f' : β → α}, s₁ ⊆ s → f' '' f '' s₁ = s₁ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (by
  rfl)) (by
  simp)

-- List.kreplace_self, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.kreplace_self.h7 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {b : β a} {l : List (Sigma β)},
        l.NodupKeys → List.kreplace a b l = l := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) (1) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)]) (by
  simp)) (by
  decide +kernel)

-- List.perm_dlookup, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.perm_dlookup.h7 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] (a : α) {l₁ l₂ : List (Sigma β)},
        l₁.NodupKeys → List.dlookup a l₁ = List.dlookup a l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ([]) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)]) (by
  simp)) (by
  decide +kernel)

-- Part.add_mem_add, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.add_mem_add.h6 : ¬∀ {α : Type} [inst : Add α] (a b : Part α) (ma mb : α), mb ∈ b → ma + mb ∈ a + b := fun hc_h => absurd (@hc_h (ℕ) (instAddNat) (0) (0) (1) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.add_mem_add, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.add_mem_add.h7 : ¬∀ {α : Type} [inst : Add α] (a b : Part α) (ma mb : α), ma ∈ a → ma + mb ∈ a + b := fun hc_h => absurd (@hc_h (ℕ) (instAddNat) (0) (0) (0) (1) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.sub_mem_sub, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.sub_mem_sub.h6 : ¬∀ {α : Type} [inst : Sub α] (a b : Part α) (ma mb : α), mb ∈ b → ma - mb ∈ a - b := fun hc_h => absurd (@hc_h (ℕ) (instSubNat) (0) (0) (1) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.sub_mem_sub, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.sub_mem_sub.h7 : ¬∀ {α : Type} [inst : Sub α] (a b : Part α) (ma mb : α), ma ∈ a → ma - mb ∈ a - b := fun hc_h => absurd (@hc_h (ℕ) (instSubNat) (0) (⊥) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Set.BijOn.insert_iff, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.BijOn.insert_iff.h6.inst : ¬(Set.BijOn (fun (n : ℕ) => n + 1) (Insert.insert 0 {n : ℕ | n = 0})
          (Insert.insert ((fun (n : ℕ) => n + 1) 0) {x : ℕ | False}) ↔
        Set.BijOn (fun (n : ℕ) => n + 1) {n : ℕ | n = 0} {x : ℕ | False}) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Set.BijOn.insert_iff.h6.prem0 : (fun (n : ℕ) => n + 1) 0 ∉ {x : ℕ | False} := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Set.BijOn.insert_iff.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} {a : α},
        f a ∉ t → (Set.BijOn f (Insert.insert a s) (Insert.insert (f a) t) ↔ Set.BijOn f s t) := fun hc_h => HypCheckProof.Set.BijOn.insert_iff.h6.inst (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (fun (n : ℕ) => n + 1) (0) HypCheckProof.Set.BijOn.insert_iff.h6.prem0)

-- Part.mem_bind, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.mem_bind.h6 : ¬∀ {α β : Type} {f : Part α} {g : α → Part β} {a : α} {b : β}, b ∈ g a → b ∈ f.bind g := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (⊥) (fun (a : ℕ) => 0) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.mem_bind, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.mem_bind.h7 : ¬∀ {α β : Type} {f : Part α} {g : α → Part β} {a : α} {b : β}, a ∈ f → b ∈ f.bind g := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) (fun (a : ℕ) => 0) (0) (1) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.inter_mem_inter, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.inter_mem_inter.h6 : ¬∀ {α : Type} [inst : Inter α] (a b : Part α) (ma mb : α), mb ∈ b → ma ∩ mb ∈ a ∩ b := fun hc_h => absurd (@hc_h (Multiset ℕ) (Multiset.instInter) (⊥) (0) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.inter_mem_inter, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.inter_mem_inter.h7 : ¬∀ {α : Type} [inst : Inter α] (a b : Part α) (ma mb : α), ma ∈ a → ma ∩ mb ∈ a ∩ b := fun hc_h => absurd (@hc_h (Multiset ℕ) (Multiset.instInter) (0) (⊥) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.mul_mem_mul, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.mul_mem_mul.h6 : ¬∀ {α : Type} [inst : Mul α] (a b : Part α) (ma mb : α), mb ∈ b → ma * mb ∈ a * b := fun hc_h => absurd (@hc_h (ℕ) (instMulNat) (⊥) (0) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.mul_mem_mul, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.mul_mem_mul.h7 : ¬∀ {α : Type} [inst : Mul α] (a b : Part α) (ma mb : α), ma ∈ a → ma * mb ∈ a * b := fun hc_h => absurd (@hc_h (ℕ) (instMulNat) (0) (⊥) (0) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Nat.Prime.dvd_choose_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose_pow.h3 : ¬∀ {p n k : ℕ}, k ≠ 0 → k ≠ p ^ n → p ∣ (p ^ n).choose k := fun hc_h => absurd (@hc_h (4) (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_choose_pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose_pow.h4 : ¬∀ {p n k : ℕ}, Nat.Prime p → k ≠ p ^ n → p ∣ (p ^ n).choose k := fun hc_h => absurd (@hc_h (2) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_choose_pow, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose_pow.h5 : ¬∀ {p n k : ℕ}, Nat.Prime p → k ≠ 0 → p ∣ (p ^ n).choose k := fun hc_h => absurd (@hc_h (2) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.emultiplicity_eq_card_pow_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.emultiplicity_eq_card_pow_dvd.h3 : ¬∀ {m n b : ℕ}, 0 < n → Nat.log m n < b → emultiplicity m n = ↑{i ∈ Finset.Ico 1 b | m ^ i ∣ n}.card := fun hc_h => absurd (@hc_h (1) (1) (1) (by
  decide) (by
  decide)) (by
  simp)

-- Nat.emultiplicity_eq_card_pow_dvd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.emultiplicity_eq_card_pow_dvd.h4 : ¬∀ {m n b : ℕ}, m ≠ 1 → Nat.log m n < b → emultiplicity m n = ↑{i ∈ Finset.Ico 1 b | m ^ i ∣ n}.card := fun hc_h => absurd (@hc_h (2) (0) (1) (by
  decide) (by
  decide)) (by
  simp)

-- Function.Injective.invFun_restrict, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.invFun_restrict.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst : DecidableEq β] {f : α → β} [inst : Nonempty α], Function.Injective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (instDecidableEqNat) (fun _ => 0 : Bool → ℕ) _) (by
  decide +kernel)

-- List.eq_of_tail_eq_of_dropLast_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.eq_of_tail_eq_of_dropLast_eq.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.tail = l₂.tail → l₁.dropLast = l₂.dropLast → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.eq_of_tail_eq_of_dropLast_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.eq_of_tail_eq_of_dropLast_eq.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, 1 < l₁.length → l₁.dropLast = l₂.dropLast → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) ([0, 0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.eq_of_tail_eq_of_dropLast_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.eq_of_tail_eq_of_dropLast_eq.h5 : ¬∀ {α : Type} {l₁ l₂ : List α}, 1 < l₁.length → l₁.tail = l₂.tail → l₁ = l₂ := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) ([0, 0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.forall₂_of_length_eq_of_get, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.forall₂_of_length_eq_of_get.h5.inst : ¬List.Forall₂ (fun (a b : ℕ) => a < b) [] [0] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.forall₂_of_length_eq_of_get.h5.prem0 : ∀ (i : ℕ) (h₁ : i < [].length) (h₂ : i < [0].length),
      (fun (a b : ℕ) => a < b) ([].get (⟨i, h₁⟩ : Fin [].length)) ([0].get (⟨i, h₂⟩ : Fin [0].length)) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.forall₂_of_length_eq_of_get.h5 : ¬∀ {α β : Type} {R : α → β → Prop} {x : List α} {y : List β},
        (∀ (i : ℕ) (h₁ : i < x.length) (h₂ : i < y.length),
            R (x.get (⟨i, h₁⟩ : Fin x.length)) (y.get (⟨i, h₂⟩ : Fin y.length))) →
          List.Forall₂ R x y := fun hc_h => HypCheckProof.List.forall₂_of_length_eq_of_get.h5.inst (@hc_h (ℕ) (ℕ) (fun (a b : ℕ) => a < b) ([]) ([0]) HypCheckProof.List.forall₂_of_length_eq_of_get.h5.prem0)

-- List.forall₂_of_length_eq_of_get, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forall₂_of_length_eq_of_get.h6 : ¬∀ {α β : Type} {R : α → β → Prop} {x : List α} {y : List β}, x.length = y.length → List.Forall₂ R x y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0]) ([0]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Set.Finite.eq_of_subset_of_encard_le', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.eq_of_subset_of_encard_le'.h4 : ¬∀ {α : Type} {s t : Set α}, t.Finite → t.encard ≤ s.encard → s = t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (by
  simp)) (by
  simp)

-- Set.Finite.eq_of_subset_of_encard_le', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.eq_of_subset_of_encard_le'.h5 : ¬∀ {α : Type} {s t : Set α}, t.Finite → s ⊆ t → s = t := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp) (by
  simp)) (by
  simp)

-- List.getElem_insertIdx_add_succ, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_insertIdx_add_succ.h5 : ¬∀ {α : Type} (l : List α) (x : α) (n k : ℕ), n + k < l.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (0) (0)) (by
  decide +kernel)

-- List.getElem_insertIdx_add_succ, hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.getElem_insertIdx_add_succ.h6.der.{u} : ∀ {α : Type u} (l : List α) (x : α) (n k : Nat),
      @LT.lt Nat instLTNat (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n k) (@List.length α l) →
        @LT.lt Nat instLTNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n k)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@List.length α (@List.insertIdx α l n x)) := by
  (intros; grind)
theorem HypCheckProof.List.getElem_insertIdx_add_succ.h6.{u} : ∀ {α : Type u} (l : List α) (x : α) (n k : Nat)
      (hk' : @LT.lt Nat instLTNat (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n k) (@List.length α l)),
      @Eq α
        (@GetElem.getElem (List α) Nat α (fun (as : List α) (i : Nat) => @LT.lt Nat instLTNat i (@List.length α as))
          (@List.instGetElemNatLtLength α) (@List.insertIdx α l n x)
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n k)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HypCheckProof.List.getElem_insertIdx_add_succ.h6.der α l x n k hk'))
        (@GetElem.getElem (List α) Nat α (fun (as : List α) (i : Nat) => @LT.lt Nat instLTNat i (@List.length α as))
          (@List.instGetElemNatLtLength α) l (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n k) hk') := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @List.getElem_insertIdx_add_succ hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.List.getElem_insertIdx_add_succ.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- EReal.toReal_sub, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toReal_sub.h3 : ¬∀ {x y : EReal}, x ≠ ⊤ → y ≠ ⊤ → y ≠ ⊥ → (x - y).toReal = x.toReal - y.toReal := fun hc_h => absurd (@hc_h (⊥) (1) (by
  decide) (by
  decide) (by
  decide)) (by
  simp)

-- EReal.toReal_sub, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toReal_sub.h4 : ¬∀ {x y : EReal}, x ≠ ⊤ → x ≠ ⊥ → y ≠ ⊥ → (x - y).toReal = x.toReal - y.toReal := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide) (by
  decide) (by
  decide)) (by
  simp)

-- Set.preimage_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.preimage_subset.h5 : ¬∀ {α β : Type} {f : α → β} {s : Set β} {t : Set α}, Set.InjOn f (f ⁻¹' s) → f ⁻¹' s ⊆ t := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) ({n : ℕ | n = 0}) ({b : Bool | b = Bool.true}) (by
  simp)) (by
  simp)

-- Nat.one_div_lt_one_div, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.one_div_lt_one_div.h6 : Not
      (∀ {α : Type} [inst : Semifield α] [inst_1 : LinearOrder α]
        [inst_2 :
          @IsStrictOrderedRing α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))
            (@SemilatticeInf.toPartialOrder α
              (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))]
        {n m : Nat},
        @LT.lt α
          (@Preorder.toLT α
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
                          (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))))))) := fun hc_h => absurd (@hc_h (Rat) (@Field.toSemifield Rat Rat.instField) (Rat.linearOrder) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- EReal.mul_le_of_forall_lt_of_nonneg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.mul_le_of_forall_lt_of_nonneg.h4 : ¬∀ {a b c : EReal}, 0 ≤ a → (∀ a' ∈ Set.Ioo 0 a, ∀ b' ∈ Set.Ioo 0 b, a' * b' ≤ c) → a * b ≤ c := fun hc_h => absurd (@hc_h (0) (0) (⊥) (by
  rfl) (by
  simp)) (by
  decide +kernel)

-- EReal.mul_le_of_forall_lt_of_nonneg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.mul_le_of_forall_lt_of_nonneg.h5 : ¬∀ {a b c : EReal}, 0 ≤ a → 0 ≤ c → a * b ≤ c := fun hc_h => absurd (@hc_h (1) (1) (0) (by
  simp) (by
  rfl)) (by
  simp)

-- EReal.div_lt_div_right_of_neg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_lt_div_right_of_neg.h3 : ¬∀ {a b c : EReal}, c ≠ ⊥ → a < b → b / c < a / c := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide) (by
  simp)) (by
  simp)

-- Set.ncard_union_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_union_eq.h3 : ¬∀ {α : Type} {s t : Set α},
        autoParam s.Finite Set.ncard_union_eq._auto_1 →
          autoParam t.Finite Set.ncard_union_eq._auto_3 → (s ∪ t).ncard = s.ncard + t.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp) (by
  simp)) (by
  simp)

-- Set.SurjOn.image_eq_of_mapsTo, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.image_eq_of_mapsTo.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.MapsTo f s t → f '' s = t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | True}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Function.Semiconj.surjOn_range, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Semiconj.surjOn_range.h5 : ¬∀ {α β : Type} {fa : α → α} {fb : β → β} {f : α → β},
        Function.Surjective fa → Set.SurjOn fb (Set.range f) (Set.range f) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (not : Bool → Bool) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : Bool → ℕ) (by
  decide)) (by
  simp)

-- Nat.decreasingInduction_succ_left, hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Nat.decreasingInduction_succ_left.h6.der.{u_1} : ∀ {m n : Nat} {motive : (m : Nat) → @LE.le Nat instLENat m n → Sort u_1}
      (of_succ :
        (k : Nat) →
          (h : @LT.lt Nat instLTNat k n) →
            motive
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                h →
              motive k (@Nat.le_of_succ_le k n h))
      (self : motive n (Nat.le_refl n)),
      @LE.le Nat instLENat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          n →
        @LE.le Nat instLENat m n := by
  (intros; lia)
theorem HypCheckProof.Nat.decreasingInduction_succ_left.h6.{u_1} : ∀ {m n : Nat} {motive : (m : Nat) → @LE.le Nat instLENat m n → Sort u_1}
      (of_succ :
        (k : Nat) →
          (h : @LT.lt Nat instLTNat k n) →
            motive
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                h →
              motive k (@Nat.le_of_succ_le k n h))
      (self : motive n (Nat.le_refl n))
      (smn :
        @LE.le Nat instLENat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          n),
      @Eq (motive m (@HypCheckProof.Nat.decreasingInduction_succ_left.h6.der m n motive of_succ self smn))
        (@Nat.decreasingInduction n motive of_succ self m
          (@HypCheckProof.Nat.decreasingInduction_succ_left.h6.der m n motive of_succ self smn))
        (of_succ m smn
          (@Nat.decreasingInduction n (fun (x : Nat) (x_1 : @LE.le Nat instLENat x n) => motive x x_1) of_succ self
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            smn)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Nat.decreasingInduction_succ_left hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Nat.decreasingInduction_succ_left.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Set.InjOn.exists_subset_injOn_subset_range_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.InjOn.exists_subset_injOn_subset_range_eq.h6 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {r : Set α},
        Set.InjOn f r → ∃ (u : Set α), r ⊆ u ∧ u ⊆ s ∧ f '' u = f '' s ∧ Set.InjOn f u := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- List.Subperm.map, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.map.h6 : ¬∀ {α β : Type} {l₁ l₂ : List α} {f : α → β}, Function.Injective f → (List.map f l₁).Subperm (List.map f l₂) := fun hc_h => absurd (@hc_h (Bool) (ℕ) ([Bool.false]) ([]) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  decide +kernel)

-- WellFounded.asymmetricₙ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WellFounded.asymmetricₙ.h3 : ¬∀ {α : Type} {r : α → α → Prop} {l : List α} (hne : l ≠ []), List.IsChain r l → ¬r (l.getLast hne) (l.head hne) := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ([0]) hc_k0 hc_k1) (by
  decide +kernel)

-- Nat.set_induction_bounded, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.set_induction_bounded.h3 : ¬∀ {n k : ℕ} {S : Set ℕ}, (∀ k ∈ S, k + 1 ∈ S) → k ≤ n → n ∈ S := fun hc_h => absurd (@hc_h (0) (0) ({x : ℕ | False}) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- Nat.set_induction_bounded, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.set_induction_bounded.h4 : ¬∀ {n k : ℕ} {S : Set ℕ}, k ∈ S → k ≤ n → n ∈ S := fun hc_h => absurd (@hc_h (1) (0) ({n : ℕ | n = 0}) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.le_maximum_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_maximum_of_mem.h5 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {a m : α}, l.maximum = ↑m → a ≤ m := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([0]) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.le_maximum_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_maximum_of_mem.h6 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {a m : α}, a ∈ l → a ≤ m := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([1]) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.minimum_le_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minimum_le_of_mem.h5 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {a m : α}, l.minimum = ↑m → m ≤ a := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([1]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.minimum_le_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minimum_le_of_mem.h6 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {a m : α}, a ∈ l → m ≤ a := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([0]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.sublist_insertionSort, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sublist_insertionSort.h6 : ¬∀ {α : Type} {r : α → α → Prop} [inst : DecidableRel r] {l c : List α},
        List.Pairwise r c → c.Sublist (List.insertionSort r l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.append, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.append.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₂.Nodup → l₁.Disjoint l₂ → (l₁ ++ l₂).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) ([]) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- List.Nodup.append, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.append.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.Nodup → l₁.Disjoint l₂ → (l₁ ++ l₂).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0, 0]) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- List.Nodup.append, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.append.h5 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.Nodup → l₂.Nodup → (l₁ ++ l₂).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Set.inter_eq_inter_mono_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_eq_inter_mono_left.h5 : ¬∀ {α : Type} {t u s₁ s₂ : Set α}, s₂ ⊆ s₁ → s₂ ∩ t = s₂ ∩ u := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- pairwiseDisjoint_unique, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.pairwiseDisjoint_unique.h6 : ¬∀ {α ι : Type} {f : ι → Set α} {s : Set ι} {y : α}, s.PairwiseDisjoint f → ∃! i : ι, i ∈ s ∧ y ∈ f i := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => {n : ℕ | n = 0}) ({n : ℕ | n = 0}) (1) (by
  simp)) (by
  simp)

-- Set.union_subset_union, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.union_subset_union.h5 : ¬∀ {α : Type} {s₁ s₂ t₁ t₂ : Set α}, t₁ ⊆ t₂ → s₁ ∪ t₁ ⊆ s₂ ∪ t₂ := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  rfl)) (by
  simp)

-- Set.union_subset_union, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.union_subset_union.h6 : ¬∀ {α : Type} {s₁ s₂ t₁ t₂ : Set α}, s₁ ⊆ s₂ → s₁ ∪ t₁ ⊆ s₂ ∪ t₂ := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) (by
  rfl)) (by
  simp)

-- Set.Finite.bddAbove, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.bddAbove.h5 : ¬∀ {α : Type} [inst : Preorder α] [inst_1 : IsDirectedOrder α] [inst_2 : Nonempty α] {s : Set α}, BddAbove s := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) _ _ ({x : ℕ | True})) (by
  simp)

-- Set.infinite_of_not_bddBelow, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infinite_of_not_bddBelow.h5 : ¬∀ {α : Type} [inst : Preorder α] [inst : IsCodirectedOrder α] [inst : Nonempty α] {s : Set α}, s.Infinite := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) _ _ ({n : ℕ | n = 0})) (by
  simp)

-- Set.MapsTo.nonempty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.nonempty.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, s.Nonempty → t.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.exists_ne_map_eq_of_encard_lt_of_maps_to, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_ne_map_eq_of_encard_lt_of_maps_to.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.MapsTo f s t → ∃ a₁ ∈ s, ∃ a₂ ∈ s, a₁ ≠ a₂ ∧ f a₁ = f a₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.exists_ne_map_eq_of_encard_lt_of_maps_to, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_ne_map_eq_of_encard_lt_of_maps_to.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, t.encard < s.encard → ∃ a₁ ∈ s, ∃ a₂ ∈ s, a₁ ≠ a₂ ∧ f a₁ = f a₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.Finite.eq_of_subset_of_encard_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.eq_of_subset_of_encard_le.h4 : ¬∀ {α : Type} {s t : Set α}, s.Finite → t.encard ≤ s.encard → s = t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp) (by
  simp)) (by
  simp)

-- Set.Finite.eq_of_subset_of_encard_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.eq_of_subset_of_encard_le.h5 : ¬∀ {α : Type} {s t : Set α}, s.Finite → s ⊆ t → s = t := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp) (by
  simp)) (by
  simp)

-- List.prev_cons_cons_of_ne, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.prev_cons_cons_of_ne.h5.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y : α), x ≠ y → x ∈ y :: x :: l := by
  (intros; solve_by_elim)
theorem HypCheckProof.List.prev_cons_cons_of_ne.h5.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x y : α) (hy : x ≠ y),
      (y :: x :: l).prev x (HypCheckProof.List.prev_cons_cons_of_ne.h5.der l x y hy) = y := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @List.prev_cons_cons_of_ne hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.List.prev_cons_cons_of_ne.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x5

-- List.prev_cons_cons_of_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_cons_cons_of_ne.h6 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (x y : α) (h : x ∈ y :: x :: l), (y :: x :: l).prev x h = y := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (instDecidableEqNat) ([1]) (0) (0) hc_k0) (by
  decide +kernel)

-- Nat.clog.go_spec, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog.go_spec.h3 : ¬∀ {n b fuel : ℕ},
        1 < b →
          n < b ^ fuel →
            (Nat.clog.go n b fuel).1 = b ^ ((Nat.clog.go n b fuel).2 + 1) / n ∧
              b ^ (Nat.clog.go n b fuel).2 < n ∧ n ≤ b ^ ((Nat.clog.go n b fuel).2 + 1) := fun hc_h => absurd (@hc_h (0) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.clog.go_spec, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog.go_spec.h5 : ¬∀ {n b fuel : ℕ},
        1 < n →
          1 < b →
            (Nat.clog.go n b fuel).1 = b ^ ((Nat.clog.go n b fuel).2 + 1) / n ∧
              b ^ (Nat.clog.go n b fuel).2 < n ∧ n ≤ b ^ ((Nat.clog.go n b fuel).2 + 1) := fun hc_h => absurd (@hc_h (3) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.next_cons_eq_next_of_mem_dropLast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_cons_eq_next_of_mem_dropLast.h4 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (x y : α), x ≠ y → x ∈ l.dropLast := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.next_cons_eq_next_of_mem_dropLast, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_cons_eq_next_of_mem_dropLast.h6 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (x : α) (h : x ∈ l.dropLast) (y : α),
        (y :: l).next x (List.mem_cons_of_mem y (List.mem_of_mem_dropLast h)) = l.next x (List.mem_of_mem_dropLast h) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (instDecidableEqNat) ([0, 1]) (0) hc_k0 (0)) (by
  decide +kernel)

-- List.mem_inter_of_mem_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_inter_of_mem_of_mem.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} {a : α} [inst : DecidableEq α], a ∈ l₂ → a ∈ l₁ ∩ l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (0) (instDecidableEqNat) (by
  decide)) (by
  decide +kernel)

-- List.mem_inter_of_mem_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_inter_of_mem_of_mem.h6 : ¬∀ {α : Type} {l₁ l₂ : List α} {a : α} [inst : DecidableEq α], a ∈ l₁ → a ∈ l₁ ∩ l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (0) (instDecidableEqNat) (by
  decide)) (by
  decide +kernel)

-- Set.Finite.eq_insert_of_subset_of_encard_eq_succ, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.eq_insert_of_subset_of_encard_eq_succ.h5 : ¬∀ {α : Type} {s t : Set α}, s.Finite → s ⊆ t → ∃ (a : α), t = Insert.insert a s := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({x : ℕ | False}) (by
  simp) (by
  rfl)) (by
  simp)

-- List.Perm.drop_inter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.drop_inter.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {xs ys : List α} (n : ℕ), ys.Nodup → (List.drop n xs).Perm (ys ∩ List.drop n xs) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([]) (0) (by
  decide)) (by
  decide +kernel)

-- Set.Finite.toFinset_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.toFinset_mono.h5 : ¬∀ {α : Type} {s t : Set α} {hs : s.Finite} {ht : t.Finite}, hs.toFinset ⊆ ht.toFinset := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) hc_k0 hc_k1) (by
  (simp <;> decide))

-- Set.Finite.toFinset_strictMono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.toFinset_strictMono.h5 : ¬∀ {α : Type} {s t : Set α} {hs : s.Finite} {ht : t.Finite}, hs.toFinset ⊂ ht.toFinset := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) hc_k0 hc_k1) (by
  simp)

-- Set.image_image2_antidistrib_right, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_image2_antidistrib_right.h11 : ¬∀ {α α' β γ δ : Type} {f : α → β → γ} {s : Set α} {t : Set β} {g : γ → δ} {f' : β → α' → δ} {g' : α → α'},
        g '' Set.image2 f s t = Set.image2 f' t (g' '' s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Set.image_image2_antidistrib_left, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_image2_antidistrib_left.h11 : ¬∀ {α β β' γ δ : Type} {f : α → β → γ} {s : Set α} {t : Set β} {g : γ → δ} {f' : β' → α → δ} {g' : β → β'},
        g '' Set.image2 f s t = Set.image2 f' (g' '' t) s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Nat.lt_of_testBit, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_of_testBit.h3 : ¬∀ {n m : ℕ} (i : ℕ), m.testBit i = Bool.true → (∀ (j : ℕ), i < j → n.testBit j = m.testBit j) → n < m := fun hc_h => absurd (@hc_h (1) (1) (0) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Nat.lt_of_testBit, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_of_testBit.h4 : ¬∀ {n m : ℕ} (i : ℕ), n.testBit i = Bool.false → (∀ (j : ℕ), i < j → n.testBit j = m.testBit j) → n < m := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Nat.lt_of_testBit, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_of_testBit.h5 : ¬∀ {n m : ℕ} (i : ℕ), n.testBit i = Bool.false → m.testBit i = Bool.true → n < m := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.bitwise_bit', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bitwise_bit'.h5 : ¬∀ {f : Bool → Bool → Bool} (a : Bool) (m : ℕ) (b : Bool) (n : ℕ),
        (n = 0 → b = Bool.true) → Nat.bitwise f (Nat.bit a m) (Nat.bit b n) = Nat.bit (f a b) (Nat.bitwise f m n) := fun hc_h => absurd (@hc_h (fun a b => !a || b : Bool → Bool → Bool) (Bool.false) (0) (Bool.false) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.bitwise_bit', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bitwise_bit'.h6 : ¬∀ {f : Bool → Bool → Bool} (a : Bool) (m : ℕ) (b : Bool) (n : ℕ),
        (m = 0 → a = Bool.true) → Nat.bitwise f (Nat.bit a m) (Nat.bit b n) = Nat.bit (f a b) (Nat.bitwise f m n) := fun hc_h => absurd (@hc_h (fun a b => !a || b : Bool → Bool → Bool) (Bool.false) (1) (Bool.false) (0) (by
  decide)) (by
  decide +kernel)

-- Multiset.sort_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.sort_zero.h4 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r], Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide))) (by
  exact fun hc_c =>
    absurd
      (hc_c.antisymm (Bool.false : Bool) (Bool.true : Bool)
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

-- Multiset.sort_zero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.sort_zero.h5 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r], Std.Total r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.NodupKeys.map₁, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.NodupKeys.map₁.h4 : Not
      (∀ {α α' β : Type} (f : α → α') {l : List (@Sigma α fun (x : α) => β)},
        @List.NodupKeys α (fun (x : α) => β) l →
          @List.NodupKeys α' (fun (x : α') => β)
            (@List.map (@Sigma α fun (x : α) => β) (@Sigma α' fun (x : α') => β)
              (@Sigma.map α α' (fun (x : α) => β) (fun (x : α') => β) f fun (x : α) => @id β) l)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (Nat) (fun _ => 0 : Nat → Nat) (@List.cons (@Sigma Nat fun (x : Nat) => Nat)
      (@Sigma.mk Nat (fun (x : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.cons (@Sigma Nat fun (x : Nat) => Nat)
        (@Sigma.mk Nat (fun (x : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@List.nil (@Sigma Nat fun (x : Nat) => Nat)))) (by
  simp)) (by
  (simp <;> decide))

-- List.relationReflTransGen_of_exists_isChain_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.relationReflTransGen_of_exists_isChain_cons.h5 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (l : List α),
        (a :: l).getLast (List.cons_ne_nil a l) = b → Relation.ReflTransGen r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) _ ([0]) rfl) (by
  nofun)

-- List.relationReflTransGen_of_exists_isChain_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.relationReflTransGen_of_exists_isChain_cons.h6 : ¬∀ {α : Type} {r : α → α → Prop} {a b : α} (l : List α), List.IsChain r (a :: l) → Relation.ReflTransGen r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (1) (0) ([]) (by
  decide)) (by
  nofun)

-- Nat.leRec_succ, hypothesis 6: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Nat.leRec_succ.h6.der.{u_1} : ∀ {m n : Nat} {motive : (m : Nat) → @LE.le Nat instLENat n m → Sort u_1} (refl : motive n (Nat.le_refl n))
      (le_succ_of_le :
        ⦃k : Nat⦄ →
          (h : @LE.le Nat instLENat n k) →
            motive k h →
              motive
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Nat.le_succ_of_le n k h)),
      @LE.le Nat instLENat n m →
        @LE.le Nat instLENat n
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  (intros; solve_by_elim)
theorem HypCheckProof.Nat.leRec_succ.h6.{u_1} : ∀ {m n : Nat} {motive : (m : Nat) → @LE.le Nat instLENat n m → Sort u_1} (refl : motive n (Nat.le_refl n))
      (le_succ_of_le :
        ⦃k : Nat⦄ →
          (h : @LE.le Nat instLENat n k) →
            motive k h →
              motive
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Nat.le_succ_of_le n k h))
      (h1 : @LE.le Nat instLENat n m),
      @Eq
        (motive
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HypCheckProof.Nat.leRec_succ.h6.der m n motive refl le_succ_of_le h1))
        (@Nat.leRec n motive refl le_succ_of_le
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HypCheckProof.Nat.leRec_succ.h6.der m n motive refl le_succ_of_le h1))
        (@le_succ_of_le m h1 (@Nat.leRec n motive refl le_succ_of_le m h1)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Nat.leRec_succ hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 (@HypCheckProof.Nat.leRec_succ.h6.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5)

-- Finset.sort_empty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_empty.h4 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Total r], Std.Antisymm r := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => True : Bool → Bool → Prop) (fun (a b : Bool) => instDecidableTrue) (@IsTrans.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide)) (@Std.Total.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide))) (by
  exact fun hc_c =>
    absurd
      (hc_c.antisymm (Bool.false : Bool) (Bool.true : Bool)
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

-- Finset.sort_empty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.sort_empty.h5 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] [inst : IsTrans α r] [inst : Std.Antisymm r], Std.Total r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ _) (by
  exact fun hc_c =>
    absurd (hc_c.total (0 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.eq_of_nonempty_of_subsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_nonempty_of_subsingleton.h1 : ¬∀ {α : Type} (s t : Set α) [inst : Nonempty ↑s] [inst : Nonempty ↑t], s = t := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (by
  simp) (by
  simp)) (by
  simp)

-- Set.eq_of_nonempty_of_subsingleton, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_nonempty_of_subsingleton.h5 : ¬∀ {α : Type} [inst : Subsingleton α] (s t : Set α) [inst : Nonempty ↑s], s = t := fun hc_h => absurd (@hc_h (Unit) _ (⊤) (∅) _) (by
  simp)

-- List.length_mem_splitLengths, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_mem_splitLengths.h4 : ¬∀ {α : Type} (l : List α) (sz : List ℕ) (b : ℕ), ∀ l₂ ∈ sz.splitLengths l, l₂.length ≤ b := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([1]) (0) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.length_mem_splitLengths, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_mem_splitLengths.h6 : ¬∀ {α : Type} (l : List α) (sz : List ℕ) (b : ℕ), (∀ n ∈ sz, n ≤ b) → ∀ (l₂ : List α), l₂.length ≤ b := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (0) (by
  decide) ([0])) (by
  decide +kernel)

-- Nat.leRec_succ_left, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Nat.leRec_succ_left.h5.der.{u_1} : ∀ {n : Nat} {motive : (m : Nat) → @LE.le Nat instLENat n m → Sort u_1} (refl : motive n (Nat.le_refl n))
      (le_succ_of_le :
        ⦃k : Nat⦄ →
          (h : @LE.le Nat instLENat n k) →
            motive k h →
              motive
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Nat.le_succ_of_le n k h))
      {m : Nat},
      @LE.le Nat instLENat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          m →
        @LE.le Nat instLENat n m := by
  (intros; lia)
theorem HypCheckProof.Nat.leRec_succ_left.h5.{u_1} : ∀ {n : Nat} {motive : (m : Nat) → @LE.le Nat instLENat n m → Sort u_1} (refl : motive n (Nat.le_refl n))
      (le_succ_of_le :
        ⦃k : Nat⦄ →
          (h : @LE.le Nat instLENat n k) →
            motive k h →
              motive
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Nat.le_succ_of_le n k h))
      {m : Nat}
      (h2 :
        @LE.le Nat instLENat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          m),
      @Eq (motive m (@Nat.le_of_succ_le n m h2))
        (@Nat.leRec
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (fun (x : Nat)
              (h :
                @LE.le Nat instLENat
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  x) =>
            motive x (@Nat.le_of_succ_le n x h))
          (@le_succ_of_le n (Nat.le_refl n) refl)
          (fun (x : Nat)
              (h :
                @LE.le Nat instLENat
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  x)
              (ih : motive x (@Nat.le_of_succ_le n x h)) =>
            @le_succ_of_le x (@Nat.le_of_succ_le n x h) ih)
          m h2)
        (@Nat.leRec n motive refl le_succ_of_le m
          (@HypCheckProof.Nat.leRec_succ_left.h5.der n motive refl le_succ_of_le m h2)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5
  exact @Nat.leRec_succ_left hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.Nat.leRec_succ_left.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5) hc_x5

-- Finset.mem_range_iff_mem_finset_range_of_mod_eq', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_range_iff_mem_finset_range_of_mod_eq'.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {f : ℕ → α} {a : α} {n : ℕ},
        (∀ (i : ℕ), f (i % n) = f i) → (a ∈ Set.range f ↔ a ∈ Finset.image (fun (i : ℕ) => f i) (Finset.range n)) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (fun n => n + 1 : ℕ → ℕ) (1) (0) (by
  simp)) (by
  simp)

-- Finset.mem_range_iff_mem_finset_range_of_mod_eq', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_range_iff_mem_finset_range_of_mod_eq'.h6 : ¬∀ {α : Type} [inst : DecidableEq α] {f : ℕ → α} {a : α} {n : ℕ},
        0 < n → (a ∈ Set.range f ↔ a ∈ Finset.image (fun (i : ℕ) => f i) (Finset.range n)) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (fun n => n + 1 : ℕ → ℕ) (2) (1) (by
  decide)) (by
  simp)

-- Nat.nth_eq_zero_mono, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_eq_zero_mono.h1 : ¬∀ {p : ℕ → Prop} {a b : ℕ}, a ≤ b → Nat.nth p a = 0 → Nat.nth p b = 0 := fun hc_h => absurd (@hc_h (fun _ => True : ℕ → Prop) (0) (1) (by
  decide) (by
  simp)) (by
  simp)

-- Nat.nth_lt_nth_of_lt_card, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_lt_nth_of_lt_card.h4 : ¬∀ {p : ℕ → Prop} (hf : (Set.ofPred p).Finite) {m n : ℕ}, n < hf.toFinset.card → Nat.nth p m < Nat.nth p n := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (fun n => n = 0 : ℕ → Prop) hc_k0 (0) (0) hc_k1) (by
  simp)

-- Nat.nth_lt_nth_of_lt_card, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_lt_nth_of_lt_card.h5 : ¬∀ {p : ℕ → Prop}, (Set.ofPred p).Finite → ∀ {m n : ℕ}, m < n → Nat.nth p m < Nat.nth p n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (by
  simp) (0) (1) (by
  decide)) (by
  simp)

-- Ordnode.balancedSz_up, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.balancedSz_up.h3 : ¬∀ {l r₁ r₂ : ℕ}, l + r₂ ≤ 1 ∨ r₂ ≤ Ordnode.delta * l → Ordnode.BalancedSz l r₁ → Ordnode.BalancedSz l r₂ := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Ordnode.balancedSz_up, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.balancedSz_up.h4 : ¬∀ {l r₁ r₂ : ℕ}, r₁ ≤ r₂ → Ordnode.BalancedSz l r₁ → Ordnode.BalancedSz l r₂ := fun hc_h => absurd (@hc_h (0) (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Ordnode.balancedSz_up, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.balancedSz_up.h5 : ¬∀ {l r₁ r₂ : ℕ}, r₁ ≤ r₂ → l + r₂ ≤ 1 ∨ r₂ ≤ Ordnode.delta * l → Ordnode.BalancedSz l r₂ := fun hc_h => absurd (@hc_h (2) (0) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Ordnode.pos_size_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.pos_size_of_mem.h5 : ¬∀ {α : Type} [inst : LE α] [inst_1 : DecidableLE α] {x : α} {t : Ordnode α}, x ∈ t → 0 < t.size := fun hc_h => absurd (@hc_h (ℕ) (instLENat) (Nat.decLe) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  decide)) (by
  decide +kernel)

-- Ordnode.pos_size_of_mem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.pos_size_of_mem.h6 : ¬∀ {α : Type} [inst : LE α] [inst : DecidableLE α] {x : α} {t : Ordnode α}, t.Sized → 0 < t.size := fun hc_h => absurd (@hc_h (ℕ) (instLENat) (Nat.decLe) (0) (Ordnode.nil) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Ordnode.insert'.valid, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.insert'.valid.h6 : ¬∀ {α : Type} [inst : Preorder α] [inst_1 : Std.Total fun (x1 x2 : α) => x1 ≤ x2] [inst_2 : DecidableLE α] (x : α)
        {t : Ordnode α}, (Ordnode.insert' x t).Valid := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) _ (Nat.decLe) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil)) (by
  nofun)

-- Nat.not_prime_of_mul_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_prime_of_mul_eq.h3 : ¬∀ {a b n : ℕ}, a ≠ 1 → b ≠ 1 → ¬Nat.Prime n := fun hc_h => absurd (@hc_h (0) (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.not_prime_of_mul_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_prime_of_mul_eq.h4 : ¬∀ {a b n : ℕ}, a * b = n → b ≠ 1 → ¬Nat.Prime n := fun hc_h => absurd (@hc_h (1) (2) _ rfl (by
  decide)) (by
  decide +kernel)

-- Nat.not_prime_of_mul_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_prime_of_mul_eq.h5 : ¬∀ {a b n : ℕ}, a * b = n → a ≠ 1 → ¬Nat.Prime n := fun hc_h => absurd (@hc_h (2) (1) _ rfl (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.mul_eq_prime_sq_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.mul_eq_prime_sq_iff.h3 : ¬∀ {x y p : ℕ}, x ≠ 1 → y ≠ 1 → (x * y = p ^ 2 ↔ x = p ∧ y = p) := fun hc_h => absurd (@hc_h (0) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.mul_eq_prime_sq_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.mul_eq_prime_sq_iff.h4 : ¬∀ {x y p : ℕ}, Nat.Prime p → y ≠ 1 → (x * y = p ^ 2 ↔ x = p ∧ y = p) := fun hc_h => absurd (@hc_h (1) (4) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.mul_eq_prime_sq_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.mul_eq_prime_sq_iff.h5 : ¬∀ {x y p : ℕ}, Nat.Prime p → x ≠ 1 → (x * y = p ^ 2 ↔ x = p ∧ y = p) := fun hc_h => absurd (@hc_h (4) (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.IsSuffix.idxOf_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsSuffix.idxOf_le.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] (a : α),
        List.idxOf a l₂ ≤ l₂.length - l₁.length + List.idxOf a l₁ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([1]) (instBEqOfDecidableEq) _ (0)) (by
  decide +kernel)

-- Ordnode.insert.valid, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.insert.valid.h6 : ¬∀ {α : Type} [inst : Preorder α] [inst_1 : Std.Total fun (x1 x2 : α) => x1 ≤ x2] [inst_2 : DecidableLE α] (x : α)
        {t : Ordnode α}, (Ordnode.insert x t).Valid := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) _ (Nat.decLe) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil)) (by
  nofun)

-- List.Disjoint.map, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Disjoint.map.h6 : ¬∀ {α β : Type} {f : α → β} {s t : List α}, Function.Injective f → (List.map f s).Disjoint (List.map f t) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) ([Bool.false]) ([Bool.false]) (by
  decide)) (by
  simp)

-- Part.eq_of_get_eq_get, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.eq_of_get_eq_get.h3 : ¬∀ {α : Type} {a b : Part α}, b.Dom → a.Dom := fun hc_h => absurd (@hc_h (ℕ) (⊥) (0) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Part.eq_of_get_eq_get, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.eq_of_get_eq_get.h4 : ¬∀ {α : Type} {a b : Part α}, a.Dom → b.Dom := fun hc_h => absurd (@hc_h (ℕ) (0) (⊥) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- ZMod.cast_natCast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.cast_natCast.h4 : Not
      (∀ {n : Nat} {R : Type} [inst : Ring R] {m : Nat},
        @Dvd.dvd Nat Nat.instDvd m n →
          ∀ (k : Nat),
            @Eq R
              (@ZMod.cast R (@Ring.toAddGroupWithOne R inst) n
                (@Nat.cast (ZMod n)
                  (@AddMonoidWithOne.toNatCast (ZMod n)
                    (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                      (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
                  k))
              (@Nat.cast R
                (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R (@Ring.toAddGroupWithOne R inst))) k)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Bool) (@BooleanRing.toRing Bool instBooleanRingBool) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Nat.digits_add, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_add.h1 : ¬∀ (b x y : ℕ), x < b → x ≠ 0 ∨ y ≠ 0 → b.digits (x + b * y) = x :: b.digits y := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.digits_add, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_add.h4 : ¬∀ (b : ℕ), 1 < b → ∀ (x y : ℕ), x ≠ 0 ∨ y ≠ 0 → b.digits (x + b * y) = x :: b.digits y := fun hc_h => absurd (@hc_h (2) (by
  decide) (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.digits_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_add.h5 : ¬∀ (b : ℕ), 1 < b → ∀ (x y : ℕ), x < b → b.digits (x + b * y) = x :: b.digits y := fun hc_h => absurd (@hc_h (2) (by
  decide) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Set.eq_of_nonempty_of_subsingleton', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_nonempty_of_subsingleton'.h5 : ¬∀ {α : Type} [inst : Subsingleton α] {s : Set α} (t : Set α), s.Nonempty → s = t := fun hc_h => absurd (@hc_h (Unit) _ (⊤) (∅) (by
  simp)) (by
  simp)

-- Nat.Ico_filter_pow_dvd_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Ico_filter_pow_dvd_eq.h3 : ¬∀ {n p b : ℕ}, n ≠ 0 → n ≤ p ^ b → {i ∈ Finset.Ico 1 n | p ^ i ∣ n} = {i ∈ Finset.Icc 1 b | p ^ i ∣ n} := fun hc_h => absurd (@hc_h (1) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Ico_filter_pow_dvd_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Ico_filter_pow_dvd_eq.h4 : ¬∀ {n p b : ℕ}, Nat.Prime p → n ≤ p ^ b → {i ∈ Finset.Ico 1 n | p ^ i ∣ n} = {i ∈ Finset.Icc 1 b | p ^ i ∣ n} := fun hc_h => absurd (@hc_h (0) (2) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Ico_filter_pow_dvd_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Ico_filter_pow_dvd_eq.h5 : ¬∀ {n p b : ℕ}, Nat.Prime p → n ≠ 0 → {i ∈ Finset.Ico 1 n | p ^ i ∣ n} = {i ∈ Finset.Icc 1 b | p ^ i ∣ n} := fun hc_h => absurd (@hc_h (2) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_eq_card_pow_dvd_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_card_pow_dvd_of_lt.h3 : ¬∀ {b m n : ℕ}, 0 < n → n < m ^ b → n.factorization m = {i ∈ Finset.Ico 1 b | m ^ i ∣ n}.card := fun hc_h => absurd (@hc_h (2) (4) (4) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_eq_card_pow_dvd_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_card_pow_dvd_of_lt.h4 : ¬∀ {b m n : ℕ}, Nat.Prime m → n < m ^ b → n.factorization m = {i ∈ Finset.Ico 1 b | m ^ i ∣ n}.card := fun hc_h => absurd (@hc_h (2) (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_eq_card_pow_dvd_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_card_pow_dvd_of_lt.h5 : ¬∀ {b m n : ℕ}, Nat.Prime m → 0 < n → n.factorization m = {i ∈ Finset.Ico 1 b | m ^ i ∣ n}.card := fun hc_h => absurd (@hc_h (0) (2) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_choose_prime_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose_prime_pow.h3 : ¬∀ {p n k : ℕ}, k ≤ p ^ n → k ≠ 0 → ((p ^ n).choose k).factorization p = n - k.factorization p := fun hc_h => absurd (@hc_h (1) (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_choose_prime_pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose_prime_pow.h4 : ¬∀ {p n k : ℕ}, Nat.Prime p → k ≠ 0 → ((p ^ n).choose k).factorization p = n - k.factorization p := fun hc_h => absurd (@hc_h (2) (1) (3) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_choose_prime_pow, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose_prime_pow.h5 : ¬∀ {p n k : ℕ}, Nat.Prime p → k ≤ p ^ n → ((p ^ n).choose k).factorization p = n - k.factorization p := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- DFinsupp.comapDomain'_smul, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.comapDomain'_smul.h8 : ¬∀ {ι γ : Type} {β : ι → Type} {κ : Type} [inst : (i : ι) → Zero (β i)] [inst_1 : (i : ι) → SMulZeroClass γ (β i)]
        (h : κ → ι) {h' : ι → κ} (r : γ) (f : Π₀ (i : ι), β i), Function.LeftInverse h' h := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => ℕ) (Bool) (fun (i : ℕ) => Nat.instMulZeroClass.toZero) (fun (i : ℕ) => NonUnitalNonAssocSemiring.toDistribSMul.toSMulZeroClass) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n % 2 == 0 : ℕ → Bool) (0) (0)) (by
  decide +kernel)

-- Set.mem_image_val_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_image_val_of_mem.h4 : ¬∀ {α : Type} {β : Set α} {γ : Set ↑β} {a : α}, a ∈ β := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (∅) (1)) (by
  decide +kernel)

-- Set.mem_image_val_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_image_val_of_mem.h5 : ¬∀ {α : Type} {β : Set α} {γ : Set ↑β} {a : α}, a ∈ β → a ∈ Subtype.val '' γ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (∅) (0) (by
  decide)) (by
  simp)

-- List.mem_dropLast_iff_idxOf_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_dropLast_iff_idxOf_lt.h2 : ¬∀ {α : Type} [inst : BEq α] {l : List α} {a : α}, a ∈ l → (a ∈ l.dropLast ↔ List.idxOf a l < l.length - 1) := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) ([0, 1]) (1) (by
  decide)) (by
  decide +kernel)

-- Set.eq_of_mem_insert_of_notMem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_mem_insert_of_notMem.h4 : ¬∀ {α : Type} {s : Set α} {a b : α}, b ∉ s → b = a := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Set.eq_of_mem_insert_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_mem_insert_of_notMem.h5 : ¬∀ {α : Type} {s : Set α} {a b : α}, b ∈ Insert.insert a s → b = a := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.dvd_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.dvd_iff.h4 : ¬∀ {m a b d : ℕ}, d ∣ m → (d ∣ a ↔ d ∣ b) := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.dvd_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.dvd_iff.h5 : ¬∀ {m a b d : ℕ}, a ≡ b [MOD m] → (d ∣ a ↔ d ∣ b) := fun hc_h => absurd (@hc_h (1) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Option.eq_of_mem_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.eq_of_mem_of_mem.h4 : ¬∀ {α : Type} {a : α} {o1 o2 : Option α}, a ∈ o2 → o1 = o2 := fun hc_h => absurd (@hc_h (ℕ) (0) (Option.none) (Option.some 0) (by
  decide)) (by
  decide +kernel)

-- Option.eq_of_mem_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.eq_of_mem_of_mem.h5 : ¬∀ {α : Type} {a : α} {o1 o2 : Option α}, a ∈ o1 → o1 = o2 := fun hc_h => absurd (@hc_h (ℕ) (0) (Option.some 0) (Option.none) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.cancel_right_div_gcd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.cancel_right_div_gcd.h4 : ¬∀ {m a b c : ℕ}, a * c ≡ b * c [MOD m] → a ≡ b [MOD m / m.gcd c] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.cancel_right_div_gcd, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.cancel_right_div_gcd.h5 : ¬∀ {m a b c : ℕ}, 0 < m → a ≡ b [MOD m / m.gcd c] := fun hc_h => absurd (@hc_h (2) (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.sub_right', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.sub_right'.h4 : ¬∀ {n a b c : ℕ}, b ≡ c [MOD n] → b - a ≡ c - a [MOD n] := fun hc_h => absurd (@hc_h (2) (1) (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.sub_right', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.sub_right'.h5 : ¬∀ {n a b c : ℕ}, (a ≤ b ↔ a ≤ c) → b - a ≡ c - a [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.cancel_left_of_coprime, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.cancel_left_of_coprime.h4 : ¬∀ {m a b c : ℕ}, c * a ≡ c * b [MOD m] → a ≡ b [MOD m] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.cancel_left_of_coprime, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.cancel_left_of_coprime.h5 : ¬∀ {m a b c : ℕ}, m.gcd c = 1 → a ≡ b [MOD m] := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.of_dvd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.of_dvd.h4 : ¬∀ {m n a b : ℕ}, a ≡ b [MOD n] → a ≡ b [MOD m] := fun hc_h => absurd (@hc_h (0) (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.ModEq.of_dvd, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.of_dvd.h5 : ¬∀ {m n a b : ℕ}, m ∣ n → a ≡ b [MOD m] := fun hc_h => absurd (@hc_h (0) (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Set.enumerateCountable_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.enumerateCountable_mem.h4 : ¬∀ {α : Type} {s : Set α} (h : s.Countable) {default : α} (n : ℕ), Set.enumerateCountable h default n ∈ s := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) ({x : ℕ | False}) hc_k0 (0) (0)) (by
  simp)

-- List.length_eraseP_add_one, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.length_eraseP_add_one.h4.inst : Not
      (@Eq Nat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@List.length Nat
            (@List.eraseP Nat
              (fun (n : Nat) =>
                @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
                  (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@List.nil Nat)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@List.length Nat (@List.nil Nat))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.length_eraseP_add_one.h4.prem0 : @Eq Bool
      ((fun (n : Nat) =>
          @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      Bool.true := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.length_eraseP_add_one.h4 : Not
      (∀ {α : Type} {p : α → Bool} {l : List α} {a : α},
        @Eq Bool (p a) Bool.true →
          @Eq Nat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@List.length α (@List.eraseP α p l))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@List.length α l)) := fun hc_h => HypCheckProof.List.length_eraseP_add_one.h4.inst (@hc_h (Nat) (fun (n : Nat) =>
      @BEq.beq Nat (@instBEqOfDecidableEq Nat instDecidableEqNat)
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@List.nil Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) HypCheckProof.List.length_eraseP_add_one.h4.prem0)

-- List.length_eraseP_add_one, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_eraseP_add_one.h5 : ¬∀ {α : Type} {p : α → Bool} {l : List α} {a : α}, a ∈ l → (List.eraseP p l).length + 1 = l.length := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) ([1]) (1) (by
  decide)) (by
  decide +kernel)

-- Prod.total_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.total_right.h4 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop} [inst : Std.Total s], Std.Total (Prod.Lex r s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (fun a b => a ≤ b : ℕ → ℕ → Prop) _) (by
  exact fun hc_c =>
    absurd (hc_c.total ((0, 0) : ℕ × ℕ) ((1, 0) : ℕ × ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Prod.total_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.total_right.h5 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop} [inst : Std.Trichotomous r], Std.Total (Prod.Lex r s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) _) (by
  exact fun hc_c =>
    absurd (hc_c.total ((0, 0) : ℕ × ℕ) ((0, 0) : ℕ × ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.ncard_exchange', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_exchange'.h5 : ¬∀ {α : Type} {s : Set α} {a b : α}, a ∉ s → (Insert.insert a s \ {b}).ncard = s.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1) (2) (by
  decide)) (by
  simp)

-- Set.ncard_preimage_of_injective_subset_range, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_preimage_of_injective_subset_range.h4 : ¬∀ {α β : Type} {f : α → β} {s : Set β}, s ⊆ Set.range f → (f ⁻¹' s).ncard = s.ncard := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.ncard_preimage_of_injective_subset_range, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_preimage_of_injective_subset_range.h5 : ¬∀ {α β : Type} {f : α → β} {s : Set β}, Function.Injective f → (f ⁻¹' s).ncard = s.ncard := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) ({x : ℕ | True}) (by
  decide)) (by
  simp)

-- Sigma.eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sigma.eq.h4 : ¬∀ {α : Type} {β : α → Type} {p₁ p₂ : (a : α) × β a}, p₁.fst = p₂.fst := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ((⟨0, 0⟩ : (a : ℕ) × (fun (a : ℕ) => ℕ) a)) ((⟨1, 0⟩ : (a : ℕ) × (fun (a : ℕ) => ℕ) a))) (by
  decide +kernel)

-- Sigma.eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sigma.eq.h5 : ¬∀ {α : Type} {β : α → Type} {p₁ p₂ : (a : α) × β a}, p₁.fst = p₂.fst → p₁ = p₂ := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ((⟨0, 0⟩ : (a : ℕ) × (fun (a : ℕ) => ℕ) a)) ((⟨0, 1⟩ : (a : ℕ) × (fun (a : ℕ) => ℕ) a)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Set.pairwise_insert_of_symmetric_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.pairwise_insert_of_symmetric_of_notMem.h5 : ¬∀ {α : Type} {r : α → α → Prop} {s : Set α} {a : α} [inst : Std.Symm r],
        (Insert.insert a s).Pairwise r ↔ s.Pairwise r ∧ ∀ b ∈ s, r a b := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≠ b : ℕ → ℕ → Prop) ({n : ℕ | n = 0}) (0) _) (by
  simp)

-- Set.Nonempty.preimage', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.preimage'.h3 : ¬∀ {α β : Type} {s : Set β} {f : α → β}, s ⊆ Set.range f → (f ⁻¹' s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ) (by
  simp)) (by
  simp)

-- Set.Nonempty.preimage', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.preimage'.h5 : ¬∀ {α β : Type} {s : Set β}, s.Nonempty → ∀ {f : α → β}, (f ⁻¹' s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (by
  simp) (fun n => n + 1 : ℕ → ℕ)) (by
  nofun)

-- List.IsChain.infix, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.infix.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l l₁ : List α}, List.IsChain R l → List.IsChain R l₁ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([1, 0]) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.iterate_eq_of_apply_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.iterate_eq_of_apply_eq.h3 : ¬∀ {α : Type} {f : α → α} {l : List α} (i : ℕ) (hi : i < l.length), f^[i] l[0] = l[i] := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) ([1, 0]) (1) hc_k0) (by
  decide +kernel)

-- List.IsChain.iterate_eq_of_apply_eq, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.iterate_eq_of_apply_eq.h5.inst : Not (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.length Nat (@List.nil Nat))) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.iterate_eq_of_apply_eq.h5.prem0 : @List.IsChain Nat
      (fun (x y : Nat) =>
        @Eq Nat
          ((fun (n : Nat) =>
              @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            x)
          y)
      (@List.nil Nat) := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.IsChain.iterate_eq_of_apply_eq.h5 : Not
      (∀ {α : Type} {f : α → α} {l : List α},
        @List.IsChain α (fun (x y : α) => @Eq α (f x) y) l → ∀ (i : Nat), @LT.lt Nat instLTNat i (@List.length α l)) := fun hc_h => HypCheckProof.List.IsChain.iterate_eq_of_apply_eq.h5.inst (@hc_h (Nat) (fun (n : Nat) =>
      @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@List.nil Nat) HypCheckProof.List.IsChain.iterate_eq_of_apply_eq.h5.prem0 (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))

-- Subtype.mk_eq_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.mk_eq_mk.h3 : ¬∀ {α : Type} {p : α → Prop} {a a' : α} {h' : p a'}, p a := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Subtype.mk_eq_mk, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.mk_eq_mk.h5 : ¬∀ {α : Type} {p : α → Prop} {a : α} {h : p a} {a' : α}, p a' := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1)) (by
  decide +kernel)

-- List.IsChain.cons, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.cons.h4.inst : ¬List.IsChain (fun (a b : ℕ) => a < b) [0, 1, 0] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.IsChain.cons.h4.prem0 : ∀ y ∈ [1, 0].head?, (fun (a b : ℕ) => a < b) 0 y := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.IsChain.cons.h4 : ¬∀ {α : Type} {R : α → α → Prop} {x : α} {l : List α}, (∀ y ∈ l.head?, R x y) → List.IsChain R (x :: l) := fun hc_h => HypCheckProof.List.IsChain.cons.h4.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) (0) ([1, 0]) HypCheckProof.List.IsChain.cons.h4.prem0)

-- List.IsChain.cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons.h5 : ¬∀ {α : Type} {R : α → α → Prop} {x : α} {l : List α}, List.IsChain R l → List.IsChain R (x :: l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) ([0]) (by
  decide)) (by
  decide +kernel)

-- Subtype.coind_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.coind_injective.h4 : ¬∀ {α β : Type} {f : α → β} {p : β → Prop}, Function.Injective f → ∀ (a : α), p (f a) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (fun n => n = 0 : ℕ → Prop) (by
  decide)) (by
  decide +kernel)

-- Subtype.coind_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.coind_injective.h5 : ¬∀ {α β : Type} {f : α → β} {p : β → Prop} (h : ∀ (a : α), p (f a)), Function.Injective (Subtype.coind f h) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (fun n => n = 0 : ℕ → Prop) hc_k0) (by
  simp)

-- DFinsupp.comapDomain_smul, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.comapDomain_smul.h7 : ¬∀ {ι γ : Type} {β : ι → Type} {κ : Type} [inst : (i : ι) → Zero (β i)] [inst_1 : (i : ι) → SMulZeroClass γ (β i)]
        (h : κ → ι) (r : γ) (f : Π₀ (i : ι), β i), Function.Injective h := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => ℕ) (ℕ) (fun (i : ℕ) => Nat.instMulZeroClass.toZero) (fun (i : ℕ) => NonUnitalNonAssocSemiring.toDistribSMul.toSMulZeroClass) (fun _ => 0 : ℕ → ℕ) (0) (0)) (by
  simp)

-- Set.image_comm, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_comm.h9 : ¬∀ {α β γ : Type} {s : Set α} {β' : Type} {f : β → γ} {g : α → β} {f' : α → β'} {g' : β' → γ},
        f '' g '' s = g' '' f' '' s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- List.IsChain.imp_of_mem_imp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.imp_of_mem_imp.h4 : ¬∀ {α : Type} {R S : α → α → Prop} {l : List α}, List.IsChain R l → List.IsChain S l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a = b : ℕ → ℕ → Prop) ([0, 1]) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.imp_of_mem_imp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.imp_of_mem_imp.h5 : ¬∀ {α : Type} {R S : α → α → Prop} {l : List α}, (∀ (a b : α), a ∈ l → b ∈ l → R a b → S a b) → List.IsChain S l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0]) (by
  simp)) (by
  decide +kernel)

-- Nat.ofNat_nonneg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofNat_nonneg.h5 : ¬∀ {α : Type} [inst : Semiring α] [inst_1 : PartialOrder α] [inst : IsOrderedRing α] (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (Nat.instSemiring) (Nat.instPartialOrder) _ (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.cast_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.cast_pos.h3 : Not
      (∀ {α : Type} [inst : Semiring α] [inst_1 : PartialOrder α] [inst_2 : Nontrivial α] {n : Nat},
        Iff
          (@LT.lt α (@Preorder.toLT α (@PartialOrder.toPreorder α inst_1))
            (@OfNat.ofNat α (nat_lit 0) (@Zero.toOfNat0 α (@MulZeroClass.toZero α (@instMulZeroClassOfSemiring α inst))))
            (@Nat.cast α
              (@AddMonoidWithOne.toNatCast α
                (@AddCommMonoidWithOne.toAddMonoidWithOne α
                  (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
              n))
          (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)) := fun hc_h => absurd (@hc_h (Bool) (@CommSemiring.toSemiring Bool (@CommRing.toCommSemiring Bool (@BooleanRing.toCommRing Bool instBooleanRingBool))) (Bool.instPartialOrder) _ (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (by
  decide +kernel)

-- Set.Nonempty.preimage, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.preimage.h3 : ¬∀ {α β : Type} {s : Set β} {f : α → β}, Function.Surjective f → (f ⁻¹' s).Nonempty := fun hc_h => absurd (@hc_h (Bool) (Bool) ({x : Bool | False}) (not : Bool → Bool) (by
  decide)) (by
  simp)

-- Set.Nonempty.preimage, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.preimage.h5 : ¬∀ {α β : Type} {s : Set β}, s.Nonempty → ∀ {f : α → β}, (f ⁻¹' s).Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (by
  simp) (fun n => n + 1 : ℕ → ℕ)) (by
  nofun)

-- Set.Nontrivial.image, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.image.h4 : ¬∀ {α β : Type} {s : Set α} {f : α → β}, Function.Injective f → (f '' s).Nontrivial := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({b : Bool | b = Bool.true}) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide)) (by
  simp)

-- Nat.findGreatest_of_ne_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.findGreatest_of_ne_zero.h4 : ¬∀ {m : ℕ} {P : ℕ → Prop} [inst : DecidablePred P] {n : ℕ}, m ≠ 0 → P m := fun hc_h => absurd (@hc_h (1) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.findGreatest_of_ne_zero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.findGreatest_of_ne_zero.h5 : ¬∀ {m : ℕ} {P : ℕ → Prop} [inst : DecidablePred P] {n : ℕ}, Nat.findGreatest P n = m → P m := fun hc_h => absurd (@hc_h _ (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (0) rfl) (by
  decide +kernel)

-- Matrix.submatrix_ofNat_equiv, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.submatrix_ofNat_equiv.h9 : ¬∀ {l m α : Type} [inst : Zero α] [inst : NatCast α] [inst : DecidableEq m] [inst : DecidableEq l] (e : l ≃ m) (k : ℕ),
        k.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (instNatCastNat) (instDecidableEqNat) (instDecidableEqNat) (1) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.subsingleton_of_image, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subsingleton_of_image.h3 : ¬∀ {α β : Type} {f : α → β} (s : Set α), (f '' s).Subsingleton → s.Subsingleton := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ => 0 : Bool → ℕ) ({x : Bool | True}) (by
  simp)) (by
  decide +kernel)

-- Set.subsingleton_of_image, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subsingleton_of_image.h5 : ¬∀ {α β : Type} {f : α → β}, Function.Injective f → ∀ (s : Set α), s.Subsingleton := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (by
  decide) ({x : Bool | True})) (by
  decide +kernel)

-- Fin.sub_castLT_eq_castLT_sub_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.sub_castLT_eq_castLT_sub_of_le.h4 : ¬∀ {n m : ℕ} {a b : Fin m}, b ≤ a → ↑a < n := fun hc_h => absurd (@hc_h (0) (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- Fin.sub_castLT_eq_castLT_sub_of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.sub_castLT_eq_castLT_sub_of_le.h5 : ¬∀ {n m : ℕ} {a b : Fin m}, ↑a < n → b ≤ a := fun hc_h => absurd (@hc_h (1) (2) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Fin.snoc_injective_of_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.snoc_injective_of_injective.h4 : ¬∀ {n : ℕ} {α : Type} {x₀ : α} {x : Fin n → α}, x₀ ∉ Set.range x → Function.Injective (Fin.snoc x x₀) := fun hc_h => absurd (@hc_h (2) (ℕ) (0) (fun (a : Fin 2) => 1) (by
  decide)) (by
  decide +kernel)

-- Fin.snoc_injective_of_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.snoc_injective_of_injective.h5 : ¬∀ {n : ℕ} {α : Type} {x₀ : α} {x : Fin n → α}, Function.Injective x → Function.Injective (Fin.snoc x x₀) := fun hc_h => absurd (@hc_h (1) (ℕ) (0) (fun (a : Fin 1) => 0) (by
  decide)) (by
  decide +kernel)

-- List.prev_getElem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_getElem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α), l.Nodup → ∀ (i : ℕ), i < l.length := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (by
  decide) (0)) (by
  decide +kernel)

-- Fin.cons_injective_of_injective, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.cons_injective_of_injective.h4 : ¬∀ {n : ℕ} {α : Type} {x₀ : α} {x : Fin n → α}, Function.Injective x → Function.Injective (Fin.cons x₀ x) := fun hc_h => absurd (@hc_h (1) (ℕ) (0) (fun (a : Fin 1) => 0) (by
  decide)) (by
  decide +kernel)

-- Fin.cons_injective_of_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.cons_injective_of_injective.h5 : ¬∀ {n : ℕ} {α : Type} {x₀ : α} {x : Fin n → α}, x₀ ∉ Set.range x → Function.Injective (Fin.cons x₀ x) := fun hc_h => absurd (@hc_h (2) (ℕ) (0) (fun (a : Fin 2) => 1) (by
  decide)) (by
  decide +kernel)

-- List.prev_reverse_eq_next, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_reverse_eq_next.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α), l.Nodup → ∀ (x : α), x ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (by
  decide) (0)) (by
  decide +kernel)

-- List.prev_next, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prev_next.h5 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α), l.Nodup → ∀ (x : α), x ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (by
  decide) (0)) (by
  decide +kernel)

-- Function.Surjective.injective_of_finite, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.injective_of_finite.h5 : Not (∀ {α β : Type} [inst : Finite α] {f : α → β} (e : Equiv α β), @Function.Injective α β f) := fun hc_h => absurd (@hc_h (Bool) (Bool) _ (fun _ => true : Bool → Bool) (@Equiv.mk Bool Bool Bool.not Bool.not
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

-- List.Duplicate.of_duplicate_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Duplicate.of_duplicate_cons.h4 : ¬∀ {α : Type} {l : List α} {x y : α}, x ≠ y → List.Duplicate x l := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.Duplicate.of_duplicate_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Duplicate.of_duplicate_cons.h5 : ¬∀ {α : Type} {l : List α} {x y : α}, List.Duplicate x (y :: l) → List.Duplicate x l := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (0) (by
  decide)) (by
  decide +kernel)

-- List.map_orderedInsert, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map_orderedInsert.h9 : ¬∀ {α β : Type} (r : α → α → Prop) (s : β → β → Prop) [inst : DecidableRel r] [inst_1 : DecidableRel s] (f : α → β)
        (l : List α) (x : α), List.map f (List.orderedInsert r x l) = List.orderedInsert s (f x) (List.map f l) := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun a b => a < b : ℕ → ℕ → Prop) (fun _ _ => True : Bool → Bool → Prop) (Nat.decLt) (fun (a b : Bool) => instDecidableTrue) (fun n => n % 2 == 0 : ℕ → Bool) ([0]) (1)) (by
  decide +kernel)

-- List.pairwise_mergeSort', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwise_mergeSort'.h3 : ¬∀ {α : Type} (r : α → α → Prop) [inst : DecidableRel r] [inst_1 : IsTrans α r] (l : List α),
        List.Pairwise r (l.mergeSort fun (x1 x2 : α) => Decidable.decide (r x1 x2)) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) _ ([0, 0])) (by
  simp)

-- Int.ModEq.cancel_right_div_gcd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.cancel_right_div_gcd.h4 : ¬∀ {m a b c : ℤ}, a * c ≡ b * c [ZMOD m] → a ≡ b [ZMOD m / ↑(m.gcd c)] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.cancel_right_div_gcd, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.cancel_right_div_gcd.h5 : ¬∀ {m a b c : ℤ}, 0 < m → a ≡ b [ZMOD m / ↑(m.gcd c)] := fun hc_h => absurd (@hc_h (2) (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.mul_left_cancel', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.mul_left_cancel'.h4 : ¬∀ {m a b c : ℤ}, c * a ≡ c * b [ZMOD c * m] → a ≡ b [ZMOD m] := fun hc_h => absurd (@hc_h (0) (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Int.ModEq.mul_left_cancel', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.mul_left_cancel'.h5 : ¬∀ {m a b c : ℤ}, c ≠ 0 → a ≡ b [ZMOD m] := fun hc_h => absurd (@hc_h (0) (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Set.mem_sdiff_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_sdiff_of_mem.h4 : ¬∀ {α : Type} {s t : Set α} {x : α}, x ∉ t → x ∈ s \ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (1) (by
  decide)) (by
  decide +kernel)

-- Set.mem_sdiff_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_sdiff_of_mem.h5 : ¬∀ {α : Type} {s t : Set α} {x : α}, x ∈ s → x ∈ s \ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (0) (by
  decide)) (by
  decide +kernel)

-- Prime.not_dvd_prod, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prime.not_dvd_prod.h4 : ¬∀ {M : Type} [inst : CommMonoidWithZero M] {p : M} {L : List M}, (∀ a ∈ L, ¬p ∣ a) → ¬p ∣ L.prod := fun hc_h => absurd (@hc_h (ℕ) (Nat.instCommMonoidWithZero) (1) ([]) (by
  decide)) (by
  decide +kernel)

-- Prime.not_dvd_prod, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prime.not_dvd_prod.h5 : ¬∀ {M : Type} [inst : CommMonoidWithZero M] {p : M} {L : List M}, Prime p → ¬p ∣ L.prod := fun hc_h => absurd (@hc_h (ℕ) (Nat.instCommMonoidWithZero) (2) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.ne_empty_of_mem_consFixedLengthDigits, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.ne_empty_of_mem_consFixedLengthDigits.h1 : ¬∀ {b : ℕ} {l d : ℕ} {L : List ℕ}, 1 < b := fun hc_h => absurd (@hc_h (0) (0) (0) ([])) (by
  decide +kernel)

-- List.ne_empty_of_mem_consFixedLengthDigits, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.ne_empty_of_mem_consFixedLengthDigits.h5 : ¬∀ {b : ℕ}, 1 < b → ∀ {l d : ℕ} {L : List ℕ}, L ≠ [] := fun hc_h => absurd (@hc_h (2) (by
  decide) (0) (0) ([])) (by
  decide +kernel)

-- Nat.multiplicity_choose_aux, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.multiplicity_choose_aux.h4 : ¬∀ {p n b k : ℕ},
        k ≤ n →
          ∑ i ∈ Finset.Ico 1 b, n / p ^ i =
            ∑ i ∈ Finset.Ico 1 b, k / p ^ i + ∑ i ∈ Finset.Ico 1 b, (n - k) / p ^ i +
              {i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}.card := fun hc_h => absurd (@hc_h (0) (0) (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.multiplicity_choose_aux, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.multiplicity_choose_aux.h5 : ¬∀ {p n b k : ℕ},
        Nat.Prime p →
          ∑ i ∈ Finset.Ico 1 b, n / p ^ i =
            ∑ i ∈ Finset.Ico 1 b, k / p ^ i + ∑ i ∈ Finset.Ico 1 b, (n - k) / p ^ i +
              {i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}.card := fun hc_h => absurd (@hc_h (2) (0) (2) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.pow_dvd_factorial_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.pow_dvd_factorial_iff.h4 : ¬∀ {p n r b : ℕ}, Nat.log p n < b → (p ^ r ∣ n.factorial ↔ r ≤ ∑ i ∈ Finset.Ico 1 b, n / p ^ i) := fun hc_h => absurd (@hc_h (1) (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.pow_dvd_factorial_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.pow_dvd_factorial_iff.h5 : ¬∀ {p n r b : ℕ}, Nat.Prime p → (p ^ r ∣ n.factorial ↔ r ≤ ∑ i ∈ Finset.Ico 1 b, n / p ^ i) := fun hc_h => absurd (@hc_h (2) (2) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Set.not_injOn_infinite_finite_image, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.not_injOn_infinite_finite_image.h4 : ¬∀ {α β : Type} {f : α → β} {s : Set α}, (f '' s).Finite → ¬Set.InjOn f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- List.mk_mem_sym2, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mk_mem_sym2.h4 : ¬∀ {α : Type} {xs : List α} {a b : α}, b ∈ xs → s(a, b) ∈ xs.sym2 := fun hc_h => absurd (@hc_h (ℕ) ([0]) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.mk_mem_sym2, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mk_mem_sym2.h5 : ¬∀ {α : Type} {xs : List α} {a b : α}, a ∈ xs → s(a, b) ∈ xs.sym2 := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Set.Infinite.preimage, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.preimage.h4 : ¬∀ {α β : Type} {f : α → β} {s : Set β}, s ⊆ Set.range f → (f ⁻¹' s).Infinite := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Nat.cast_div, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.cast_div.h4 : Not
      (∀ {K : Type} [inst : DivisionSemiring K] {m n : Nat},
        @Ne K
            (@Nat.cast K
              (@AddMonoidWithOne.toNatCast K
                (@AddCommMonoidWithOne.toAddMonoidWithOne K
                  (@NonAssocSemiring.toAddCommMonoidWithOne K
                    (@Semiring.toNonAssocSemiring K (@DivisionSemiring.toSemiring K inst)))))
              n)
            (@OfNat.ofNat K (nat_lit 0)
              (@Zero.toOfNat0 K
                (@MulZeroClass.toZero K (@instMulZeroClassOfSemiring K (@DivisionSemiring.toSemiring K inst))))) →
          @Eq K
            (@Nat.cast K
              (@AddMonoidWithOne.toNatCast K
                (@AddCommMonoidWithOne.toAddMonoidWithOne K
                  (@NonAssocSemiring.toAddCommMonoidWithOne K
                    (@Semiring.toNonAssocSemiring K (@DivisionSemiring.toSemiring K inst)))))
              (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) m n))
            (@HDiv.hDiv K K K
              (@instHDiv K
                (@DivInvMonoid.toDiv K (@GroupWithZero.toDivInvMonoid K (@DivisionSemiring.toGroupWithZero K inst))))
              (@Nat.cast K
                (@AddMonoidWithOne.toNatCast K
                  (@AddCommMonoidWithOne.toAddMonoidWithOne K
                    (@NonAssocSemiring.toAddCommMonoidWithOne K
                      (@Semiring.toNonAssocSemiring K (@DivisionSemiring.toSemiring K inst)))))
                m)
              (@Nat.cast K
                (@AddMonoidWithOne.toNatCast K
                  (@AddCommMonoidWithOne.toAddMonoidWithOne K
                    (@NonAssocSemiring.toAddCommMonoidWithOne K
                      (@Semiring.toNonAssocSemiring K (@DivisionSemiring.toSemiring K inst)))))
                n))) := fun hc_h => absurd (@hc_h (Rat) (@Semifield.toDivisionSemiring Rat (@Field.toSemifield Rat Rat.instField)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Nat.cast_choose, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.cast_choose.h5 : Not
      (∀ (K : Type) [inst : DivisionSemiring K]
        [inst_1 :
          @CharZero K
            (@AddCommMonoidWithOne.toAddMonoidWithOne K
              (@NonAssocSemiring.toAddCommMonoidWithOne K
                (@Semiring.toNonAssocSemiring K (@DivisionSemiring.toSemiring K inst))))]
        {a b : Nat},
        @Eq K
          (@Nat.cast K
            (@AddMonoidWithOne.toNatCast K
              (@AddCommMonoidWithOne.toAddMonoidWithOne K
                (@NonAssocSemiring.toAddCommMonoidWithOne K
                  (@Semiring.toNonAssocSemiring K (@DivisionSemiring.toSemiring K inst)))))
            (b.choose a))
          (@HDiv.hDiv K K K
            (@instHDiv K
              (@DivInvMonoid.toDiv K (@GroupWithZero.toDivInvMonoid K (@DivisionSemiring.toGroupWithZero K inst))))
            (@Nat.cast K
              (@AddMonoidWithOne.toNatCast K
                (@AddCommMonoidWithOne.toAddMonoidWithOne K
                  (@NonAssocSemiring.toAddCommMonoidWithOne K
                    (@Semiring.toNonAssocSemiring K (@DivisionSemiring.toSemiring K inst)))))
              b.factorial)
            (@HMul.hMul K K K
              (@instHMul K (@Distrib.toMul K (@instDistribOfSemiring K (@DivisionSemiring.toSemiring K inst))))
              (@Nat.cast K
                (@AddMonoidWithOne.toNatCast K
                  (@AddCommMonoidWithOne.toAddMonoidWithOne K
                    (@NonAssocSemiring.toAddCommMonoidWithOne K
                      (@Semiring.toNonAssocSemiring K (@DivisionSemiring.toSemiring K inst)))))
                a.factorial)
              (@Nat.cast K
                (@AddMonoidWithOne.toNatCast K
                  (@AddCommMonoidWithOne.toAddMonoidWithOne K
                    (@NonAssocSemiring.toAddCommMonoidWithOne K
                      (@Semiring.toNonAssocSemiring K (@DivisionSemiring.toSemiring K inst)))))
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) b a).factorial)))) := fun hc_h => absurd (@hc_h (Rat) (@Semifield.toDivisionSemiring Rat (@Field.toSemifield Rat Rat.instField)) _ (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- List.idxOf_eq_zero_iff_head_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_eq_zero_iff_head_eq.h2 : ¬∀ {α : Type} [inst : BEq α] {l : List α} (hl : l ≠ []) {a : α}, List.idxOf a l = 0 ↔ l.head hl = a := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) ([0]) hc_k0 (1)) (by
  decide +kernel)

-- List.idxOf_eq_zero_iff_head_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_eq_zero_iff_head_eq.h4 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {l : List α} {a : α}, l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ ([]) (0)) (by
  decide +kernel)

-- List.getElem?_idxOf, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem?_idxOf.h2 : ¬∀ {α : Type} [inst : BEq α] {a : α} {l : List α}, a ∈ l → l[List.idxOf a l]? = Option.some a := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a != b⟩ : BEq ℕ) (0) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.getElem?_idxOf, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem?_idxOf.h5 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {a : α} {l : List α}, l[List.idxOf a l]? = Option.some a := fun hc_h => absurd (@hc_h (ℕ) (instBEqOfDecidableEq) _ (0) ([])) (by
  decide +kernel)

-- Set.inter_congr_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_congr_right.h4 : ¬∀ {α : Type} {s t u : Set α}, s ∩ u ⊆ t → s ∩ u = t ∩ u := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.inter_congr_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_congr_right.h5 : ¬∀ {α : Type} {s t u : Set α}, t ∩ u ⊆ s → s ∩ u = t ∩ u := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- EReal.sub_le_sub, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.sub_le_sub.h4 : ¬∀ {x y z t : EReal}, t ≤ z → x - z ≤ y - t := fun hc_h => absurd (@hc_h (1) (0) (0) (0) (by
  rfl)) (by
  simp)

-- EReal.sub_le_sub, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.sub_le_sub.h5 : ¬∀ {x y z t : EReal}, x ≤ y → x - z ≤ y - t := fun hc_h => absurd (@hc_h (0) (0) (0) (1) (by
  rfl)) (by
  (simp <;> decide))

-- Nat.one_div_cast_ne_zero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.one_div_cast_ne_zero.h5 : Not
      (∀ {α : Type} [inst : Semifield α] [inst_1 : LinearOrder α]
        [inst_2 :
          @IsStrictOrderedRing α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))
            (@SemilatticeInf.toPartialOrder α
              (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))]
        {n : Nat},
        @Ne α
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
              n))
          (@OfNat.ofNat α (nat_lit 0)
            (@Zero.toOfNat0 α
              (@MulZeroClass.toZero α
                (@instMulZeroClassOfSemiring α (@CommSemiring.toSemiring α (@Semifield.toCommSemiring α inst))))))) := fun hc_h => absurd (@hc_h (Rat) (@Field.toSemifield Rat Rat.instField) (Rat.linearOrder) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Set.mem_inter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_inter.h4 : ¬∀ {α : Type} {x : α} {a b : Set α}, x ∈ b → x ∈ a ∩ b := fun hc_h => absurd (@hc_h (ℕ) (0) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  decide)) (by
  decide +kernel)

-- Set.mem_inter, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_inter.h5 : ¬∀ {α : Type} {x : α} {a b : Set α}, x ∈ a → x ∈ a ∩ b := fun hc_h => absurd (@hc_h (ℕ) (0) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  decide)) (by
  decide +kernel)

-- List.get_insertIdx_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.get_insertIdx_self.h4 : ¬∀ {α : Type} (l : List α) (x : α) (n : ℕ), n ≤ l.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (1)) (by
  decide +kernel)

-- List.get_insertIdx_self, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.get_insertIdx_self.h5.der.{u} : ∀ {α : Type u} (l : List α) (x : α), ∀ n ≤ l.length, n < (l.insertIdx n x).length := by
  (intros; grind)
theorem HypCheckProof.List.get_insertIdx_self.h5.{u} : ∀ {α : Type u} (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length),
      (l.insertIdx n x).get (⟨n, HypCheckProof.List.get_insertIdx_self.h5.der l x n hn⟩ : Fin (l.insertIdx n x).length) = x := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @List.get_insertIdx_self hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.List.get_insertIdx_self.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- Set.notMem_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.notMem_subset.h4 : ¬∀ {α : Type} {a : α} {s t : Set α}, a ∉ t → a ∉ s := fun hc_h => absurd (@hc_h (ℕ) (0) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  decide)) (by
  decide +kernel)

-- Set.notMem_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.notMem_subset.h5 : ¬∀ {α : Type} {a : α} {s t : Set α}, s ⊆ t → a ∉ s := fun hc_h => absurd (@hc_h (ℕ) (0) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  decide +kernel)

-- Set.ssubset_of_subset_of_ssubset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ssubset_of_subset_of_ssubset.h4 : ¬∀ {α : Type} {s₁ s₂ s₃ : Set α}, s₂ ⊂ s₃ → s₁ ⊂ s₃ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.ssubset_of_subset_of_ssubset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ssubset_of_subset_of_ssubset.h5 : ¬∀ {α : Type} {s₁ s₂ s₃ : Set α}, s₁ ⊆ s₂ → s₁ ⊂ s₃ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Set.subset_sUnion_of_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_sUnion_of_subset.h5 : ¬∀ {α : Type} {s : Set α} (t : Set (Set α)) (u : Set α), s ⊆ u → s ⊆ ⋃₀ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (∅) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- List.Pairwise.rel_dropLast_getLast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_dropLast_getLast.h4 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α} (ha : a ∈ l.dropLast),
        R a (l.getLast (List.ne_nil_of_mem (List.dropLast_subset l ha))) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0]) (1) hc_k0) (by
  decide +kernel)

-- List.Pairwise.rel_dropLast_getLast, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.rel_dropLast_getLast.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} {a : α}, List.Pairwise R l → a ∈ l.dropLast := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (0) (by
  decide)) (by
  decide +kernel)

-- Set.notMem_of_notMem_sUnion, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.notMem_of_notMem_sUnion.h4 : ¬∀ {α : Type} {x : α} {t : Set α} {S : Set (Set α)}, t ∈ S → x ∉ t := fun hc_h => absurd (@hc_h (ℕ) (0) ({n : ℕ | n = 0}) (⊤) (by
  simp)) (by
  decide +kernel)

-- Set.notMem_of_notMem_sUnion, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.notMem_of_notMem_sUnion.h5 : ¬∀ {α : Type} {x : α} {t : Set α} {S : Set (Set α)}, x ∉ ⋃₀ S → x ∉ t := fun hc_h => absurd (@hc_h (ℕ) (0) ({n : ℕ | n = 0}) (∅) (by
  simp)) (by
  decide +kernel)

-- List.pairwise_iff_coe_toFinset_pairwise, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwise_iff_coe_toFinset_pairwise.h4 : Not
      (∀ {α : Type} [inst : DecidableEq α] {r : α → α → Prop} {l : List α},
        @List.Nodup α l →
          Iff (@Set.Pairwise α (@SetLike.coe (Finset α) α (@Finset.instSetLike α) (@List.toFinset α inst l)) r)
            (@List.Pairwise α r l)) := fun hc_h => absurd (@hc_h (Nat) (instDecidableEqNat) (fun a b => a < b : Nat → Nat → Prop) (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.nil Nat))) (by
  decide)) (by
  decide +kernel)

-- List.pairwise_iff_coe_toFinset_pairwise, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwise_iff_coe_toFinset_pairwise.h5 : Not
      (∀ {α : Type} [inst : DecidableEq α] {r : α → α → Prop} {l : List α} [inst_1 : @Std.Symm α r],
        Iff (@Set.Pairwise α (@SetLike.coe (Finset α) α (@Finset.instSetLike α) (@List.toFinset α inst l)) r)
          (@List.Pairwise α r l)) := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) (fun _ _ => False : Bool → Bool → Prop) (@List.cons Bool Bool.false (@List.cons Bool Bool.false (@List.nil Bool))) _) (by
  decide +kernel)

-- Set.Nonempty.infs, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.infs.h4 : Not
      (∀ {α : Type} [inst : SemilatticeInf α] {s t : Set α},
        @Set.Nonempty α t → @Set.Nonempty α (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s t)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Set.ofPred Nat fun (x : Nat) => False) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  simp)) (by
  simp)

-- Set.Nonempty.infs, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.infs.h5 : Not
      (∀ {α : Type} [inst : SemilatticeInf α] {s t : Set α},
        @Set.Nonempty α s → @Set.Nonempty α (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s t)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeInf Nat Nat.instLattice) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@Set.ofPred Nat fun (x : Nat) => False) (by
  simp)) (by
  simp)

-- Nat.append_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.append_lt.h4 : ¬∀ {x y n m : ℕ}, y < 2 ^ m → y <<< n ||| x < 2 ^ (n + m) := fun hc_h => absurd (@hc_h (1) (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.append_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.append_lt.h5 : ¬∀ {x y n m : ℕ}, x < 2 ^ n → y <<< n ||| x < 2 ^ (n + m) := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- List.not_nodup_of_get_eq_of_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_nodup_of_get_eq_of_ne.h4 : ¬∀ {α : Type} (xs : List α) (n m : Fin xs.length), n ≠ m → ¬xs.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.not_nodup_of_get_eq_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.not_nodup_of_get_eq_of_ne.h5 : ¬∀ {α : Type} (xs : List α) (n m : Fin xs.length), xs.get n = xs.get m → ¬xs.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Set.mem_sep, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_sep.h4 : ¬∀ {α : Type} {s : Set α} {p : α → Prop} {x : α}, p x → x ∈ {x : α | x ∈ s ∧ p x} := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (fun n => n = 0 : ℕ → Prop) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Set.mem_sep, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_sep.h5 : ¬∀ {α : Type} {s : Set α} {p : α → Prop} {x : α}, x ∈ s → x ∈ {x : α | x ∈ s ∧ p x} := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (fun _ => False : ℕ → Prop) (0) (by
  decide)) (by
  decide +kernel)

-- Set.Subset.trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subset.trans.h4 : ¬∀ {α : Type} {a b c : Set α}, b ⊆ c → a ⊆ c := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true}) (by
  rfl)) (by
  simp)

-- Set.Subset.trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subset.trans.h5 : ¬∀ {α : Type} {a b c : Set α}, a ⊆ b → a ⊆ c := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  rfl)) (by
  simp)

-- List.Nodup.diff_eq_filter, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.diff_eq_filter.h2 : ¬∀ {α : Type} [inst : BEq α] {l₁ : List α} {l₂ : List α}, l₁.Nodup → LawfulBEq α := fun hc_h => absurd (@hc_h (ℕ) (⟨fun a b => a / 2 == b / 2⟩ : BEq ℕ) ([]) ([]) (by
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

-- List.minimum_of_length_pos_le_getElem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minimum_of_length_pos_le_getElem.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {i : ℕ}, i < l.length := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([]) (0)) (by
  decide +kernel)

-- List.minimum_of_length_pos_le_getElem, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.minimum_of_length_pos_le_getElem.h5.der.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] {l : List α} {i : ℕ}, i < l.length → 0 < l.length := by
  (intros; lia)
theorem HypCheckProof.List.minimum_of_length_pos_le_getElem.h5.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] {l : List α} {i : ℕ} (w : i < l.length),
      List.minimum_of_length_pos (HypCheckProof.List.minimum_of_length_pos_le_getElem.h5.der w) ≤ l[i] := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @List.minimum_of_length_pos_le_getElem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.List.minimum_of_length_pos_le_getElem.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- List.Nodup.set, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.set.h4 : ¬∀ {α : Type} {l : List α} {n : ℕ} {a : α}, a ∉ l → (l.set n a).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (2) (1) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.set, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.set.h5 : ¬∀ {α : Type} {l : List α} {n : ℕ} {a : α}, l.Nodup → (l.set n a).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.foldl_eq_foldr_of_commute, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.foldl_eq_foldr_of_commute.h4.inst : ¬List.foldl (fun (a b : Bool) => !(a && b)) Bool.false [Bool.false, Bool.true] =
        List.foldr (fun (a b : Bool) => !(a && b)) Bool.false [Bool.false, Bool.true] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.foldl_eq_foldr_of_commute.h4.prem0 : ∀ (x : Bool), (fun (a b : Bool) => !(a && b)) Bool.false x = (fun (a b : Bool) => !(a && b)) x Bool.false := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.foldl_eq_foldr_of_commute.h4 : ¬∀ {α : Type} {l : List α} {a : α} {f : α → α → α}, (∀ (x : α), f a x = f x a) → List.foldl f a l = List.foldr f a l := fun hc_h => HypCheckProof.List.foldl_eq_foldr_of_commute.h4.inst (@hc_h (Bool) ([Bool.false, Bool.true]) (Bool.false) (fun (a b : Bool) => !(a && b)) HypCheckProof.List.foldl_eq_foldr_of_commute.h4.prem0)

-- List.foldl_eq_foldr_of_commute, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.foldl_eq_foldr_of_commute.h5 : ¬∀ {α : Type} {l : List α} {a : α} {f : α → α → α} [inst : Std.Associative f], List.foldl f a l = List.foldr f a l := fun hc_h => absurd (@hc_h (ℕ) ([0]) (1) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done)))) (by
  decide +kernel)

-- List.Interleaves.pairwise_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Interleaves.pairwise_right.h5 : ¬∀ {α : Type} {r : α → α → Prop} {l₁ : List α} {l₂ : List α} [inst : IsTrans α r], List.Pairwise r l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([1, 0]) _) (by
  decide +kernel)

-- List.HasPeriod.getElem?_mod, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.HasPeriod.getElem?_mod.h4 : ¬∀ {α : Type} (p i : ℕ) (w : List α), i < w.length → w[i % p]? = w[i]? := fun hc_h => absurd (@hc_h (ℕ) (1) (1) ([0, 1]) (by
  decide)) (by
  decide +kernel)

-- List.HasPeriod.getElem?_mod, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.HasPeriod.getElem?_mod.h5 : ¬∀ {α : Type} (p i : ℕ) (w : List α), w.HasPeriod p → w[i % p]? = w[i]? := fun hc_h => absurd (@hc_h (ℕ) (1) (1) ([0]) (by
  simp)) (by
  decide +kernel)

-- List.le_maximum_of_length_pos_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_maximum_of_length_pos_of_mem.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {a : α} (w : 0 < l.length), a ≤ List.maximum_of_length_pos w := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (Nat.instLinearOrder) ([0]) (1) hc_k0) (by
  decide +kernel)

-- List.le_maximum_of_length_pos_of_mem, hypothesis 5: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.le_maximum_of_length_pos_of_mem.h5.der.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] {l : List α} {a : α}, a ∈ l → 0 < l.length := by
  (intros; grind)
theorem HypCheckProof.List.le_maximum_of_length_pos_of_mem.h5.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] {l : List α} {a : α} (h : a ∈ l),
      a ≤ List.maximum_of_length_pos (HypCheckProof.List.le_maximum_of_length_pos_of_mem.h5.der h) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4
  exact @List.le_maximum_of_length_pos_of_mem hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 (@HypCheckProof.List.le_maximum_of_length_pos_of_mem.h5.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4)

-- List.Shortlex.of_lex, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Shortlex.of_lex.h5 : ¬∀ {α : Type} {r : α → α → Prop} {s t : List α}, s.length = t.length → List.Shortlex r s t := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- List.length_splitLengths_getElem_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_splitLengths_getElem_eq.h4 : ¬∀ {α : Type} (l : List α) (sz : List ℕ) {i : ℕ}, (List.take (i + 1) sz).sum ≤ l.length → i < sz.length := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (0) (by
  decide)) (by
  decide +kernel)

-- List.length_splitLengths_getElem_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_splitLengths_getElem_eq.h5 : ¬∀ {α : Type} (l : List α) (sz : List ℕ) {i : ℕ} (hi : i < sz.length),
        List.length (GetElem.getElem (sz.splitLengths l) i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)) = GetElem.getElem sz i hi := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) ([]) ([1]) (0) hc_k0) (by
  decide +kernel)

-- Nat.chineseRemainderOfList_lt_prod, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.chineseRemainderOfList_lt_prod.h4.inst : ¬List.Pairwise (Function.onFun Nat.Coprime fun (a : Bool) => 2) [Bool.false, Bool.true] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.chineseRemainderOfList_lt_prod.h4.prem0 : ∀ i ∈ [Bool.false, Bool.true], (fun (a : Bool) => 2) i ≠ 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.chineseRemainderOfList_lt_prod.h4 : ¬∀ {ι : Type} (a s : ι → ℕ) (l : List ι), (∀ i ∈ l, s i ≠ 0) → List.Pairwise (Function.onFun Nat.Coprime s) l := fun hc_h => HypCheckProof.Nat.chineseRemainderOfList_lt_prod.h4.inst (@hc_h (Bool) (fun (b : Bool) => if b = Bool.true then 1 else 0) (fun (a : Bool) => 2) ([Bool.false, Bool.true]) HypCheckProof.Nat.chineseRemainderOfList_lt_prod.h4.prem0)

-- Nat.chineseRemainderOfList_lt_prod, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.chineseRemainderOfList_lt_prod.h5 : ¬∀ {ι : Type} (a s : ι → ℕ) (l : List ι) (co : List.Pairwise (Function.onFun Nat.Coprime s) l),
        ↑(Nat.chineseRemainderOfList a s l co) < (List.map s l).prod := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) ([0]) hc_k0) (by
  decide +kernel)

-- IsUnit.natCast_factorial_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsUnit.natCast_factorial_of_le.h3 : Not
      (∀ {A : Type} [inst : Semiring A] {n m : Nat},
        @LE.le Nat instLENat m n →
          @IsUnit A (@Semiring.toMonoid A inst)
            (@Nat.cast A
              (@AddMonoidWithOne.toNatCast A
                (@AddCommMonoidWithOne.toAddMonoidWithOne A
                  (@NonAssocSemiring.toAddCommMonoidWithOne A (@Semiring.toNonAssocSemiring A inst))))
              m.factorial)) := fun hc_h => absurd (@hc_h (Nat) (Nat.instSemiring) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- IsUnit.natCast_factorial_of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsUnit.natCast_factorial_of_le.h5 : Not
      (∀ {A : Type} [inst : Semiring A] {n : Nat},
        @IsUnit A (@Semiring.toMonoid A inst)
            (@Nat.cast A
              (@AddMonoidWithOne.toNatCast A
                (@AddCommMonoidWithOne.toAddMonoidWithOne A
                  (@NonAssocSemiring.toAddCommMonoidWithOne A (@Semiring.toNonAssocSemiring A inst))))
              n.factorial) →
          ∀ {m : Nat},
            @IsUnit A (@Semiring.toMonoid A inst)
              (@Nat.cast A
                (@AddMonoidWithOne.toNatCast A
                  (@AddCommMonoidWithOne.toAddMonoidWithOne A
                    (@NonAssocSemiring.toAddCommMonoidWithOne A (@Semiring.toNonAssocSemiring A inst))))
                m.factorial)) := fun hc_h => absurd (@hc_h (Nat) (Nat.instSemiring) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (by
  decide +kernel)

-- IsUnit.natCast_factorial_iff_of_charP, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsUnit.natCast_factorial_iff_of_charP.h3 : Not
      (∀ {A : Type} [inst : Ring A] (p : Nat)
        [inst_1 : @CharP A (@AddGroupWithOne.toAddMonoidWithOne A (@Ring.toAddGroupWithOne A inst)) p] {n : Nat},
        Iff
          (@IsUnit A (@Semiring.toMonoid A (@Ring.toSemiring A inst))
            (@Nat.cast A
              (@AddMonoidWithOne.toNatCast A (@AddGroupWithOne.toAddMonoidWithOne A (@Ring.toAddGroupWithOne A inst)))
              n.factorial))
          (@LT.lt Nat instLTNat n p)) := fun hc_h => absurd (@hc_h (Int) (Int.instRing) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) _ (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- IsUnit.natCast_factorial_iff_of_charP, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.IsUnit.natCast_factorial_iff_of_charP.h4 : Not
      (∀ {A : Type} [inst : Ring A] (p : Nat) [inst_1 : Fact (Nat.Prime p)] {n : Nat},
        Iff
          (@IsUnit A (@Semiring.toMonoid A (@Ring.toSemiring A inst))
            (@Nat.cast A
              (@AddMonoidWithOne.toNatCast A (@AddGroupWithOne.toAddMonoidWithOne A (@Ring.toAddGroupWithOne A inst)))
              n.factorial))
          (@LT.lt Nat instLTNat n p)) := fun hc_h => absurd (@hc_h (Bool) (@BooleanRing.toRing Bool instBooleanRingBool) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) _ (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (by
  decide +kernel)

-- Ordnode.Sized.balance', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.balance'.h4 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α}, r.Sized → (l.balance' x r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.nil) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Sized.balance', hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.balance'.h5 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α}, l.Sized → (l.balance' x r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.findMax'_all, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.findMax'_all.h4 : ¬∀ {α : Type} {P : α → Prop} (x : α) (t : Ordnode α), Ordnode.All P t → P (Ordnode.findMax' x t) := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (1) (Ordnode.nil) (by
  decide)) (by
  decide +kernel)

-- Ordnode.findMax'_all, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.findMax'_all.h5 : ¬∀ {α : Type} {P : α → Prop} (x : α) (t : Ordnode α), P x → P (Ordnode.findMax' x t) := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (0) (Ordnode.node 0 Ordnode.nil 1 Ordnode.nil) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Ordnode.Sized.rotateL, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.rotateL.h4 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α}, r.Sized → (l.rotateL x r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.nil) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Ordnode.Sized.rotateL, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.rotateL.h5 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {r : Ordnode α}, l.Sized → (l.rotateL x r).Sized := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil)) (by
  (repeat' constructor) <;> done)) (by
  nofun)

-- Disjoint.notMem_of_mem_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.notMem_of_mem_left.h3 : ¬∀ {α : Type} {s t : Set α} ⦃a : α⦄, a ∈ s → a ∉ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (0) (by
  decide)) (by
  decide +kernel)

-- Disjoint.notMem_of_mem_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.notMem_of_mem_left.h5 : ¬∀ {α : Type} {s t : Set α}, Disjoint s t → ∀ ⦃a : α⦄, a ∉ t := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (by
  simp) (0)) (by
  decide +kernel)

-- Set.disjoint_of_subset_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.disjoint_of_subset_left.h4 : ¬∀ {α : Type} {s t u : Set α}, Disjoint u t → Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Set.disjoint_of_subset_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.disjoint_of_subset_left.h5 : ¬∀ {α : Type} {s t u : Set α}, s ⊆ u → Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Set.disjoint_of_subset_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.disjoint_of_subset_right.h4 : ¬∀ {α : Type} {s t u : Set α}, Disjoint s u → Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Set.disjoint_of_subset_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.disjoint_of_subset_right.h5 : ¬∀ {α : Type} {s t u : Set α}, t ⊆ u → Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- Set.mem_of_mem_insert_of_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_of_mem_insert_of_ne.h4 : ¬∀ {α : Type} {s : Set α} {a b : α}, b ≠ a → b ∈ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Set.mem_of_mem_insert_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_of_mem_insert_of_ne.h5 : ¬∀ {α : Type} {s : Set α} {a b : α}, b ∈ Insert.insert a s → b ∈ s := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) (Bool.false) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Set.one_lt_ncard_of_nonempty_of_even, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.one_lt_ncard_of_nonempty_of_even.h2 : ¬∀ {α : Type} {s : Set α},
        autoParam s.Nonempty Set.one_lt_ncard_of_nonempty_of_even._auto_1 → Even s.ncard → 1 < s.ncard := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True}) (by
  simp) (by
  simp)) (by
  simp)

-- Set.one_lt_ncard_of_nonempty_of_even, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.one_lt_ncard_of_nonempty_of_even.h3 : ¬∀ {α : Type} {s : Set α}, s.Finite → Even s.ncard → 1 < s.ncard := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (by
  simp) (by
  simp)) (by
  simp)

-- Set.one_lt_ncard_of_nonempty_of_even, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.one_lt_ncard_of_nonempty_of_even.h4 : ¬∀ {α : Type} {s : Set α}, s.Finite → autoParam s.Nonempty Set.one_lt_ncard_of_nonempty_of_even._auto_1 → 1 < s.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (by
  simp) (by
  simp)) (by
  simp)

-- List.dlookup_map₁, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dlookup_map₁.h7 : Not
      (∀ {α α' : Type} [inst : DecidableEq α] [inst_1 : DecidableEq α'] {β : Type} (l : List (@Sigma α fun (x : α) => β))
        {f : α → α'} (a : α),
        @Eq (Option β)
          (@List.dlookup α' (fun (x : α') => β) inst_1 (f a)
            (@List.map (@Sigma α fun (x : α) => β) (@Sigma α' fun (x : α') => β)
              (@Sigma.map α α' (fun (x : α) => β) (fun (x : α') => β) f fun (x : α) => @id β) l))
          (@List.dlookup α (fun (x : α) => β) inst a l)) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (instDecidableEqNat) (Nat) (@List.cons (@Sigma Nat fun (x : Nat) => Nat)
      (@Sigma.mk Nat (fun (x : Nat) => Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@List.nil (@Sigma Nat fun (x : Nat) => Nat))) (fun _ => 0 : Nat → Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- EReal.div_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_pos.h2 : ¬∀ {a b : EReal}, 0 < b → b ≠ ⊤ → 0 < a / b := fun hc_h => absurd (@hc_h (0) (1) (by
  simp) (by
  decide)) (by
  simp)

-- EReal.div_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_pos.h3 : ¬∀ {a b : EReal}, 0 < a → b ≠ ⊤ → 0 < a / b := fun hc_h => absurd (@hc_h (1) (0) (by
  simp) (by
  decide)) (by
  simp)

-- Fin.comp_contractNth, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.comp_contractNth.h6 : ¬∀ {n : ℕ} {α β : Type} (opα : α → α → α) (opβ : β → β → β) {f : α → β} (j : Fin (n + 1)) (g : Fin (n + 1) → α),
        f ∘ j.contractNth opα g = j.contractNth opβ (f ∘ g) := fun hc_h => absurd (@hc_h (1) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (fun (a : Fin (1 + 1)) => 0)) (by
  decide +kernel)

-- DFinsupp.support_update_ne_zero, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.support_update_ne_zero.h8 : ¬∀ {ι : Type} {β : ι → Type} [inst : DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]
        [inst_2 : (i : ι) → (x : β i) → Decidable (x ≠ 0)] (f : Π₀ (i : ι), β i) (i : ι) {b : β i},
        (f.update i b).support = Insert.insert i f.support := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (fun (i : ℕ) => Nat.instMulZeroClass.toZero) (fun (i x : ℕ) => instDecidableNot) (0) (0) (0)) (by
  decide +kernel)

-- Matrix.submatrix_diagonal, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.submatrix_diagonal.h8 : ¬∀ {l m α : Type} [inst : Zero α] [inst_1 : DecidableEq m] [inst_2 : DecidableEq l] (d : m → α) (e : l → m),
        (Matrix.diagonal d).submatrix e e = Matrix.diagonal (d ∘ e) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (instDecidableEqNat) (instDecidableEqBool) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : Bool → ℕ)) (by
  decide +kernel)

-- Nat.factorization_eq_one_of_squarefree, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_one_of_squarefree.h2 : ¬∀ {n p : ℕ}, Nat.Prime p → p ∣ n → n.factorization p = 1 := fun hc_h => absurd (@hc_h (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_eq_one_of_squarefree, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_one_of_squarefree.h3 : ¬∀ {n p : ℕ}, Squarefree n → p ∣ n → n.factorization p = 1 := fun hc_h => absurd (@hc_h (1) (1) (by
  decide +kernel) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_eq_one_of_squarefree, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_one_of_squarefree.h4 : ¬∀ {n p : ℕ}, Squarefree n → Nat.Prime p → n.factorization p = 1 := fun hc_h => absurd (@hc_h (1) (2) (by
  decide +kernel) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_choose_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose_self.h2 : ¬∀ {p k : ℕ}, k ≠ 0 → k < p → p ∣ p.choose k := fun hc_h => absurd (@hc_h (4) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_choose_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose_self.h3 : ¬∀ {p k : ℕ}, Nat.Prime p → k < p → p ∣ p.choose k := fun hc_h => absurd (@hc_h (2) (0) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_choose_self, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_choose_self.h4 : ¬∀ {p k : ℕ}, Nat.Prime p → k ≠ 0 → p ∣ p.choose k := fun hc_h => absurd (@hc_h (2) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- DFinsupp.single_eq_of_sigma_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.single_eq_of_sigma_eq.h8 : Not
      (∀ {ι : Type} {β : ι → Type} [inst : (i : ι) → Zero (β i)] [inst_1 : DecidableEq ι] {i j : ι} {xi : β i} {xj : β j},
        @Eq (@DFinsupp ι (fun (i : ι) => β i) inst) (@DFinsupp.single ι β inst inst_1 i xi)
          (@DFinsupp.single ι β inst inst_1 j xj)) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun (i : Nat) => @MulZeroClass.toZero Nat Nat.instMulZeroClass) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Int.eq_zero_of_dvd_of_nonneg_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.eq_zero_of_dvd_of_nonneg_of_lt.h2 : ¬∀ {m n : ℤ}, m < n → n ∣ m → m = 0 := fun hc_h => absurd (@hc_h (-1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.eq_zero_of_dvd_of_nonneg_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.eq_zero_of_dvd_of_nonneg_of_lt.h3 : ¬∀ {m n : ℤ}, 0 ≤ m → n ∣ m → m = 0 := fun hc_h => absurd (@hc_h (1) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Int.eq_zero_of_dvd_of_nonneg_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.eq_zero_of_dvd_of_nonneg_of_lt.h4 : ¬∀ {m n : ℤ}, 0 ≤ m → m < n → m = 0 := fun hc_h => absurd (@hc_h (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.le_maxPrimeFac, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_maxPrimeFac.h2 : ¬∀ {n p : ℕ}, Nat.Prime p → p ∣ n → p ≤ n.maxPrimeFac := fun hc_h => absurd (@hc_h (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.le_maxPrimeFac, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_maxPrimeFac.h4 : ¬∀ {n p : ℕ}, n ≠ 0 → Nat.Prime p → p ≤ n.maxPrimeFac := fun hc_h => absurd (@hc_h (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- ZMod.prime_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.prime_ne_zero.h2 : Not
      (∀ (p q : Nat) [hq : Fact (Nat.Prime q)],
        @Ne Nat p q →
          @Ne (ZMod p)
            (@Nat.cast (ZMod p)
              (@AddMonoidWithOne.toNatCast (ZMod p)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod p)
                  (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p)))))
              q)
            (@OfNat.ofNat (ZMod p) (nat_lit 0)
              (@Zero.toOfNat0 (ZMod p)
                (@MulZeroClass.toZero (ZMod p)
                  (@instMulZeroClassOfSemiring (ZMod p)
                    (@CommSemiring.toSemiring (ZMod p) (@CommRing.toCommSemiring (ZMod p) (ZMod.commRing p)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) _ (by
  decide)) (by
  decide +kernel)

-- ZMod.prime_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.prime_ne_zero.h3 : Not
      (∀ (p q : Nat) [hp : Fact (Nat.Prime p)],
        @Ne Nat p q →
          @Ne (ZMod p)
            (@Nat.cast (ZMod p)
              (@AddMonoidWithOne.toNatCast (ZMod p)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod p)
                  (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p)))))
              q)
            (@OfNat.ofNat (ZMod p) (nat_lit 0)
              (@Zero.toOfNat0 (ZMod p)
                (@MulZeroClass.toZero (ZMod p)
                  (@instMulZeroClassOfSemiring (ZMod p)
                    (@CommSemiring.toSemiring (ZMod p) (@CommRing.toCommSemiring (ZMod p) (ZMod.commRing p)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) _ (by
  decide)) (by
  decide +kernel)

-- ZMod.prime_ne_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.prime_ne_zero.h4 : Not
      (∀ (p q : Nat) [hp : Fact (Nat.Prime p)] [hq : Fact (Nat.Prime q)],
        @Ne (ZMod p)
          (@Nat.cast (ZMod p)
            (@AddMonoidWithOne.toNatCast (ZMod p)
              (@AddGroupWithOne.toAddMonoidWithOne (ZMod p)
                (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p)))))
            q)
          (@OfNat.ofNat (ZMod p) (nat_lit 0)
            (@Zero.toOfNat0 (ZMod p)
              (@MulZeroClass.toZero (ZMod p)
                (@instMulZeroClassOfSemiring (ZMod p)
                  (@CommSemiring.toSemiring (ZMod p) (@CommRing.toCommSemiring (ZMod p) (ZMod.commRing p)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) _ _) (by
  decide +kernel)

-- DFinsupp.filter_single_neg, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.filter_single_neg.h8 : ¬∀ {ι : Type} {β : ι → Type} [inst : (i : ι) → Zero (β i)] [inst_1 : DecidableEq ι] {p : ι → Prop}
        [inst_2 : DecidablePred p] (i : ι) (x : β i), (DFinsupp.filter p fun₀ | i => x) = 0 := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (fun (i : ℕ) => Nat.instMulZeroClass.toZero) (instDecidableEqNat) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0) (1)) (by
  decide +kernel)

-- induction_on_primes, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.induction_on_primes.h2 : ¬∀ {motive : ℕ → Prop}, motive 0 → (∀ (p a : ℕ), Nat.Prime p → motive a → motive (p * a)) → ∀ (n : ℕ), motive n := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp) (1)) (by
  decide +kernel)

-- Sum.LiftRel.isLeft_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sum.LiftRel.isLeft_right.h8 : ¬∀ {α β γ δ : Type} {r : α → γ → Prop} {s : β → δ → Prop} {y : γ ⊕ δ} {a : α}, y.isLeft = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (Sum.inr 0) (0)) (by
  decide +kernel)

-- Nat.coprime_of_lt_prime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_of_lt_prime.h2 : ¬∀ {n p : ℕ}, n < p → Nat.Prime p → p.Coprime n := fun hc_h => absurd (@hc_h (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.coprime_of_lt_prime, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_of_lt_prime.h3 : ¬∀ {n p : ℕ}, n ≠ 0 → Nat.Prime p → p.Coprime n := fun hc_h => absurd (@hc_h (2) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.coprime_of_lt_prime, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_of_lt_prime.h4 : ¬∀ {n p : ℕ}, n ≠ 0 → n < p → p.Coprime n := fun hc_h => absurd (@hc_h (2) (4) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.not_prime_of_dvd_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_prime_of_dvd_of_lt.h2 : ¬∀ {m n : ℕ}, 2 ≤ m → m < n → ¬Nat.Prime n := fun hc_h => absurd (@hc_h (2) (3) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.not_prime_of_dvd_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_prime_of_dvd_of_lt.h3 : ¬∀ {m n : ℕ}, m ∣ n → m < n → ¬Nat.Prime n := fun hc_h => absurd (@hc_h (1) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.not_prime_of_dvd_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_prime_of_dvd_of_lt.h4 : ¬∀ {m n : ℕ}, m ∣ n → 2 ≤ m → ¬Nat.Prime n := fun hc_h => absurd (@hc_h (2) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.mem_primeFactors', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.mem_primeFactors'.h2 : ¬∀ {n p : ℕ}, p ∣ n → ∀ [inst : NeZero n], p ∈ n.primeFactors := fun hc_h => absurd (@hc_h (1) (1) (by
  decide) _) (by
  decide +kernel)

-- Nat.Prime.mem_primeFactors', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.mem_primeFactors'.h3 : ¬∀ {n p : ℕ}, Nat.Prime p → ∀ [inst : NeZero n], p ∈ n.primeFactors := fun hc_h => absurd (@hc_h (1) (2) (by
  decide) _) (by
  decide +kernel)

-- Nat.Prime.mem_primeFactors', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.mem_primeFactors'.h4 : ¬∀ {n p : ℕ}, Nat.Prime p → p ∣ n → p ∈ n.primeFactors := fun hc_h => absurd (@hc_h (0) (2) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Fin.castPred_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_ne_zero.h3 : ¬∀ {n : ℕ} [inst : NeZero n] {i : Fin (n + 1)}, i ≠ 0 → i ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) _ ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.castPred_ne_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_ne_zero.h4 : ¬∀ {n : ℕ} [inst : NeZero n] {i : Fin (n + 1)} (h₁ : i ≠ Fin.last n), i.castPred h₁ ≠ 0 := fun hc_h => absurd (fun hc_k0 => @hc_h (1) _ ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) hc_k0) (by
  decide +kernel)

-- Nat.digits_getLast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_getLast.h4 : ¬∀ {b : ℕ} (m : ℕ), 1 < b → b.digits m ≠ [] → b.digits (m / b) ≠ [] := fun hc_h => absurd (@hc_h (2) (1) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Matrix.diagonal_map, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.diagonal_map.h7 : ¬∀ {n α β : Type} [inst : DecidableEq n] [inst_1 : Zero α] [inst_2 : Zero β] {f : α → β} {d : n → α},
        (Matrix.diagonal d).map f = Matrix.diagonal fun (m : n) => f (d m) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (ℕ) (instDecidableEqBool) (Nat.instMulZeroClass.toZero) (Nat.instMulZeroClass.toZero) (fun n => n + 1 : ℕ → ℕ) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  decide +kernel)

-- Finset.sorted_zero_eq_min'_aux, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finset.sorted_zero_eq_min'_aux.h3.der.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] (s : Finset α), s.Nonempty → 0 < (s.sort fun (a b : α) => a ≤ b).length := by
  (intros; simp_all; done)
theorem HypCheckProof.Finset.sorted_zero_eq_min'_aux.h3.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] (s : Finset α) (H : s.Nonempty),
      (s.sort fun (a b : α) => a ≤ b).get
          (⟨0, HypCheckProof.Finset.sorted_zero_eq_min'_aux.h3.der s H⟩ : Fin (s.sort fun (a b : α) => a ≤ b).length) =
        s.min' H := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Finset.sorted_zero_eq_min'_aux hc_x0 hc_x1 hc_x2 (@HypCheckProof.Finset.sorted_zero_eq_min'_aux.h3.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x3

-- Finset.sorted_zero_eq_min'_aux, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finset.sorted_zero_eq_min'_aux.h4.der.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] (s : Finset α), 0 < (s.sort fun (a b : α) => a ≤ b).length → s.Nonempty := by
  (intros; simp_all; done)
theorem HypCheckProof.Finset.sorted_zero_eq_min'_aux.h4.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] (s : Finset α) (h : 0 < (s.sort fun (a b : α) => a ≤ b).length),
      (s.sort fun (a b : α) => a ≤ b).get (⟨0, h⟩ : Fin (s.sort fun (a b : α) => a ≤ b).length) =
        s.min' (HypCheckProof.Finset.sorted_zero_eq_min'_aux.h4.der s h) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Finset.sorted_zero_eq_min'_aux hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Finset.sorted_zero_eq_min'_aux.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- Finset.sorted_last_eq_max'_aux, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finset.sorted_last_eq_max'_aux.h3.der.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] (s : Finset α),
      @Finset.Nonempty α s →
        @LT.lt Nat instLTNat
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
            (@List.length α
              (@Finset.sort α s
                (fun (a b : α) =>
                  @LE.le α
                    (@Preorder.toLE α
                      (@PartialOrder.toPreorder α
                        (@SemilatticeInf.toPartialOrder α
                          (@Lattice.toSemilatticeInf α
                            (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
                    a b)
                (@LinearOrder.toDecidableLE α inst)
                (@IsPreorder.toIsTrans α
                  (fun (a b : α) =>
                    @LE.le α
                      (@Preorder.toLE α
                        (@PartialOrder.toPreorder α
                          (@SemilatticeInf.toPartialOrder α
                            (@Lattice.toSemilatticeInf α
                              (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
                      a b)
                  (@instIsPreorderLe α
                    (@PartialOrder.toPreorder α
                      (@SemilatticeInf.toPartialOrder α
                        (@Lattice.toSemilatticeInf α
                          (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst)))))))
                (@instAntisymmLe_mathlib α
                  (@SemilatticeInf.toPartialOrder α
                    (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst)))))
                (@instTotalLe_mathlib α inst)))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@List.length α
            (@Finset.sort α s
              (fun (a b : α) =>
                @LE.le α
                  (@Preorder.toLE α
                    (@PartialOrder.toPreorder α
                      (@SemilatticeInf.toPartialOrder α
                        (@Lattice.toSemilatticeInf α
                          (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
                  a b)
              (@LinearOrder.toDecidableLE α inst)
              (@IsPreorder.toIsTrans α
                (fun (a b : α) =>
                  @LE.le α
                    (@Preorder.toLE α
                      (@PartialOrder.toPreorder α
                        (@SemilatticeInf.toPartialOrder α
                          (@Lattice.toSemilatticeInf α
                            (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
                    a b)
                (@instIsPreorderLe α
                  (@PartialOrder.toPreorder α
                    (@SemilatticeInf.toPartialOrder α
                      (@Lattice.toSemilatticeInf α
                        (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst)))))))
              (@instAntisymmLe_mathlib α
                (@SemilatticeInf.toPartialOrder α
                  (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst)))))
              (@instTotalLe_mathlib α inst))) := by
  (intros; simp_all; done)
theorem HypCheckProof.Finset.sorted_last_eq_max'_aux.h3.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] (s : Finset α) (H : @Finset.Nonempty α s),
      @Eq α
        (@GetElem.getElem (List α) Nat α (fun (as : List α) (i : Nat) => @LT.lt Nat instLTNat i (@List.length α as))
          (@List.instGetElemNatLtLength α)
          (@Finset.sort α s
            (fun (a b : α) =>
              @LE.le α
                (@Preorder.toLE α
                  (@PartialOrder.toPreorder α
                    (@SemilatticeInf.toPartialOrder α
                      (@Lattice.toSemilatticeInf α
                        (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
                a b)
            (@LinearOrder.toDecidableLE α inst)
            (@IsPreorder.toIsTrans α
              (fun (a b : α) =>
                @LE.le α
                  (@Preorder.toLE α
                    (@PartialOrder.toPreorder α
                      (@SemilatticeInf.toPartialOrder α
                        (@Lattice.toSemilatticeInf α
                          (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
                  a b)
              (@instIsPreorderLe α
                (@PartialOrder.toPreorder α
                  (@SemilatticeInf.toPartialOrder α
                    (@Lattice.toSemilatticeInf α
                      (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst)))))))
            (@instAntisymmLe_mathlib α
              (@SemilatticeInf.toPartialOrder α
                (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst)))))
            (@instTotalLe_mathlib α inst))
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
            (@List.length α
              (@Finset.sort α s
                (fun (a b : α) =>
                  @LE.le α
                    (@Preorder.toLE α
                      (@PartialOrder.toPreorder α
                        (@SemilatticeInf.toPartialOrder α
                          (@Lattice.toSemilatticeInf α
                            (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
                    a b)
                (@LinearOrder.toDecidableLE α inst)
                (@IsPreorder.toIsTrans α
                  (fun (a b : α) =>
                    @LE.le α
                      (@Preorder.toLE α
                        (@PartialOrder.toPreorder α
                          (@SemilatticeInf.toPartialOrder α
                            (@Lattice.toSemilatticeInf α
                              (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst))))))
                      a b)
                  (@instIsPreorderLe α
                    (@PartialOrder.toPreorder α
                      (@SemilatticeInf.toPartialOrder α
                        (@Lattice.toSemilatticeInf α
                          (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst)))))))
                (@instAntisymmLe_mathlib α
                  (@SemilatticeInf.toPartialOrder α
                    (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst)))))
                (@instTotalLe_mathlib α inst)))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HypCheckProof.Finset.sorted_last_eq_max'_aux.h3.der α inst s H))
        (@Finset.max' α inst s H) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Finset.sorted_last_eq_max'_aux hc_x0 hc_x1 hc_x2 (@HypCheckProof.Finset.sorted_last_eq_max'_aux.h3.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x3

-- Finset.sorted_last_eq_max'_aux, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finset.sorted_last_eq_max'_aux.h4.der.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] (s : Finset α),
      (s.sort fun (a b : α) => a ≤ b).length - 1 < (s.sort fun (a b : α) => a ≤ b).length → s.Nonempty := by
  (intros; simp_all; done)
theorem HypCheckProof.Finset.sorted_last_eq_max'_aux.h4.{u_1} : ∀ {α : Type u_1} [inst : LinearOrder α] (s : Finset α)
      (h : (s.sort fun (a b : α) => a ≤ b).length - 1 < (s.sort fun (a b : α) => a ≤ b).length),
      (s.sort fun (a b : α) => a ≤ b)[(s.sort fun (a b : α) => a ≤ b).length - 1] =
        s.max' (HypCheckProof.Finset.sorted_last_eq_max'_aux.h4.der s h) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Finset.sorted_last_eq_max'_aux hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Finset.sorted_last_eq_max'_aux.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- Set.Nonempty.eq_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.eq_zero.h1 : ¬∀ {α : Type} [inst : Zero α] {s : Set α}, s.Nonempty → s = {0} := fun hc_h => absurd (@hc_h (Bool) (instZeroBool_mathlib) ({b : Bool | b = Bool.true}) (by
  simp)) (by
  simp)

-- Set.Nonempty.eq_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.eq_zero.h4 : ¬∀ {α : Type} [inst : Subsingleton α] [inst : Zero α] {s : Set α}, s = {0} := fun hc_h => absurd (@hc_h (Unit) _ (PUnit.instZero_mathlib) (∅)) (by
  simp)

-- Set.exists_mem_notMem_of_ncard_lt_ncard, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_mem_notMem_of_ncard_lt_ncard.h3 : ¬∀ {α : Type} {s t : Set α}, autoParam s.Finite Set.exists_mem_notMem_of_ncard_lt_ncard._auto_1 → ∃ e ∈ t, e ∉ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.exists_mem_notMem_of_ncard_lt_ncard, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_mem_notMem_of_ncard_lt_ncard.h4 : ¬∀ {α : Type} {s t : Set α}, s.ncard < t.ncard → ∃ e ∈ t, e ∉ s := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.ncard_insert_of_notMem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_insert_of_notMem.h3 : ¬∀ {α : Type} {s : Set α} {a : α},
        autoParam s.Finite Set.ncard_insert_of_notMem._auto_1 → (Insert.insert a s).ncard = s.ncard + 1 := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0) (by
  simp)) (by
  simp)

-- Set.BijOn.iInter_comp, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.iInter_comp.h7 : ¬∀ {α β γ : Type} {s : Set β} {t : Set γ} {f : β → γ} (g : γ → Set α), ⋂ x ∈ s, g (f x) = ⋂ y ∈ t, g y := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (fun n => n + 1 : ℕ → ℕ) (fun (a : ℕ) => {n : ℕ | n = 0})) (by
  simp)

-- Nat.Prime.dvd_of_dvd_pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_of_dvd_pow.h4 : ¬∀ {p m : ℕ} {n : ℕ}, Nat.Prime p → p ∣ m := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.mem_primeFactorsList_mul_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mem_primeFactorsList_mul_left.h3 : ¬∀ {p a b : ℕ}, b ≠ 0 → p ∈ (a * b).primeFactorsList := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.mem_primeFactorsList_mul_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mem_primeFactorsList_mul_left.h4 : ¬∀ {p a b : ℕ}, p ∈ a.primeFactorsList → p ∈ (a * b).primeFactorsList := fun hc_h => absurd (@hc_h (2) (2) (0) (by
  decide +kernel)) (by
  decide +kernel)

-- Set.ncard_diff', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_diff'.h3 : ¬∀ {α : Type} {s t : Set α}, autoParam t.Finite Set.ncard_sdiff'._auto_1 → (t \ s).ncard = t.ncard - s.ncard := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (by
  simp)) (by
  simp)

-- ZMod.natAbs_min_of_le_div_two, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.natAbs_min_of_le_div_two.h3 : ¬∀ (n : ℕ) (x y : ℤ), x.natAbs ≤ n / 2 → x.natAbs ≤ y.natAbs := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide)) (by
  decide +kernel)

-- ZMod.natAbs_min_of_le_div_two, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.natAbs_min_of_le_div_two.h4 : Not
      (∀ (n : Nat) (x y : Int),
        @Eq (ZMod n)
            (@Int.cast (ZMod n)
              (@AddGroupWithOne.toIntCast (ZMod n)
                (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
              x)
            (@Int.cast (ZMod n)
              (@AddGroupWithOne.toIntCast (ZMod n)
                (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
              y) →
          @LE.le Nat instLENat x.natAbs y.natAbs) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- not_injective_infinite_finite, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.not_injective_infinite_finite.h2 : ¬∀ {α β : Type} [inst : Finite β] (f : α → β), ¬Function.Injective f := fun hc_h => absurd (@hc_h (Bool) (Bool) _ (not : Bool → Bool)) (by
  decide +kernel)

-- ZMod.castHom_comp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.castHom_comp.h3 : ¬∀ {n m d : ℕ}, m ∣ d → n ∣ m := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- ZMod.castHom_comp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.castHom_comp.h4 : ¬∀ {n m d : ℕ}, n ∣ m → m ∣ d := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.nat_repr_len_aux, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Nat.nat_repr_len_aux.h3.gneg : ∀ (n b e : ℕ), ¬0 < b → n < b ^ e.succ → n / b < b ^ e := by
  (intros; lia)
theorem HypCheckProof.Nat.nat_repr_len_aux.h3 : ∀ (n b e : ℕ), n < b ^ e.succ → n / b < b ^ e := by
  intro hc_x0 hc_x1 hc_x2 hc_x4
  exact Classical.byCases (fun hc_h => @Nat.nat_repr_len_aux hc_x0 hc_x1 hc_x2 hc_h hc_x4) (fun hc_hn => @HypCheckProof.Nat.nat_repr_len_aux.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4)
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Nat.nat_repr_len_aux.h3.derivable : ∀ (n b e : ℕ), n < b ^ e.succ → 0 < b := by
  (intros; lia)

-- Nat.nat_repr_len_aux, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nat_repr_len_aux.h4 : ¬∀ (n b e : ℕ), 0 < b → n / b < b ^ e := fun hc_h => absurd (@hc_h (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.toDigits_length, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toDigits_length.h3 : ¬∀ (b n e : ℕ), n < b ^ e → (b.toDigits n).length ≤ e := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.toDigits_length, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toDigits_length.h4 : ¬∀ (b n e : ℕ), 0 < e → (b.toDigits n).length ≤ e := fun hc_h => absurd (@hc_h (1) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.ofDigits_div_pow_eq_ofDigits_drop, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofDigits_div_pow_eq_ofDigits_drop.h4 : ¬∀ {p : ℕ} (i : ℕ), 0 < p → ∀ (digits : List ℕ), Nat.ofDigits p digits / p ^ i = Nat.ofDigits p (List.drop i digits) := fun hc_h => absurd (@hc_h (1) (1) (by
  decide) ([1])) (by
  decide +kernel)

-- Nat.digits_lt_base, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_lt_base.h3 : ¬∀ {b m d : ℕ}, d ∈ b.digits m → d < b := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.digits_lt_base, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_lt_base.h4 : ¬∀ {b : ℕ} {m : ℕ} {d : ℕ}, 1 < b → d < b := fun hc_h => absurd (@hc_h (2) (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.length_digitsAppend, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.length_digitsAppend.h4 : ¬∀ {n b : ℕ}, 1 < b → ∀ (l : ℕ), (b.digitsAppend l n).length = l := fun hc_h => absurd (@hc_h (1) (2) (by
  decide) (0)) (by
  decide +kernel)

-- Nat.pow_dvd_iff_le_multiplicity, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_dvd_iff_le_multiplicity.h3 : ¬∀ {p k n : ℕ}, n ≠ 0 → (p ^ k ∣ n ↔ k ≤ multiplicity p n) := fun hc_h => absurd (@hc_h (1) (1) (1) (by
  decide)) (by
  simp)

-- Nat.pow_dvd_iff_le_padicValNat, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_dvd_iff_le_padicValNat.h3 : ¬∀ {p k n : ℕ}, n ≠ 0 → (p ^ k ∣ n ↔ k ≤ multiplicity p n) := fun hc_h => absurd (@hc_h (1) (1) (1) (by
  decide)) (by
  simp)

-- Set.ncard_diff_singleton_add_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_diff_singleton_add_one.h3 : ¬∀ {α : Type} {s : Set α} {a : α},
        autoParam s.Finite Set.ncard_sdiff_singleton_add_one._auto_1 → (s \ {a}).ncard + 1 = s.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1) (by
  simp)) (by
  simp)

-- Nat.Prime.pow_dvd_iff_dvd_ordProj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.pow_dvd_iff_dvd_ordProj.h3 : ¬∀ {p k n : ℕ}, n ≠ 0 → (p ^ k ∣ n ↔ p ^ k ∣ p ^ n.factorization p) := fun hc_h => absurd (@hc_h (4) (1) (4) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.pow_dvd_iff_dvd_ordProj, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.pow_dvd_iff_dvd_ordProj.h4 : ¬∀ {p k n : ℕ}, Nat.Prime p → (p ^ k ∣ n ↔ p ^ k ∣ p ^ n.factorization p) := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.pow_dvd_iff_le_factorization, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.pow_dvd_iff_le_factorization.h3 : ¬∀ {p k n : ℕ}, n ≠ 0 → (p ^ k ∣ n ↔ k ≤ n.factorization p) := fun hc_h => absurd (@hc_h (1) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.pow_dvd_iff_le_factorization, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.pow_dvd_iff_le_factorization.h4 : ¬∀ {p k n : ℕ}, Nat.Prime p → (p ^ k ∣ n ↔ k ≤ n.factorization p) := fun hc_h => absurd (@hc_h (2) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ordProj_dvd_ordProj_of_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordProj_dvd_ordProj_of_dvd.h2 : ¬∀ {a b : ℕ}, a ∣ b → ∀ (p : ℕ), p ^ a.factorization p ∣ p ^ b.factorization p := fun hc_h => absurd (@hc_h (2) (0) (by
  decide) (2)) (by
  decide +kernel)

-- Nat.ordProj_dvd_ordProj_of_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordProj_dvd_ordProj_of_dvd.h3 : ¬∀ {a b : ℕ}, b ≠ 0 → ∀ (p : ℕ), p ^ a.factorization p ∣ p ^ b.factorization p := fun hc_h => absurd (@hc_h (2) (1) (by
  decide) (2)) (by
  decide +kernel)

-- Nat.factorization_le_factorization_choose_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_le_factorization_choose_add.h3 : ¬∀ {p n k : ℕ}, k ≠ 0 → n.factorization p ≤ (n.choose k).factorization p + k.factorization p := fun hc_h => absurd (@hc_h (2) (2) (3) (by
  decide)) (by
  decide +kernel)

-- Nat.factorization_le_factorization_choose_add, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_le_factorization_choose_add.h4 : ¬∀ {p n k : ℕ}, k ≤ n → n.factorization p ≤ (n.choose k).factorization p + k.factorization p := fun hc_h => absurd (@hc_h (2) (2) (0) (by
  decide)) (by
  decide +kernel)

-- Multiset.fold_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_zero.h2 : ¬∀ {α : Type} (op : α → α → α) [ha : Std.Associative op] (b : α), Std.Commutative op := fun hc_h => absurd (@hc_h (ℕ) (fun a _ => a : ℕ → ℕ → ℕ) (@Std.Associative.mk (Nat) (fun (a x : Nat) => a) (by (try dsimp only);   (intros; simp_all; done))) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.comm (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.fold_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.fold_zero.h3 : ¬∀ {α : Type} (op : α → α → α) [hc : Std.Commutative op] (b : α), Std.Associative op := fun hc_h => absurd (@hc_h (Bool) (fun a b => !(a && b) : Bool → Bool → Bool) (@Std.Commutative.mk (Bool) (fun (a b : Bool) => (a.and b).not) (by (try dsimp only);   decide)) (Bool.false)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.true : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.Infinite.diff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.diff.h3 : ¬∀ {α : Type} {s t : Set α}, t.Finite → (s \ t).Infinite := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Set.Infinite.sdiff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.sdiff.h3 : ¬∀ {α : Type} {s t : Set α}, t.Finite → (s \ t).Infinite := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Set.ncard_lt_ncard, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_lt_ncard.h3 : ¬∀ {α : Type} {s t : Set α}, autoParam t.Finite Set.ncard_lt_ncard._auto_1 → s.ncard < t.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.ncard_lt_ncard, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_lt_ncard.h4 : ¬∀ {α : Type} {s t : Set α}, s ⊂ t → s.ncard < t.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | True}) (by
  simp)) (by
  simp)

-- List.Nodup.pairwise_of_set_pairwise, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.pairwise_of_set_pairwise.h3 : ¬∀ {α : Type} {l : List α} {r : α → α → Prop}, {x : α | x ∈ l}.Pairwise r → List.Pairwise r l := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (fun a b => a < b : ℕ → ℕ → Prop) (by
  simp)) (by
  decide +kernel)

-- List.Nodup.pairwise_of_set_pairwise, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.pairwise_of_set_pairwise.h4 : ¬∀ {α : Type} {l : List α} {r : α → α → Prop}, l.Nodup → List.Pairwise r l := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (fun a b => a < b : ℕ → ℕ → Prop) (by
  decide)) (by
  decide +kernel)

-- Set.nonempty_inter_of_lt_ncard_add_ncard, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nonempty_inter_of_lt_ncard_add_ncard.h3 : ¬∀ {α : Type} {s t : Set α}, Nat.card α < s.ncard + t.ncard → (s ∩ t).Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- Set.nonempty_inter_of_lt_ncard_add_ncard, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nonempty_inter_of_lt_ncard_add_ncard.h4 : ¬∀ {α : Type} {s t : Set α} [inst : Finite α], (s ∩ t).Nonempty := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) _) (by
  simp)

-- Bool.or_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.or_le.h3 : ¬∀ {x y z : Bool}, y ≤ z → (x || y) ≤ z := fun hc_h => absurd (@hc_h (Bool.true) (Bool.false) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Bool.or_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.or_le.h4 : ¬∀ {x y z : Bool}, x ≤ z → (x || y) ≤ z := fun hc_h => absurd (@hc_h (Bool.false) (Bool.true) (Bool.false) (by
  decide)) (by
  decide +kernel)

-- Set.Infinite.exists_notMem_finite, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.exists_notMem_finite.h3 : ¬∀ {α : Type} {s t : Set α}, t.Finite → ∃ a ∈ s, a ∉ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- Set.ne_univ_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ne_univ_of_subset.h3 : ¬∀ {α : Type} {s t : Set α}, s ≠ Set.univ → t ≠ Set.univ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | True}) (by
  simp)) (by
  simp)

-- Set.ne_univ_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ne_univ_of_subset.h4 : ¬∀ {α : Type} {s t : Set α}, t ⊆ s → t ≠ Set.univ := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True}) ({x : ℕ | True}) (by
  rfl)) (by
  simp)

-- Set.SurjOn.comp_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.comp_left.h6 : ¬∀ {α β γ : Type} {s : Set α} {t : Set β} {f : α → β} (g : β → γ), Set.SurjOn (g ∘ f) s (g '' t) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Computation.results_of_terminates', hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Computation.results_of_terminates'.h2.der.{u} : ∀ {α : Type u} (s : Computation α) {a : α},
      @Membership.mem α (Computation α) (@Computation.instMembership α) s a → @Computation.Terminates α s := by
  (intros; solve_by_elim)
theorem HypCheckProof.Computation.results_of_terminates'.h2.{u} : ∀ {α : Type u} (s : Computation α) {a : α} (h : @Membership.mem α (Computation α) (@Computation.instMembership α) s a),
      @Computation.Results α s a
        (@Computation.length α s (@HypCheckProof.Computation.results_of_terminates'.h2.der α s a h)) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Computation.results_of_terminates' hc_x0 hc_x1 (@HypCheckProof.Computation.results_of_terminates'.h2.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x2 hc_x3

-- Set.nontrivial_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_mono.h4 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t → Nontrivial ↑t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  nofun)

-- Nat.log_anti_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_anti_left.h3 : ¬∀ {b c n : ℕ}, c ≤ b → Nat.log b n ≤ Nat.log c n := fun hc_h => absurd (@hc_h (2) (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.log_anti_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_anti_left.h4 : ¬∀ {b c n : ℕ}, 1 < c → Nat.log b n ≤ Nat.log c n := fun hc_h => absurd (@hc_h (2) (3) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.pow_le_of_le_log, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_le_of_le_log.h3 : ¬∀ {b x y : ℕ}, x ≤ Nat.log b y → b ^ x ≤ y := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.pow_le_of_le_log, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_le_of_le_log.h4 : ¬∀ {b x y : ℕ}, y ≠ 0 → b ^ x ≤ y := fun hc_h => absurd (@hc_h (2) (1) (1) (by
  decide)) (by
  decide +kernel)

-- List.Vector.get_append_cons_succ, hypothesis 7: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.Vector.get_append_cons_succ.h7.der.{u_1} : ∀ {α : Type u_1} {m n : Nat} {x : α} (xs : List.Vector α n) (ys : List.Vector α m)
      {i : Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n m)},
      @LT.lt Nat instLTNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@Fin.val (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n m) i)
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n.succ m) := by
  (intros; lia)
theorem HypCheckProof.List.Vector.get_append_cons_succ.h7.{u_1} : ∀ {α : Type u_1} {m n : Nat} {x : α} (xs : List.Vector α n) (ys : List.Vector α m)
      {i : Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n m)},
      @Eq α
        (@List.Vector.get α (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n.succ m)
          (@HAppend.hAppend (List.Vector α n.succ) (List.Vector α m)
            (List.Vector α (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n.succ m))
            (@List.Vector.instHAppendHAddNat α n.succ m) (@List.Vector.cons α n x xs) ys)
          (@Fin.mk (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n.succ m)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@Fin.val (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n m) i)
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@HypCheckProof.List.Vector.get_append_cons_succ.h7.der α m n x xs ys i)))
        (@List.Vector.get α (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n m)
          (@HAppend.hAppend (List.Vector α n) (List.Vector α m)
            (List.Vector α (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n m)) (@List.Vector.instHAppendHAddNat α n m)
            xs ys)
          i) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6
  exact @List.Vector.get_append_cons_succ hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 (@HypCheckProof.List.Vector.get_append_cons_succ.h7.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6)

-- Nat.clog_anti_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_anti_left.h3 : ¬∀ {b c n : ℕ}, c ≤ b → Nat.clog b n ≤ Nat.clog c n := fun hc_h => absurd (@hc_h (2) (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.clog_anti_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_anti_left.h4 : ¬∀ {b c n : ℕ}, 1 < c → Nat.clog b n ≤ Nat.clog c n := fun hc_h => absurd (@hc_h (2) (3) (3) (by
  decide)) (by
  decide +kernel)

-- Nat.lt_pow_of_log_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_pow_of_log_lt.h3 : ¬∀ {b x y : ℕ}, Nat.log b y < x → y < b ^ x := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.lt_pow_of_log_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_pow_of_log_lt.h4 : ¬∀ {b x y : ℕ}, 1 < b → y < b ^ x := fun hc_h => absurd (@hc_h (2) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.log_eq_of_pow_le_of_lt_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_eq_of_pow_le_of_lt_pow.h3 : ¬∀ {b m n : ℕ}, n < b ^ (m + 1) → Nat.log b n = m := fun hc_h => absurd (@hc_h (1) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.log_eq_of_pow_le_of_lt_pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_eq_of_pow_le_of_lt_pow.h4 : ¬∀ {b m n : ℕ}, b ^ m ≤ n → Nat.log b n = m := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.log_lt_of_lt_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_lt_of_lt_pow.h3 : ¬∀ {b x y : ℕ}, y < b ^ x → Nat.log b y < x := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.log_lt_of_lt_pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_lt_of_lt_pow.h4 : ¬∀ {b x y : ℕ}, y ≠ 0 → Nat.log b y < x := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.rel_getLast_dropLast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.rel_getLast_dropLast.h3 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} (hne : l.dropLast ≠ []),
        R (l.dropLast.getLast hne)
          (l.getLast
            ((fun {α : Type} {l : List α} (hne : l.dropLast ≠ []) =>
                (fun {α : Type} {l : List α} (hne : l.dropLast ≠ []) =>
                    Classical.byContradiction
                      (Lean.Grind.intro_with_eq (¬¬l = []) (l = []) False (Lean.Grind.not_not (l = []))
                        fun (h_1 : l = []) =>
                        id
                          (Eq.mp
                            (Eq.trans
                              (Eq.symm
                                (eq_true
                                  (Eq.trans (congrArg List.dropLast h_1)
                                    (Eq.mp (Eq.refl ([].dropLast = [])) List.dropLast_nil))))
                              (eq_false hne))
                            True.intro)))
                  hne)
              hne)) := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0]) hc_k0) (by
  decide +kernel)

-- List.IsChain.rel_getLast_dropLast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.rel_getLast_dropLast.h4 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α}, List.IsChain R l → l.dropLast ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) (by
  decide)) (by
  decide +kernel)

-- DFinsupp.support_single, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.support_single.h7 : Not
      (∀ {ι : Type} {β : ι → Type} [inst : DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]
        [inst_2 :
          (i : ι) → (x : β i) → Decidable (@Ne (β i) x (@OfNat.ofNat (β i) (nat_lit 0) (@Zero.toOfNat0 (β i) (inst_1 i))))]
        {i : ι} {b : β i},
        @Eq (Finset ι) (@DFinsupp.support ι β inst inst_1 inst_2 (@DFinsupp.single ι β inst_1 inst i b))
          (@Singleton.singleton ι (Finset ι) (@Finset.instSingleton ι) i)) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (instDecidableEqNat) (fun (i : Nat) => @MulZeroClass.toZero Nat Nat.instMulZeroClass) (fun (i x : Nat) =>
      @instDecidableNot
        (@Eq ((fun (a : Nat) => Nat) i) x
          (@OfNat.ofNat ((fun (a : Nat) => Nat) i) (nat_lit 0)
            (@Zero.toOfNat0 ((fun (a : Nat) => Nat) i)
              ((fun (i : Nat) => @MulZeroClass.toZero Nat Nat.instMulZeroClass) i))))
        (instDecidableEqNat x
          (@OfNat.ofNat ((fun (a : Nat) => Nat) i) (nat_lit 0)
            (@Zero.toOfNat0 ((fun (a : Nat) => Nat) i)
              ((fun (i : Nat) => @MulZeroClass.toZero Nat Nat.instMulZeroClass) i))))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- DFinsupp.comapDomain_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.comapDomain_add.h5 : ¬∀ {ι : Type} {β : ι → Type} {κ : Type} [inst : (i : ι) → AddZeroClass (β i)] (h : κ → ι) (f g : Π₀ (i : ι), β i),
        Function.Injective h := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (ℕ) (fun (i : ℕ) => Nat.instAddMonoid.toAddZeroClass) (fun _ => 0 : ℕ → ℕ) (0) (0)) (by
  simp)

-- EReal.div_le_div_right_of_nonpos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_le_div_right_of_nonpos.h3 : ¬∀ {a b c : EReal}, a ≤ b → b / c ≤ a / c := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  simp)) (by
  (simp <;> omega))

-- EReal.mul_le_mul_of_nonpos_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.mul_le_mul_of_nonpos_right.h4 : ¬∀ {a b c : EReal}, b ≤ a → a * c ≤ b * c := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  simp)) (by
  simp)

-- EReal.le_div_iff_mul_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.le_div_iff_mul_le.h3 : ¬∀ {a b c : EReal}, b ≠ ⊤ → (a ≤ c / b ↔ a * b ≤ c) := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide)) (by
  simp)

-- DFinsupp.single_eq_of_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.single_eq_of_ne.h7 : Not
      (∀ {ι : Type} {β : ι → Type} [inst : (i : ι) → Zero (β i)] [inst_1 : DecidableEq ι] {i i' : ι} {b : β i},
        @Eq (β i')
          (@DFunLike.coe (@DFinsupp ι (fun (i : ι) => β i) inst) ι β (@DFinsupp.instDFunLike ι β inst)
            (@DFinsupp.single ι β inst inst_1 i b) i')
          (@OfNat.ofNat (β i') (nat_lit 0) (@Zero.toOfNat0 (β i') (inst i')))) := fun hc_h => absurd (@hc_h (Nat) (fun (a : Nat) => Nat) (fun (i : Nat) => @MulZeroClass.toZero Nat Nat.instMulZeroClass) (instDecidableEqNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- List.get_tail, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.get_tail.h3 : ¬∀ {α : Type} (l : List α) (i : ℕ), i < l.tail.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- List.get_tail, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.get_tail.h4.der.{u} : ∀ {α : Type u} (l : List α), ∀ i < l.tail.length, i + 1 < l.length := by
  (intros; simp_all <;> lia)
theorem HypCheckProof.List.get_tail.h4.{u} : ∀ {α : Type u} (l : List α) (i : ℕ) (h : i < l.tail.length),
      l.tail.get (⟨i, h⟩ : Fin l.tail.length) = l.get (⟨i + 1, HypCheckProof.List.get_tail.h4.der l i h⟩ : Fin l.length) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @List.get_tail hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.List.get_tail.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- Int.div_le_iff_of_dvd_of_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_le_iff_of_dvd_of_pos.h3 : ¬∀ {a b c : ℤ}, b ∣ a → (a / b ≤ c ↔ a ≤ b * c) := fun hc_h => absurd (@hc_h (0) (0) (-1) (by
  decide)) (by
  decide +kernel)

-- Int.div_le_iff_of_dvd_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_le_iff_of_dvd_of_pos.h4 : ¬∀ {a b c : ℤ}, 0 < b → (a / b ≤ c ↔ a ≤ b * c) := fun hc_h => absurd (@hc_h (1) (2) (0) (by
  decide)) (by
  decide +kernel)

-- Int.dvd_mul_of_div_dvd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.dvd_mul_of_div_dvd.h4 : ¬∀ {a b c : ℤ}, b ∣ a → a ∣ b * c := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- DFinsupp.comapDomain_apply, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.comapDomain_apply.h5 : ¬∀ {ι : Type} {β : ι → Type} {κ : Type} [inst : (i : ι) → Zero (β i)] (h : κ → ι) (f : Π₀ (i : ι), β i) (k : κ),
        Function.Injective h := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (ℕ) (fun (i : ℕ) => Nat.instMulZeroClass.toZero) (fun _ => 0 : ℕ → ℕ) (0) (0)) (by
  simp)

-- Nat.Coprime.isPrimePow_dvd_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.isPrimePow_dvd_mul.h3 : ¬∀ {n a b : ℕ}, IsPrimePow n → (n ∣ a * b ↔ n ∣ a ∨ n ∣ b) := fun hc_h => absurd (@hc_h (4) (2) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.Coprime.isPrimePow_dvd_mul, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.isPrimePow_dvd_mul.h4 : ¬∀ {n a b : ℕ}, a.Coprime b → (n ∣ a * b ↔ n ∣ a ∨ n ∣ b) := fun hc_h => absurd (@hc_h (6) (2) (3) (by
  decide)) (by
  decide +kernel)

-- Set.eq_univ_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_univ_of_subset.h3 : ¬∀ {α : Type} {s t : Set α}, s = Set.univ → t = Set.univ := fun hc_h => absurd (@hc_h (ℕ) _ ({n : ℕ | n = 0}) rfl) (by
  simp)

-- Set.eq_univ_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_univ_of_subset.h4 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t → t = Set.univ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (by
  rfl)) (by
  simp)

-- List.Nodup.concat, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.concat.h3 : ¬∀ {α : Type} {l : List α} {a : α}, l.Nodup → (l.concat a).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.concat, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.concat.h4 : ¬∀ {α : Type} {l : List α} {a : α}, a ∉ l → (l.concat a).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (1) (by
  decide)) (by
  decide +kernel)

-- Int.div_lt_iff_of_dvd_of_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.div_lt_iff_of_dvd_of_pos.h3 : ¬∀ {a b c : ℤ}, b ∣ a → (a / b < c ↔ a < b * c) := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Finset.attachFin_ssubset_attachFin, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.attachFin_ssubset_attachFin.h3 : ¬∀ {n : ℕ} {s t : Finset ℕ}, (∀ m ∈ t, m < n) → s ⊂ t := fun hc_h => absurd (@hc_h (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide)) (by
  decide +kernel)

-- List.perm_replicate_append_replicate, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.perm_replicate_append_replicate.h7 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {a b : α} {m n : ℕ},
        l.Perm (List.replicate m a ++ List.replicate n b) ↔ List.count a l = m ∧ List.count b l = n ∧ l ⊆ [a, b] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) (0) (0) (0) (1)) (by
  decide +kernel)

-- List.pairwise_of_reflexive_of_forall_ne, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.pairwise_of_reflexive_of_forall_ne.h3.inst : ¬List.Pairwise (fun (a b : ℕ) => a < b) [0, 0] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.pairwise_of_reflexive_of_forall_ne.h3.prem0 : ∀ a ∈ [0, 0], ∀ b ∈ [0, 0], a ≠ b → (fun (a b : ℕ) => a < b) a b := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.pairwise_of_reflexive_of_forall_ne.h3 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α}, (∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b) → List.Pairwise R l := fun hc_h => HypCheckProof.List.pairwise_of_reflexive_of_forall_ne.h3.inst (@hc_h (ℕ) (fun (a b : ℕ) => a < b) ([0, 0]) HypCheckProof.List.pairwise_of_reflexive_of_forall_ne.h3.prem0)

-- List.pairwise_of_reflexive_of_forall_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwise_of_reflexive_of_forall_ne.h4 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} [inst : Std.Refl R], List.Pairwise R l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a ≤ b : ℕ → ℕ → Prop) ([1, 0]) _) (by
  decide +kernel)

-- Part.assert_defined, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.assert_defined.h3 : ¬∀ {α : Type} {p : Prop} {f : p → Part α}, p := fun hc_h => absurd (@hc_h (ℕ) (False) (fun (a : False) => 0)) (by
  decide +kernel)

-- Part.assert_defined, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.assert_defined.h4 : ¬∀ {α : Type} {p : Prop} {f : p → Part α}, p → (Part.assert p f).Dom := fun hc_h => absurd (@hc_h (ℕ) (True) (fun (a : True) => ⊥) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  nofun)

-- Rat.mk_num_ne_zero_of_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.mk_num_ne_zero_of_ne_zero.h3 : ¬∀ {q : ℚ} {n d : ℤ}, q = Rat.divInt n d → n ≠ 0 := fun hc_h => absurd (@hc_h _ (0) (0) rfl) (by
  decide +kernel)

-- Rat.mk_num_ne_zero_of_ne_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.mk_num_ne_zero_of_ne_zero.h4 : ¬∀ {q : ℚ} {n : ℤ} {d : ℤ}, q ≠ 0 → n ≠ 0 := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Tuple.lt_card_gt_iff_apply_gt_of_antitone, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Tuple.lt_card_gt_iff_apply_gt_of_antitone.h7 : Not
      (∀ {n : Nat} {α : Type} {j : Fin n} {f : Fin n → α} [inst : Preorder α] {a : α}
        [inst_1 : @DecidableLT α (@Preorder.toLT α inst)],
        Iff
          (@LT.lt Nat instLTNat (@Fin.val n j)
            (@Finset.card (Fin n) {i : Fin n | @LT.lt α (@Preorder.toLT α inst) a (f i)}))
          (@LT.lt α (@Preorder.toLT α inst) a (f j))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Nat) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
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
          (@Eq.refl Bool Bool.true)))) (fun (a : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
      @ite Nat
        (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
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
                (@Eq.refl Bool Bool.true)))))
        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
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
                (@Eq.refl Bool Bool.true)))))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (Nat.instPreorder) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Nat.decLt)) (by
  decide +kernel)

-- Tuple.lt_card_le_iff_apply_le_of_monotone, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Tuple.lt_card_le_iff_apply_le_of_monotone.h7 : Not
      (∀ {n : Nat} {α : Type} {j : Fin n} {f : Fin n → α} [inst : Preorder α] {a : α}
        [inst_1 : @DecidableLE α (@Preorder.toLE α inst)],
        Iff
          (@LT.lt Nat instLTNat (@Fin.val n j)
            (@Finset.card (Fin n) {i : Fin n | @LE.le α (@Preorder.toLE α inst) (f i) a}))
          (@LE.le α (@Preorder.toLE α inst) (f j) a)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Nat) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
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
          (@Eq.refl Bool Bool.true)))) (fun (a : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
      @ite Nat
        (@Eq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
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
                (@Eq.refl Bool Bool.true)))))
        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a
          (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
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
                (@Eq.refl Bool Bool.true)))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (Nat.instPreorder) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Nat.decLe)) (by
  decide +kernel)

-- Rat.num_den_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.num_den_mk.h3 : ¬∀ {q : ℚ} {n d : ℤ}, q = Rat.divInt n d → ∃ (c : ℤ), n = c * q.num ∧ d = c * ↑q.den := fun hc_h => absurd (@hc_h _ (1) (0) rfl) (by
  simp)

-- Rat.num_den_mk, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.num_den_mk.h4 : ¬∀ {q : ℚ} {n d : ℤ}, d ≠ 0 → ∃ (c : ℤ), n = c * q.num ∧ d = c * ↑q.den := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide)) (by
  simp)

-- PNat.Coprime.coprime_dvd_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.coprime_dvd_left.h3 : ¬∀ {m k n : ℕ+}, k.Coprime n → m.Coprime n := fun hc_h => absurd (@hc_h (2) (1) (2) (by
  rfl)) (by
  nofun)

-- PNat.Coprime.coprime_dvd_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.coprime_dvd_left.h4 : ¬∀ {m k n : ℕ+}, m ∣ k → m.Coprime n := fun hc_h => absurd (@hc_h (2) (2) (2) (by
  rfl)) (by
  nofun)

-- PNat.Coprime.mul_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.mul_right.h3 : ¬∀ {k m n : ℕ+}, k.Coprime n → k.Coprime (m * n) := fun hc_h => absurd (@hc_h (2) (2) (1) (by
  rfl)) (by
  nofun)

-- PNat.Coprime.mul_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.mul_right.h4 : ¬∀ {k m n : ℕ+}, k.Coprime m → k.Coprime (m * n) := fun hc_h => absurd (@hc_h (2) (1) (2) (by
  rfl)) (by
  nofun)

-- PNat.Coprime.mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.mul.h3 : ¬∀ {k m n : ℕ+}, n.Coprime k → (m * n).Coprime k := fun hc_h => absurd (@hc_h (2) (2) (1) (by
  rfl)) (by
  nofun)

-- PNat.Coprime.mul, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.mul.h4 : ¬∀ {k m n : ℕ+}, m.Coprime k → (m * n).Coprime k := fun hc_h => absurd (@hc_h (2) (1) (2) (by
  rfl)) (by
  nofun)

-- Nat.find_le, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Nat.find_le.h3.der : ∀ {n : ℕ} {p : ℕ → Prop} [inst : DecidablePred p], p n → ∃ (n : ℕ), p n := by
  (intros; solve_by_elim)
theorem HypCheckProof.Nat.find_le.h3 : ∀ {n : ℕ} {p : ℕ → Prop} [inst : DecidablePred p] (hn : p n), Nat.find (HypCheckProof.Nat.find_le.h3.der hn) ≤ n := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Nat.find_le hc_x0 hc_x1 hc_x2 (@HypCheckProof.Nat.find_le.h3.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x3

-- Nat.find_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_le.h4 : ¬∀ {n : ℕ} {p : ℕ → Prop} [inst : DecidablePred p] {h : ∃ (n : ℕ), p n}, Nat.find h ≤ n := fun hc_h => absurd (fun hc_k0 => @hc_h (0) (fun n => n = 1 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 1) hc_k0) (by
  simp)

-- Matrix.one_apply_ne, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.one_apply_ne.h7 : Not
      (∀ {n α : Type} [inst : DecidableEq n] [inst_1 : Zero α] [inst_2 : One α] {i j : n},
        @Eq α
          (@OfNat.ofNat (Matrix n n α) (nat_lit 1) (@One.toOfNat1 (Matrix n n α) (@Matrix.one n α inst inst_1 inst_2)) i j)
          (@OfNat.ofNat α (nat_lit 0) (@Zero.toOfNat0 α inst_1))) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (Nat.instOne) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Nat.find_min', hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Nat.find_min'.h2.der : ∀ {p : ℕ → Prop} [inst : DecidablePred p] {m : ℕ}, p m → ∃ (n : ℕ), p n := by
  (intros; solve_by_elim)
theorem HypCheckProof.Nat.find_min'.h2 : ∀ {p : ℕ → Prop} [inst : DecidablePred p] {m : ℕ} (h : p m), Nat.find (HypCheckProof.Nat.find_min'.h2.der h) ≤ m := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Nat.find_min' hc_x0 hc_x1 (@HypCheckProof.Nat.find_min'.h2.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x2 hc_x3

-- Nat.find_min', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_min'.h4 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ (n : ℕ), p n) {m : ℕ}, Nat.find H ≤ m := fun hc_h => absurd (fun hc_k0 => @hc_h (fun n => n = 1 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 1) hc_k0 (0)) (by
  simp)

-- Fin.coe_of_injective_castLE_symm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.coe_of_injective_castLE_symm.h2 : ¬∀ {n k : ℕ} (i : Fin k), n ≤ k := fun hc_h => absurd (@hc_h (2) (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.coe_of_injective_castLE_symm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.coe_of_injective_castLE_symm.h4 : ¬∀ {n k : ℕ} (h : n ≤ k) (i : Fin k), i ∈ Set.range (Fin.castLE h) := fun hc_h => absurd (fun hc_k0 => @hc_h (0) (1) hc_k0 ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Nodup.map_update, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.map_update.h4 : ¬∀ {α β : Type} [inst : DecidableEq α] {l : List α} (f : α → β) (x : α) (y : β),
        List.map (Function.update f x y) l = if x ∈ l then (List.map f l).set (List.idxOf x l) y else List.map f l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) ([0, 0]) (fun n => n + 1 : ℕ → ℕ) (0) (0)) (by
  decide +kernel)

-- Fin.natCast_lt_natCast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.natCast_lt_natCast.h3 : Not
      (∀ {n a b : Nat},
        @LE.le Nat instLENat b n →
          Iff
            (@LT.lt
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@instLTFin
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
            (@LT.lt Nat instLTNat a b)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Fin.natCast_lt_natCast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.natCast_lt_natCast.h4 : Not
      (∀ {n a b : Nat},
        @LE.le Nat instLENat a n →
          Iff
            (@LT.lt
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@instLTFin
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
            (@LT.lt Nat instLTNat a b)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Matrix.ofNat_mulVec, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.ofNat_mulVec.h6 : ¬∀ {m α : Type} [inst : NonAssocSemiring α] [inst : Fintype m] [inst : DecidableEq m] (x : ℕ) (v : m → α), x.AtLeastTwo := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Nat.instNonAssocSemiring) (Bool.fintype) (instDecidableEqBool) (0) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fin.natCast_strictMono, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.natCast_strictMono.h3 : Not
      (∀ {n a b : Nat},
        @LT.lt Nat instLTNat a b →
          @LT.lt
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@instLTFin
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
              b)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (by
  decide)) (by
  decide +kernel)

-- Fin.natCast_strictMono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.natCast_strictMono.h4 : Not
      (∀ {n a b : Nat},
        @LE.le Nat instLENat b n →
          @LT.lt
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@instLTFin
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
              b)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Set.image_subset_image2_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_subset_image2_right.h7 : ¬∀ {α β γ : Type} {f : α → β → γ} {s : Set α} {t : Set β} {a : α}, f a '' t ⊆ Set.image2 f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a + b : ℕ → ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- ENat.le_sub_of_add_le_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.le_sub_of_add_le_left.h4 : ¬∀ {a b c : ℕ∞}, a ≠ ⊤ → b ≤ c - a := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.Nodup.pairwise_of_forall_ne, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Nodup.pairwise_of_forall_ne.h3.inst : ¬List.Pairwise (fun (a b : ℕ) => a < b) [0, 0] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.Nodup.pairwise_of_forall_ne.h3.prem0 : ∀ a ∈ [0, 0], ∀ b ∈ [0, 0], a ≠ b → (fun (a b : ℕ) => a < b) a b := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.Nodup.pairwise_of_forall_ne.h3 : ¬∀ {α : Type} {l : List α} {r : α → α → Prop}, (∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) → List.Pairwise r l := fun hc_h => HypCheckProof.List.Nodup.pairwise_of_forall_ne.h3.inst (@hc_h (ℕ) ([0, 0]) (fun (a b : ℕ) => a < b) HypCheckProof.List.Nodup.pairwise_of_forall_ne.h3.prem0)

-- List.Nodup.pairwise_of_forall_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.pairwise_of_forall_ne.h4 : ¬∀ {α : Type} {l : List α} {r : α → α → Prop}, l.Nodup → List.Pairwise r l := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (fun a b => a < b : ℕ → ℕ → Prop) (by
  decide)) (by
  decide +kernel)

-- Fin.castPred_le_castPred, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_le_castPred.h3 : ¬∀ {n : ℕ} {i j : Fin (n + 1)}, j ≠ Fin.last n → i ≤ j := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.castPred_le_castPred, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castPred_le_castPred.h4 : ¬∀ {n : ℕ} {i j : Fin (n + 1)}, i ≤ j → j ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- ENat.le_sub_of_add_le_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.le_sub_of_add_le_right.h4 : ¬∀ {a b c : ℕ∞}, b ≠ ⊤ → a ≤ c - b := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Int.natAbs_coe_sub_coe_le_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_coe_sub_coe_le_of_le.h3 : Not
      (∀ {a b n : Nat},
        @LE.le Nat instLENat b n →
          @LE.le Nat instLENat
            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt a)
                (@Nat.cast Int instNatCastInt b)).natAbs
            n) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Int.natAbs_coe_sub_coe_le_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_coe_sub_coe_le_of_le.h4 : Not
      (∀ {a b n : Nat},
        @LE.le Nat instLENat a n →
          @LE.le Nat instLENat
            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt a)
                (@Nat.cast Int instNatCastInt b)).natAbs
            n) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- Fin.succAbove_pred_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_pred_of_le.h3 : ¬∀ {n : ℕ} (p i : Fin (n + 1)) (hi : i ≠ 0), p.succAbove (i.pred hi) = (i.pred hi).castSucc := fun hc_h => absurd (fun hc_k0 => @hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) hc_k0) (by
  decide +kernel)

-- Fin.succAbove_pred_of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_pred_of_le.h4 : ¬∀ {n : ℕ} (p i : Fin (n + 1)), i ≤ p → i ≠ 0 := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- Fin.succAbove_ne_last, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.succAbove_ne_last.h3.gneg : ∀ {n : ℕ} {a : Fin (n + 2)} {b : Fin (n + 1)}, ¬a ≠ Fin.last (n + 1) → b ≠ Fin.last n → a.succAbove b ≠ Fin.last (n + 1) := by
  (intros; simp_all; done)
theorem HypCheckProof.Fin.succAbove_ne_last.h3 : ∀ {n : ℕ} {a : Fin (n + 2)} {b : Fin (n + 1)}, b ≠ Fin.last n → a.succAbove b ≠ Fin.last (n + 1) := by
  intro hc_x0 hc_x1 hc_x2 hc_x4
  exact Classical.byCases (fun hc_h => @Fin.succAbove_ne_last hc_x0 hc_x1 hc_x2 hc_h hc_x4) (fun hc_hn => @HypCheckProof.Fin.succAbove_ne_last.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn hc_x4)

-- Fin.succAbove_ne_last, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_ne_last.h4 : ¬∀ {n : ℕ} {a : Fin (n + 2)} {b : Fin (n + 1)}, a ≠ Fin.last (n + 1) → a.succAbove b ≠ Fin.last (n + 1) := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (by
  decide)) (by
  decide +kernel)

-- List.argmax_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.argmax_mem.h7 : ¬∀ {α β : Type} [inst : Preorder β] [inst : DecidableLT β] {f : α → β} {l : List α} {m : α}, m ∈ l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instPreorder) (Nat.decLt) (fun n => n + 1 : ℕ → ℕ) ([]) (0)) (by
  decide +kernel)

-- List.splitBy_of_isChain, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitBy_of_isChain.h3.inst : ¬List.splitBy (fun (a b : ℕ) => Decidable.decide (a < b)) [] = [[]] := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.List.splitBy_of_isChain.h3.prem0 : List.IsChain (fun (x y : ℕ) => (fun (a b : ℕ) => Decidable.decide (a < b)) x y = Bool.true) [] := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.List.splitBy_of_isChain.h3 : ¬∀ {α : Type} {r : α → α → Bool} {l : List α},
        List.IsChain (fun (x y : α) => r x y = Bool.true) l → List.splitBy r l = [l] := fun hc_h => HypCheckProof.List.splitBy_of_isChain.h3.inst (@hc_h (ℕ) (fun (a b : ℕ) => Decidable.decide (a < b)) ([]) HypCheckProof.List.splitBy_of_isChain.h3.prem0)

-- List.splitBy_of_isChain, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.splitBy_of_isChain.h4 : ¬∀ {α : Type} {r : α → α → Bool} {l : List α}, l ≠ [] → List.splitBy r l = [l] := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Bool) ([1, 0]) (by
  decide)) (by
  decide +kernel)

-- Set.Subsingleton.eq_singleton_of_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subsingleton.eq_singleton_of_mem.h2 : ¬∀ {α : Type} {s : Set α} {x : α}, x ∈ s → s = {x} := fun hc_h => absurd (@hc_h (Bool) ({x : Bool | True}) (Bool.true) (by
  decide)) (by
  simp)

-- Set.Subsingleton.eq_singleton_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subsingleton.eq_singleton_of_mem.h4 : ¬∀ {α : Type} {s : Set α}, s.Subsingleton → ∀ {x : α}, s = {x} := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (by
  simp) (1)) (by
  simp)

-- Matrix.toBlock_one_disjoint, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.toBlock_one_disjoint.h7 : Not
      (∀ {m α : Type} [inst : DecidableEq m] [inst_1 : Zero α] [inst_2 : One α] {p q : m → Prop},
        @Eq (Matrix (@Subtype m fun (a : m) => p a) (@Subtype m fun (a : m) => q a) α)
          (@Matrix.toBlock m m α
            (@OfNat.ofNat (Matrix m m α) (nat_lit 1) (@One.toOfNat1 (Matrix m m α) (@Matrix.one m α inst inst_1 inst_2))) p
            q)
          (@OfNat.ofNat (Matrix (@Subtype m fun (a : m) => p a) (@Subtype m fun (a : m) => q a) α) (nat_lit 0)
            (@Zero.toOfNat0 (Matrix (@Subtype m fun (a : m) => p a) (@Subtype m fun (a : m) => q a) α)
              (@Matrix.zero (@Subtype m fun (a : m) => p a) (@Subtype m fun (a : m) => q a) α inst_1)))) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instDecidableEqNat) (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (Nat.instOne) (fun n => n = 0 : Nat → Prop) (fun n => n = 0 : Nat → Prop)) (by
  decide +kernel)

-- Matrix.toBlock_diagonal_disjoint, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.toBlock_diagonal_disjoint.h7 : ¬∀ {m α : Type} [inst : DecidableEq m] [inst_1 : Zero α] (d : m → α) {p q : m → Prop},
        (Matrix.diagonal d).toBlock p q = 0 := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (Nat.instMulZeroClass.toZero) (fun n => n + 1 : ℕ → ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop)) (by
  decide +kernel)

-- Nat.Prime.dvd_or_dvd_of_dvd_lcm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_or_dvd_of_dvd_lcm.h4 : ¬∀ {p a b : ℕ}, Nat.Prime p → p ∣ a ∨ p ∣ b := fun hc_h => absurd (@hc_h (2) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.le_nth_of_lt_nth_succ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_nth_of_lt_nth_succ.h3 : ¬∀ {p : ℕ → Prop} {k a : ℕ}, p a → a ≤ Nat.nth p k := fun hc_h => absurd (@hc_h (fun n => n % 2 = 0 : ℕ → Prop) (0) (2) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  simp)

-- Nat.nth_add, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.nth_add.h4.inst : ¬Nat.nth (fun (i : ℕ) => (fun (x : ℕ) => False) (i + 1)) 0 + 1 = Nat.nth (fun (x : ℕ) => False) 0 := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.nth_add.h4.prem0 : ∀ k < 1, ¬(fun (x : ℕ) => False) k := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.nth_add.h4 : ¬∀ {p : ℕ → Prop} {m n : ℕ}, (∀ k < m, ¬p k) → Nat.nth (fun (i : ℕ) => p (i + m)) n + m = Nat.nth p n := fun hc_h => HypCheckProof.Nat.nth_add.h4.inst (@hc_h (fun (x : ℕ) => False) (1) (0) HypCheckProof.Nat.nth_add.h4.prem0)

-- Nat.nth_le_nth', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_le_nth'.h3 : ¬∀ {p : ℕ → Prop} {m n : ℕ}, (∀ (hf : (Set.ofPred p).Finite), n < hf.toFinset.card) → Nat.nth p m ≤ Nat.nth p n := fun hc_h => absurd (@hc_h (fun _ => True : ℕ → Prop) (1) (0) (by
  simp)) (by
  simp)

-- Num.gcd_to_nat_aux, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Num.gcd_to_nat_aux.h3 : Not
      (∀ {n : Nat} {a b : Num},
        @LE.le Nat instLENat (@HMul.hMul Num Num Num (@instHMul Num Num.instMul) a b).natSize n →
          @Eq Nat (@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (Num.gcdAux n a b))
            ((@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) a).gcd
              (@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) b))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Num.pos PosNum.one) (Num.zero) (by
  decide)) (by
  decide +kernel)

-- Num.gcd_to_nat_aux, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Num.gcd_to_nat_aux.h4 : Not
      (∀ {n : Nat} {a b : Num},
        @LE.le Num Num.instLE a b →
          @Eq Nat (@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) (Num.gcdAux n a b))
            ((@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) a).gcd
              (@castNum Nat Nat.instOne instAddNat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) b))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Num.pos PosNum.one) (Num.pos PosNum.one.bit1) (by
  decide)) (by
  decide +kernel)

-- Set.infinite_iUnion, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infinite_iUnion.h4 : ¬∀ {α ι : Type} [inst : Infinite ι] {s : ι → Set α}, (⋃ (i : ι), s i).Infinite := fun hc_h => absurd (@hc_h (ℕ) (ℕ) _ (fun (a : ℕ) => {n : ℕ | n = 0})) (by
  simp)

-- Nat.div_dvd_div_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.div_dvd_div_left.h3 : ¬∀ {n m k : ℕ}, n ∣ m → k / m ∣ k / n := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.div_dvd_div_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.div_dvd_div_left.h4 : ¬∀ {n m k : ℕ}, m ∣ k → k / m ∣ k / n := fun hc_h => absurd (@hc_h (2) (1) (2) (by
  decide)) (by
  decide +kernel)

-- Ordnode.equiv_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.equiv_iff.h3 : ¬∀ {α : Type} {t₁ t₂ : Ordnode α}, t₂.Sized → (t₁.Equiv t₂ ↔ t₁.toList = t₂.toList) := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (Ordnode.node 1 Ordnode.nil 0 Ordnode.nil) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Ordnode.equiv_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.equiv_iff.h4 : ¬∀ {α : Type} {t₁ t₂ : Ordnode α}, t₁.Sized → (t₁.Equiv t₂ ↔ t₁.toList = t₂.toList) := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 1 Ordnode.nil 0 Ordnode.nil) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (by
  (repeat' constructor) <;> done)) (by
  decide +kernel)

-- Nat.div_dvd_div_iff_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.div_dvd_div_iff_right.h3 : ¬∀ {n m k : ℕ}, k ∣ n → (m / k ∣ n / k ↔ m ∣ n) := fun hc_h => absurd (@hc_h (2) (1) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.div_dvd_div_iff_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.div_dvd_div_iff_right.h4 : ¬∀ {n m k : ℕ}, k ∣ m → (m / k ∣ n / k ↔ m ∣ n) := fun hc_h => absurd (@hc_h (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Set.EqOn.comp_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.comp_left.h7 : ¬∀ {α β γ : Type} {s : Set α} {f₁ f₂ : α → β} {g : β → γ}, Set.EqOn (g ∘ f₁) (g ∘ f₂) s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Nat.mod_eq_of_modEq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mod_eq_of_modEq.h3 : ¬∀ {a b n : ℕ}, b < n → a % n = b := fun hc_h => absurd (@hc_h (0) (1) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.mod_eq_of_modEq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mod_eq_of_modEq.h4 : ¬∀ {a b n : ℕ}, a ≡ b [MOD n] → a % n = b := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- exists_seq_of_forall_finset_exists', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.exists_seq_of_forall_finset_exists'.h4 : ¬∀ {α : Type} (P : α → Prop) (r : α → α → Prop) [inst : Std.Symm r],
        ∃ (f : ℕ → α), (∀ (n : ℕ), P (f n)) ∧ Pairwise (Function.onFun r f) := fun hc_h => absurd (@hc_h (Bool) (fun _ => False : Bool → Prop) (fun _ _ => True : Bool → Bool → Prop) (@Std.Symm.mk (Bool) (fun (x x_1 : Bool) => True) (by (try dsimp only);   decide))) (by
  simp)

-- Nat.ext_div_modEq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ext_div_modEq.h3 : ¬∀ {n a b : ℕ}, a ≡ b [MOD n] → a = b := fun hc_h => absurd (@hc_h (1) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.ext_div_modEq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ext_div_modEq.h4 : ¬∀ {n a b : ℕ}, a / n = b / n → a = b := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Ordnode.Valid'.rotateL_lemma₂, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.rotateL_lemma₂.h3 : ¬∀ {a b c : ℕ}, b < 2 * c → b < 3 * a + 1 := fun hc_h => absurd (@hc_h (0) (1) (1) (by
  decide)) (by
  decide +kernel)

-- Ordnode.Valid'.rotateL_lemma₂, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.rotateL_lemma₂.h4 : ¬∀ {a b c : ℕ}, 2 * (b + c) ≤ 9 * a + 3 → b < 3 * a + 1 := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- Option.map₂_comm, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.map₂_comm.h7 : ¬∀ {α β γ : Type} {f : α → β → γ} {a : Option α} {b : Option β} {g : β → α → γ}, Option.map₂ f a b = Option.map₂ g b a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (Option.some 0) (Option.some 1) (fun a b => a - b : ℕ → ℕ → ℕ)) (by
  decide +kernel)

-- Multiset.noncommFold_empty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.noncommFold_empty.h2 : Not
      (∀ {α : Type} (op : α → α → α),
        (@Set.Pairwise α
            (@Set.ofPred α fun (x : α) =>
              @Membership.mem α (Multiset α) (@Multiset.instMembership α)
                (@OfNat.ofNat (Multiset α) (nat_lit 0) (@Zero.toOfNat0 (Multiset α) (@Multiset.instZero α))) x)
            fun (x y : α) => @Eq α (op x y) (op y x)) →
          ∀ (a : α), @Std.Associative α op) := fun hc_h => absurd (@hc_h (Bool) (fun a b => !a || b : Bool → Bool → Bool) (by
  simp) (Bool.false)) (by
  exact fun hc_c =>
    absurd (hc_c.assoc (Bool.false : Bool) (Bool.false : Bool) (Bool.false : Bool))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Multiset.noncommFold_empty, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Multiset.noncommFold_empty.h3.der.{u_3} : ∀ {α : Type u_3} (op : α → α → α) [assoc : @Std.Associative α op] (a : α),
      @Set.Pairwise α
        (@Set.ofPred α fun (x : α) =>
          @Membership.mem α (Multiset α) (@Multiset.instMembership α)
            (@OfNat.ofNat (Multiset α) (nat_lit 0) (@Zero.toOfNat0 (Multiset α) (@Multiset.instZero α))) x)
        fun (x y : α) => @Eq α (op x y) (op y x) := by
  (intros; simp; done)
theorem HypCheckProof.Multiset.noncommFold_empty.h3.{u_3} : ∀ {α : Type u_3} (op : α → α → α) [assoc : @Std.Associative α op] (a : α),
      @Eq α
        (@Multiset.noncommFold α op assoc
          (@OfNat.ofNat (Multiset α) (nat_lit 0) (@Zero.toOfNat0 (Multiset α) (@Multiset.instZero α)))
          (@HypCheckProof.Multiset.noncommFold_empty.h3.der α op assoc a) a)
        a := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Multiset.noncommFold_empty hc_x0 hc_x1 hc_x2 (@HypCheckProof.Multiset.noncommFold_empty.h3.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x3

-- PNat.find_min', hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.PNat.find_min'.h2.der : ∀ {p : ℕ+ → Prop} [inst : DecidablePred p] {m : ℕ+}, p m → ∃ (n : ℕ+), p n := by
  (intros; solve_by_elim)
theorem HypCheckProof.PNat.find_min'.h2 : ∀ {p : ℕ+ → Prop} [inst : DecidablePred p] {m : ℕ+} (hm : p m), PNat.find (HypCheckProof.PNat.find_min'.h2.der hm) ≤ m := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @PNat.find_min' hc_x0 hc_x1 (@HypCheckProof.PNat.find_min'.h2.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x2 hc_x3

-- PNat.find_le, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.PNat.find_le.h3.der : ∀ {p : ℕ+ → Prop} [inst : DecidablePred p] {n : ℕ+}, p n → ∃ (n : ℕ+), p n := by
  (intros; solve_by_elim)
theorem HypCheckProof.PNat.find_le.h3 : ∀ {p : ℕ+ → Prop} [inst : DecidablePred p] {n : ℕ+} (hn : p n), PNat.find (HypCheckProof.PNat.find_le.h3.der hn) ≤ n := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @PNat.find_le hc_x0 hc_x1 hc_x2 (@HypCheckProof.PNat.find_le.h3.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x3

-- Set.range_enumerateCountable_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.range_enumerateCountable_of_mem.h4 : ¬∀ {α : Type} {s : Set α} (h : s.Countable) {default : α}, Set.range (Set.enumerateCountable h default) = s := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) ({x : ℕ | False}) hc_k0 (0)) (by
  simp)

-- Nat.add_div_eq_of_le_mod_add_mod, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_div_eq_of_le_mod_add_mod.h3 : ¬∀ {a b c : ℕ}, 0 < c → (a + b) / c = a / c + b / c + 1 := fun hc_h => absurd (@hc_h (0) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.add_div_eq_of_le_mod_add_mod, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_div_eq_of_le_mod_add_mod.h4 : ¬∀ {a b c : ℕ}, c ≤ a % c + b % c → (a + b) / c = a / c + b / c + 1 := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- List.IsPrefix.nodup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.nodup.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₂.Nodup → l₁.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.IsPrefix.nodup, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.nodup.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁ <+: l₂ → l₁.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) ([0, 0]) (by
  decide)) (by
  decide +kernel)

-- Function.Injective.right_inv_of_invOfMemRange, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.right_inv_of_invOfMemRange.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst : DecidableEq β] {f : α → β} (a : α), Function.Injective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (instDecidableEqNat) (fun _ => 0 : Bool → ℕ) (Bool.false)) (by
  decide +kernel)

-- Nat.dvd_ofDigits_sub_ofDigits, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_ofDigits_sub_ofDigits.h5 : ¬∀ {α : Type} [inst : CommRing α] {a b k : α} (L : List ℕ), k ∣ Nat.ofDigits a L - Nat.ofDigits b L := fun hc_h => absurd (@hc_h (Bool) (BooleanRing.toCommRing) (Bool.false) (Bool.true) (Bool.false) ([0, 1])) (by
  decide +kernel)

-- Fintype.sum_eq_single, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.sum_eq_single.h6 : ¬∀ {α M : Type} [inst : Fintype α] [inst_1 : AddCommMonoid M] {f : α → M} (a : α), ∑ x : α, f x = f a := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (Nat.instAddCommMonoid) (fun b => if b then 1 else 0 : Bool → ℕ) (Bool.false)) (by
  decide +kernel)

-- Fin.take_append_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.take_append_left.h4 : ¬∀ {n n' : ℕ} {α : Type} (m : ℕ) (u : Fin n → α) (v : Fin n' → α), m ≤ n := fun hc_h => absurd (@hc_h (0) (0) (ℕ) (1) (fun (i : Fin 0) => 0) (fun (i : Fin 0) => 0)) (by
  decide +kernel)

-- Fin.take_append_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.take_append_right.h4 : ¬∀ {n n' : ℕ} {α : Type} (m : ℕ) (u : Fin n → α) (v : Fin n' → α), m ≤ n' := fun hc_h => absurd (@hc_h (0) (0) (ℕ) (1) (fun (i : Fin 0) => 0) (fun (i : Fin 0) => 0)) (by
  decide +kernel)

-- List.dlookup_kerase_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dlookup_kerase_ne.h6 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a a' : α} {l : List (Sigma β)},
        List.dlookup a (List.kerase a' l) = List.dlookup a l := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) (0) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  decide +kernel)

-- List.Perm.kunion_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.kunion_right.h5 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {l₁ l₂ : List (Sigma β)} (l : List (Sigma β)),
        (l₁.kunion l).Perm (l₂.kunion l) := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) ([]) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)]) ([])) (by
  decide +kernel)

-- Set.card_image_of_inj_on, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.card_image_of_inj_on.h6 : ¬∀ {α β : Type} {s : Set α} [inst : Fintype ↑s] {f : α → β} [inst_1 : Fintype ↑(f '' s)],
        Fintype.card ↑(f '' s) = Fintype.card ↑s := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({x : Bool | True}) (Subtype.fintype (Membership.mem {x : Bool | True})) (fun _ => 0 : Bool → ℕ) ({x : Bool | True}.fintypeImage fun (x : Bool) => 0)) (by
  decide +kernel)

-- Set.restrict_comp_codRestrict, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.restrict_comp_codRestrict.h6 : ¬∀ {α β ι : Type} {f : ι → α} {g : α → β} {b : Set α} (x : ι), f x ∈ b := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- List.kreplace_of_forall_not, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.kreplace_of_forall_not.h6 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] (a : α) (b : β a) {l : List (Sigma β)}, List.kreplace a b l = l := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) (1) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  decide +kernel)

-- Finsupp.single_left_inj, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finsupp.single_left_inj.h6 : ¬∀ {α M : Type} [inst : Zero M] {a a' : α} {b : M}, ((fun₀ | a => b) = fun₀ | a' => b) ↔ a = a' := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instMulZeroClass.toZero) (0) (1) (0)) (by
  simp)

-- List.dlookup_cons_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dlookup_cons_ne.h6 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] (l : List (Sigma β)) {a : α} (s : Sigma β),
        List.dlookup a (s :: l) = List.dlookup a l := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) ([]) (0) ((⟨0, 0⟩ : (_ : ℕ) × ℕ))) (by
  decide +kernel)

-- List.dlookup_kunion_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dlookup_kunion_left.h6 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {l₁ l₂ : List (Sigma β)},
        List.dlookup a (l₁.kunion l₂) = List.dlookup a l₁ := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ([]) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  decide +kernel)

-- List.kerase_append_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.kerase_append_right.h6 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {l₁ l₂ : List (Sigma β)},
        List.kerase a (l₁ ++ l₂) = l₁ ++ List.kerase a l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)]) ([])) (by
  decide +kernel)

-- List.erase_orderedInsert_of_notMem, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.erase_orderedInsert_of_notMem.h6 : ¬∀ {α : Type} {r : α → α → Prop} [inst : DecidableRel r] [inst_1 : DecidableEq α] {x : α} {xs : List α},
        (List.orderedInsert r x xs).erase x = xs := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) (instDecidableEqNat) (1) ([1, 0])) (by
  decide +kernel)

-- Fintype.prod_eq_single, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.prod_eq_single.h6 : ¬∀ {α M : Type} [inst : Fintype α] [inst_1 : CommMonoid M] {f : α → M} (a : α), ∏ x : α, f x = f a := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (Nat.instCommMonoid) (fun b => if b then 1 else 0 : Bool → ℕ) (Bool.true)) (by
  decide +kernel)

-- List.mem_keys_kerase_of_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_keys_kerase_of_ne.h6 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a₁ a₂ : α} {l : List (Sigma β)},
        a₁ ∈ (List.kerase a₂ l).keys ↔ a₁ ∈ l.keys := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) (0) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  decide +kernel)

-- List.kerase_cons_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.kerase_cons_ne.h6 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {s : Sigma β} {l : List (Sigma β)},
        List.kerase a (s :: l) = s :: List.kerase a l := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ((⟨0, 0⟩ : (_ : ℕ) × ℕ)) ([])) (by
  decide +kernel)

-- List.lookupAll_cons_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lookupAll_cons_ne.h6 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] (l : List (Sigma β)) {a : α} (s : Sigma β),
        List.lookupAll a (s :: l) = List.lookupAll a l := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) ([]) (0) ((⟨0, 0⟩ : (_ : ℕ) × ℕ))) (by
  decide +kernel)

-- List.dlookup_kunion_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dlookup_kunion_right.h6 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a : α} {l₁ l₂ : List (Sigma β)},
        List.dlookup a (l₁.kunion l₂) = List.dlookup a l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)]) ([])) (by
  decide +kernel)

-- List.mem_keys_of_mem_keys_kerase, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_keys_of_mem_keys_kerase.h6 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] {a₁ : α} {a₂ : α} {l : List (Sigma β)}, a₁ ∈ l.keys := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) (0) ([])) (by
  decide +kernel)

-- Set.Subsingleton.monotoneOn, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subsingleton.monotoneOn.h6 : ¬∀ {α β : Type} {s : Set α} [inst : Preorder α] [inst_1 : Preorder β] (f : α → β), MonotoneOn f s := fun hc_h => absurd (@hc_h (Bool) (Bool) ({x : Bool | True}) (Bool.instPartialOrder.toPreorder) (Bool.instPartialOrder.toPreorder) (not : Bool → Bool)) (by
  decide +kernel)

-- Set.Subsingleton.strictAntiOn, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subsingleton.strictAntiOn.h6 : ¬∀ {α β : Type} {s : Set α} [inst : Preorder α] [inst_1 : Preorder β] (f : α → β), StrictAntiOn f s := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({x : Bool | True}) (Bool.instPartialOrder.toPreorder) (Nat.instPreorder) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  decide +kernel)

-- StrictMono.sortedLE_listMap, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictMono.sortedLE_listMap.h6 : ¬∀ {α β : Type} [inst : LinearOrder α] [inst_1 : Preorder β] {f : α → β} {l : List α},
        (List.map f l).SortedLE ↔ l.SortedLE := fun hc_h => absurd (@hc_h (ℕ) (Bool) (Nat.instLinearOrder) (Bool.instPartialOrder.toPreorder) (fun n => n % 2 == 0 : ℕ → Bool) ([0, 1])) (by
  decide +kernel)

-- List.map₂Left_eq_zipWith, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map₂Left_eq_zipWith.h6 : ¬∀ {α β γ : Type} (f : α → Option β → γ) (as : List α) (bs : List β),
        List.map₂Left f as bs = List.zipWith (fun (a : α) (b : β) => f a (Option.some b)) as bs := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun (a : ℕ) (a_1 : Option ℕ) => 0) ([0]) ([])) (by
  decide +kernel)

-- List.map₂Right_eq_zipWith, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map₂Right_eq_zipWith.h6 : ¬∀ {α β γ : Type} (f : Option α → β → γ) (as : List α) (bs : List β),
        List.map₂Right f as bs = List.zipWith (fun (a : α) (b : β) => f (Option.some a) b) as bs := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (ℕ) (fun (a : Option ℕ) (n : ℕ) => n + 1) ([]) ([0])) (by
  decide +kernel)

-- Set.Subsingleton.strictMonoOn, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subsingleton.strictMonoOn.h6 : ¬∀ {α β : Type} {s : Set α} [inst : Preorder α] [inst_1 : Preorder β] (f : α → β), StrictMonoOn f s := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({x : Bool | True}) (Bool.instPartialOrder.toPreorder) (Nat.instPreorder) (fun _ => 0 : Bool → ℕ)) (by
  decide +kernel)

-- SemiconjBy.natCast_mul_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SemiconjBy.natCast_mul_right.h5 : ¬∀ {α : Type} [inst : Semiring α] {a x y : α} (n : ℕ), SemiconjBy a (↑n * x) (↑n * y) := fun hc_h => absurd (@hc_h (ℕ) (Nat.instSemiring) (1) (0) (1) (1)) (by
  nofun)

-- Set.BijOn.exists, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.exists.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} {p : β → Prop}, (∃ b ∈ t, p b) ↔ ∃ a ∈ s, p (f a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n = 0 : ℕ → Prop)) (by
  simp)

-- Set.Disjoint.set_prod_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Disjoint.set_prod_right.h4 : ¬∀ {α β : Type} {t₁ t₂ : Set β} (s₁ s₂ : Set α), Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- List.map_destutter_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map_destutter_ne.h4 : ¬∀ {α β : Type} (l : List α) {f : α → β} [inst : DecidableEq α] [inst_1 : DecidableEq β],
        List.map f (List.destutter (fun (x1 x2 : α) => x1 ≠ x2) l) =
          List.destutter (fun (x1 x2 : β) => x1 ≠ x2) (List.map f l) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0, 1]) (fun _ => 0 : ℕ → ℕ) (instDecidableEqNat) (instDecidableEqNat)) (by
  decide +kernel)

-- List.length_foldr_permutationsAux2', hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_foldr_permutationsAux2'.h6 : ¬∀ {α : Type} (t : α) (ts : List α) (r L : List (List α)) (n : ℕ),
        (List.foldr (fun (y : List α) (r : List (List α)) => (List.permutationsAux2 t ts r y id).2) r L).length =
          n * L.length + r.length := fun hc_h => absurd (@hc_h (ℕ) (0) ([]) ([]) ([[]]) (1)) (by
  decide +kernel)

-- StrictMono.of_domRestrict, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictMono.of_domRestrict.h6 : ¬∀ {α β : Type} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β} {s : Set α}, StrictMonoOn f s := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.instPartialOrder.toPreorder) (Nat.instPreorder) (fun _ => 0 : Bool → ℕ) ({x : Bool | True})) (by
  decide +kernel)

-- SemiconjBy.intCast_mul_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.SemiconjBy.intCast_mul_left.h5 : ¬∀ {α : Type} [inst : Ring α] {a x y : α} (n : ℤ), SemiconjBy (↑n * a) x y := fun hc_h => absurd (@hc_h (Bool) (instBooleanRingBool.toRing) (Bool.true) (Bool.false) (Bool.true) (1)) (by
  nofun)

-- Set.BijOn.forall, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.forall.h6 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} {p : β → Prop}, (∀ b ∈ t, p b) ↔ ∀ a ∈ s, p (f a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n = 0 : ℕ → Prop)) (by
  simp)

-- List.nextOr_eq_nextOr_of_mem_dropLast, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nextOr_eq_nextOr_of_mem_dropLast.h6 : ¬∀ {α : Type} [inst : DecidableEq α] (xs : List α) (x d d' : α), xs.nextOr x d = xs.nextOr x d' := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0) (0) (1)) (by
  decide +kernel)

-- Set.Disjoint.set_prod_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Disjoint.set_prod_left.h4 : ¬∀ {α β : Type} {s₁ s₂ : Set α} (t₁ t₂ : Set β), Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- Rat.isNat_intCeil, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.isNat_intCeil.h6 : ¬∀ {R : Type} [inst : Ring R] [inst_1 : LinearOrder R] [inst_2 : FloorRing R] (r : R) (m : ℕ),
        Mathlib.Meta.NormNum.IsNat ⌈r⌉ m := fun hc_h => absurd (@hc_h (ℤ) (Int.instRing) (Int.instLinearOrder) (instFloorRingInt) (0) (1)) (by
  nofun)

-- Equiv.sigmaQuotFromRel_symm_apply_coe, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equiv.sigmaQuotFromRel_symm_apply_coe.h3 : ¬∀ {α β : Type} {r : α → α → Prop} {r' : β → β → Prop} (f : r →r r'), Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop) (1)) (by
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

-- List.map_filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map_filter.h4 : ¬∀ {α β : Type} (p : α → Bool) {f : α → β} (l : List α)
        [inst : DecidablePred fun (b : β) => ∃ (a : α), p a = Bool.true ∧ f a = b],
        List.map f (List.filter p l) =
          List.filter (fun (b : β) => Decidable.decide (∃ (a : α), p a = Bool.true ∧ f a = b)) (List.map f l) := fun hc_h => absurd (@hc_h (Bool) (ℕ) (not : Bool → Bool) (fun _ => 0 : Bool → ℕ) ([Bool.true]) (fun (a : ℕ) =>
      Bool.instDecidableExistsOfDecidablePred fun (a_1 : Bool) => (!a_1) = Bool.true ∧ (fun (x : Bool) => 0) a_1 = a)) (by
  decide +kernel)

-- StrictMono.sortedLT_listMap, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictMono.sortedLT_listMap.h6 : ¬∀ {α β : Type} [inst : LinearOrder α] [inst_1 : Preorder β] {f : α → β} {l : List α},
        (List.map f l).SortedLT ↔ l.SortedLT := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instPreorder) (fun _ => 0 : ℕ → ℕ) ([0, 1])) (by
  decide +kernel)

-- Fin.append_cast_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.append_cast_left.h6 : ¬∀ {α : Type} {n m : ℕ} (xs : Fin n → α) (ys : Fin m → α) (n' : ℕ), n' = n := fun hc_h => absurd (@hc_h (ℕ) (0) (0) (fun (a : Fin 0) => 0) (fun (a : Fin 0) => 0) (1)) (by
  decide +kernel)

-- Ordnode.node4L_size, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.node4L_size.h6 : ¬∀ {α : Type} {l : Ordnode α} {x : α} {m : Ordnode α} {y : α} {r : Ordnode α},
        (l.node4L x m y r).size = l.size + m.size + r.size + 2 := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.nil) (0) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil) (0) (Ordnode.nil)) (by
  decide +kernel)

-- Rat.isInt_round, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.isInt_round.h6 : ¬∀ {R : Type} [inst : Ring R] [inst_1 : LinearOrder R] [inst_2 : FloorRing R] (r : R) (m : ℤ),
        Mathlib.Meta.NormNum.IsInt (round r) m := fun hc_h => absurd (@hc_h (ℤ) (Int.instRing) (Int.instLinearOrder) (instFloorRingInt) (0) (1)) (by
  nofun)

-- Rat.isNat_intFloor, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.isNat_intFloor.h6 : ¬∀ {R : Type} [inst : Ring R] [inst_1 : LinearOrder R] [inst_2 : FloorRing R] (r : R) (m : ℕ),
        Mathlib.Meta.NormNum.IsNat ⌊r⌋ m := fun hc_h => absurd (@hc_h (ℤ) (Int.instRing) (Int.instLinearOrder) (instFloorRingInt) (0) (1)) (by
  nofun)

-- List.nextOr_cons_of_ne, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nextOr_cons_of_ne.h6 : ¬∀ {α : Type} [inst : DecidableEq α] (xs : List α) (y x d : α), (y :: xs).nextOr x d = xs.nextOr x d := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) (0) (0) (1)) (by
  decide +kernel)

-- Int.clog_of_one_le_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.clog_of_one_le_right.h6 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst_2 : FloorSemiring R] (b : ℕ) {r : R},
        Int.clog b r = ↑(Nat.clog b ⌈r⌉₊) := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) (2) (1 / 2)) (by
  decide +kernel)

-- Int.clog_ofNat, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.clog_ofNat.h6 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst : FloorSemiring R] (b n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.dedup_map_of_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dedup_map_of_injective.h5 : ¬∀ {α β : Type} [inst : DecidableEq α] [inst_1 : DecidableEq β] {f : α → β} (xs : List α),
        (List.map f xs).dedup = List.map f xs.dedup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (instDecidableEqNat) (instDecidableEqNat) (fun _ => 0 : ℕ → ℕ) ([0, 1])) (by
  decide +kernel)

-- Int.log_ofNat, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.log_ofNat.h6 : ¬∀ {R : Type} [inst : Semifield R] [inst_1 : LinearOrder R] [inst : FloorSemiring R] (b n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℚ) (Field.toSemifield) (Rat.linearOrder) (FloorRing.toFloorSemiring) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.card_image_of_injective, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.card_image_of_injective.h6 : ¬∀ {α β : Type} (s : Set α) [inst : Fintype ↑s] {f : α → β} [inst_1 : Fintype ↑(f '' s)],
        Fintype.card ↑(f '' s) = Fintype.card ↑s := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({x : Bool | True}) (Subtype.fintype (Membership.mem {x : Bool | True})) (fun _ => 0 : Bool → ℕ) ({x : Bool | True}.fintypeImage fun (x : Bool) => 0)) (by
  decide +kernel)

-- Function.LeftInverse.mem_preimage_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.mem_preimage_iff.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α} {s : Set α} {x : α}, f x ∈ g ⁻¹' s ↔ x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- Fintype.card_subtype_or_disjoint, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_subtype_or_disjoint.h3 : ¬∀ {α : Type} (p q : α → Prop) [inst : Fintype { x : α // p x }] [inst_1 : Fintype { x : α // q x }]
        [inst_2 : Fintype { x : α // p x ∨ q x }],
        Fintype.card { x : α // p x ∨ q x } = Fintype.card { x : α // p x } + Fintype.card { x : α // q x } := fun hc_h => absurd (@hc_h (Bool) (fun b => b = true : Bool → Prop) (fun b => b = true : Bool → Prop) (Fintype.subtypeEq Bool.true) (Fintype.subtypeEq Bool.true) (Subtype.fintype fun (x : Bool) => (fun (b : Bool) => b = Bool.true) x ∨ (fun (b : Bool) => b = Bool.true) x)) (by
  decide +kernel)

-- StrictAnti.sortedLT_listMap, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictAnti.sortedLT_listMap.h6 : ¬∀ {α β : Type} [inst : LinearOrder α] [inst_1 : Preorder β] {f : α → β} {l : List α},
        (List.map f l).SortedLT ↔ l.SortedGT := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instLinearOrder) (Nat.instPreorder) (fun n => n + 1 : ℕ → ℕ) ([0, 1])) (by
  decide +kernel)

-- StrictMonoOn.strictMono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictMonoOn.strictMono.h6 : Not
      (∀ {α β : Type} {s : Set α} {f : α → β} [inst : Preorder α] [inst_1 : Preorder β],
        @StrictMono (@Set.Elem α s) β
          (@Subtype.preorder α inst fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) s x) inst_1
          (@Function.comp (@Set.Elem α s) α β f
            (@Subtype.val α fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) s x))) := fun hc_h => absurd (@hc_h (Bool) (Nat) (@Set.ofPred Bool fun (x : Bool) => True) (fun _ => 0 : Bool → Nat) (@PartialOrder.toPreorder Bool Bool.instPartialOrder) (Nat.instPreorder)) (by
  decide +kernel)

-- Set.RightInvOn.eqOn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.RightInvOn.eqOn.h5 : ¬∀ {α β : Type} {t : Set β} {f : α → β} {f' : β → α}, Set.EqOn (f ∘ f') id t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Function.Injective.mem_set_image, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.mem_set_image.h3 : ¬∀ {α β : Type} {f : α → β} {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- Finite.le_ciSup, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finite.le_ciSup.h2 : ¬∀ {α ι : Type} [inst : ConditionallyCompleteLattice α] (f : ι → α) (i : ι), f i ≤ ⨆ (j : ι), f j := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (Nat.instConditionallyCompleteLinearOrderBot.toConditionallyCompleteLattice) (fun n => n : ℕ → ℕ) (1)) (by
  simp)

-- Multiset.coe_foldr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.coe_foldr.h3 : ¬∀ {α β : Type} (f : α → β → β) (b : β) (l : List α), LeftCommutative f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.left_comm (0 : ℕ) (1 : ℕ) (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.add_pred_div_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_pred_div_lt.h2 : ¬∀ {b n : ℕ}, 2 ≤ n → (n + b - 1) / b < n := fun hc_h => absurd (@hc_h (1) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.add_pred_div_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_pred_div_lt.h3 : ¬∀ {b n : ℕ}, 1 < b → (n + b - 1) / b < n := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Fin.val_cast_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_cast_of_lt.h3 : Not
      (∀ {n : Nat} [inst : @NeZero Nat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) n] {a : Nat},
        @Eq Nat (@Fin.val n (@Nat.cast (Fin n) (@Fin.NatCast.instNatCast n inst) a)) a) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) _ (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Fin.heq_fun_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.heq_fun_iff.h3 : ¬∀ {α : Type} {k l : ℕ} {f : Fin k → α} {g : Fin l → α}, k = l := fun hc_h => absurd (@hc_h (ℕ) (0) (1) (fun (a : Fin 0) => 0) (fun (a : Fin 1) => 0)) (by
  decide +kernel)

-- EReal.neg_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.neg_add.h2 : ¬∀ {x y : EReal}, x ≠ ⊤ ∨ y ≠ ⊥ → -(x + y) = -x - y := fun hc_h => absurd (@hc_h (⊥) (⊤) (by
  decide)) (by
  decide +kernel)

-- EReal.neg_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.neg_add.h3 : ¬∀ {x y : EReal}, x ≠ ⊥ ∨ y ≠ ⊤ → -(x + y) = -x - y := fun hc_h => absurd (@hc_h (⊤) (⊥) (by
  decide)) (by
  decide +kernel)

-- Nat.clog_of_two_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_of_two_le.h2 : ¬∀ {b n : ℕ}, 2 ≤ n → Nat.clog b n = Nat.clog b ((n + b - 1) / b) + 1 := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.clog_of_two_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_of_two_le.h3 : ¬∀ {b n : ℕ}, 1 < b → Nat.clog b n = Nat.clog b ((n + b - 1) / b) + 1 := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.log_eq_log_succ_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_eq_log_succ_iff.h3 : ¬∀ {b n : ℕ}, 1 < b → (Nat.log b n = Nat.log b (n + 1) ↔ b ^ Nat.log b (n + 1) ≠ n + 1) := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.clog_eq_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_eq_one.h2 : ¬∀ {b n : ℕ}, n ≤ b → Nat.clog b n = 1 := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.clog_eq_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_eq_one.h3 : ¬∀ {b n : ℕ}, 2 ≤ n → Nat.clog b n = 1 := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.log_of_one_lt_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_of_one_lt_of_le.h2 : ¬∀ {b n : ℕ}, b ≤ n → Nat.log b n = Nat.log b (n / b) + 1 := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.log_of_one_lt_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_of_one_lt_of_le.h3 : ¬∀ {b n : ℕ}, 1 < b → Nat.log b n = Nat.log b (n / b) + 1 := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.log_mul_base, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_mul_base.h2 : ¬∀ {b n : ℕ}, n ≠ 0 → Nat.log b (n * b) = Nat.log b n + 1 := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.log_mul_base, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_mul_base.h3 : ¬∀ {b n : ℕ}, 1 < b → Nat.log b (n * b) = Nat.log b n + 1 := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- EReal.add_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_pos.h2 : ¬∀ {a b : EReal}, 0 < b → 0 < a + b := fun hc_h => absurd (@hc_h (⊥) (1) (by
  simp)) (by
  decide +kernel)

-- EReal.add_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_pos.h3 : ¬∀ {a b : EReal}, 0 < a → 0 < a + b := fun hc_h => absurd (@hc_h (1) (⊥) (by
  simp)) (by
  decide +kernel)

-- EReal.add_ne_top_iff_of_ne_bot_of_ne_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_ne_top_iff_of_ne_bot_of_ne_top.h2 : ¬∀ {x y : EReal}, y ≠ ⊤ → (x + y ≠ ⊤ ↔ x ≠ ⊤) := fun hc_h => absurd (@hc_h (⊤) (⊥) (by
  decide)) (by
  decide +kernel)

-- EReal.add_ne_top_iff_of_ne_bot_of_ne_top, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_ne_top_iff_of_ne_bot_of_ne_top.h3 : ¬∀ {x y : EReal}, y ≠ ⊥ → (x + y ≠ ⊤ ↔ x ≠ ⊤) := fun hc_h => absurd (@hc_h (0) (⊤) (by
  decide)) (by
  decide +kernel)

-- Fin.succAbove_ne_zero_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_ne_zero_zero.h3 : ¬∀ {n : ℕ} [inst : NeZero n] {a : Fin (n + 1)}, a.succAbove 0 = 0 := fun hc_h => absurd (@hc_h (1) _ ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- EReal.mul_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.mul_pos.h2 : ¬∀ {a b : EReal}, 0 < b → 0 < a * b := fun hc_h => absurd (@hc_h (0) (1) (by
  simp)) (by
  simp)

-- EReal.mul_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.mul_pos.h3 : ¬∀ {a b : EReal}, 0 < a → 0 < a * b := fun hc_h => absurd (@hc_h (1) (0) (by
  simp)) (by
  simp)

-- EReal.mul_nonneg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.mul_nonneg.h2 : ¬∀ {a b : EReal}, 0 ≤ b → 0 ≤ a * b := fun hc_h => absurd (@hc_h (⊥) (1) (by
  simp)) (by
  simp)

-- EReal.mul_nonneg, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.mul_nonneg.h3 : ¬∀ {a b : EReal}, 0 ≤ a → 0 ≤ a * b := fun hc_h => absurd (@hc_h (1) (⊥) (by
  simp)) (by
  simp)

-- DFinsupp.comapDomain_zero, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.comapDomain_zero.h5 : ¬∀ {ι : Type} {β : ι → Type} {κ : Type} [inst : (i : ι) → Zero (β i)] (h : κ → ι), Function.Injective h := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (ℕ) (fun (i : ℕ) => Nat.instMulZeroClass.toZero) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- memPartitionSet_eq_iff, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.memPartitionSet_eq_iff.h5 : ¬∀ {α : Type} {f : ℕ → Set α} {n : ℕ} (a : α) {s : Set α}, memPartitionSet f n a = s ↔ a ∈ s := fun hc_h => absurd (@hc_h (Bool) (fun (a : ℕ) => {b : Bool | b = Bool.true}) (0) (Bool.true) ({b : Bool | b = Bool.true})) (by
  simp)

-- List.Sublist.inter_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.inter_right.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {l₁ l₂ l₃ : List α}, (l₁ ∩ l₃).Sublist (l₂ ∩ l₃) := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([]) ([0])) (by
  decide +kernel)

-- Fin.castSucc_pos', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castSucc_pos'.h3 : ¬∀ {n : ℕ} [inst : NeZero n] {i : Fin n}, 0 < i.castSucc := fun hc_h => absurd (@hc_h (1) _ ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.castLT_eq_castPred, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castLT_eq_castPred.h2 : ¬∀ {n : ℕ} (i : Fin (n + 1)), i < Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.castLT_eq_castPred, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.castLT_eq_castPred.h3.der : ∀ {n : ℕ}, ∀ i < Fin.last n, ¬i = Fin.last n := by
  (intros; lia)
theorem HypCheckProof.Fin.castLT_eq_castPred.h3 : ∀ {n : ℕ} (i : Fin (n + 1)) (h : i < Fin.last n),
      i.castLT h = i.castPred (HypCheckProof.Fin.castLT_eq_castPred.h3.der i h) := by
  intro hc_x0 hc_x1 hc_x2
  exact @Fin.castLT_eq_castPred hc_x0 hc_x1 hc_x2 (@HypCheckProof.Fin.castLT_eq_castPred.h3.der hc_x0 hc_x1 hc_x2)

-- List.cons_bagInter_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_bagInter_of_pos.h5 : ¬∀ {α : Type} {l₂ : List α} {a : α} [inst : DecidableEq α] (l₁ : List α),
        (a :: l₁).bagInter l₂ = a :: l₁.bagInter (l₂.erase a) := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (instDecidableEqNat) ([])) (by
  decide +kernel)

-- Set.subset_iUnion_of_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_iUnion_of_subset.h5 : ¬∀ {α ι : Type} {s : Set α} {t : ι → Set α} (i : ι), s ⊆ ⋃ (i : ι), t i := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => {x : ℕ | False}) (0)) (by
  simp)

-- List.bagInter_cons_of_notMem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.bagInter_cons_of_notMem.h5 : ¬∀ {α : Type} {l₁ : List α} {a : α} [inst : DecidableEq α] (l₂ : List α), l₁.bagInter (a :: l₂) = l₁.bagInter l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (instDecidableEqNat) ([])) (by
  decide +kernel)

-- EReal.div_nonpos_of_nonpos_of_nonneg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_nonpos_of_nonpos_of_nonneg.h2 : ¬∀ {a b : EReal}, 0 ≤ b → a / b ≤ 0 := fun hc_h => absurd (@hc_h (1) (1) (by
  simp)) (by
  (simp <;> omega))

-- List.bagInter_cons_of_not_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.bagInter_cons_of_not_mem.h5 : ¬∀ {α : Type} {l₁ : List α} {a : α} [inst : DecidableEq α] (l₂ : List α), l₁.bagInter (a :: l₂) = l₁.bagInter l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (instDecidableEqNat) ([])) (by
  decide +kernel)

-- EReal.div_nonneg_of_nonpos_of_nonpos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.div_nonneg_of_nonpos_of_nonpos.h3 : ¬∀ {a b : EReal}, a ≤ 0 → 0 ≤ a / b := fun hc_h => absurd (@hc_h (⊥) (1) (by
  decide)) (by
  simp)

-- List.bagInter_erase_of_not_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.bagInter_erase_of_not_mem.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} {a : α} [inst : DecidableEq α], l₁.bagInter (l₂.erase a) = l₁.bagInter l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([0]) (0) (instDecidableEqNat)) (by
  decide +kernel)

-- List.cons_bagInter_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_bagInter_of_mem.h5 : ¬∀ {α : Type} {l₂ : List α} {a : α} [inst : DecidableEq α] (l₁ : List α),
        (a :: l₁).bagInter l₂ = a :: l₁.bagInter (l₂.erase a) := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (instDecidableEqNat) ([])) (by
  decide +kernel)

-- Set.MapsTo.coe_iterate_restrict, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.coe_iterate_restrict.h3 : ¬∀ {α : Type} {s : Set α} {f : α → α} (x : ↑s) (k : ℕ), Set.MapsTo f s s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { x : ℕ // x ∈ {n : ℕ | n = 0} })) (0)) (by
  simp)

-- List.mem_map_of_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_map_of_injective.h3 : ¬∀ {α β : Type} {f : α → β} {a : α} {l : List α}, f a ∈ List.map f l ↔ a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) (0) ([1])) (by
  decide +kernel)

-- List.eq_of_mem_map_const, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.eq_of_mem_map_const.h5 : ¬∀ {α β : Type} {b₁ b₂ : β} {l : List α}, b₁ = b₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (0) (1) ([])) (by
  decide +kernel)

-- Nat.binomial_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.binomial_eq.h5 : ¬∀ {α : Type} {f : α → ℕ} {a b : α} [inst : DecidableEq α],
        Nat.multinomial {a, b} f = (f a + f b).factorial / ((f a).factorial * (f b).factorial) := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (0) (instDecidableEqNat)) (by
  decide +kernel)

-- List.Disjoint.of_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Disjoint.of_map.h5 : ¬∀ {α β : Type} {f : α → β} {s t : List α}, s.Disjoint t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ([0]) ([0])) (by
  simp)

-- Fintype.card_le_of_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_le_of_injective.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β] (f : α → β), Fintype.card α ≤ Fintype.card β := fun hc_h => absurd (@hc_h (Fin 3) (Bool) (Fin.fintype 3) (Bool.fintype) (fun (a : Fin 3) => Bool.false)) (by
  decide +kernel)

-- Function.Injective.bijective_of_finite, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.bijective_of_finite.h3 : ¬∀ {α : Type} [inst : Finite α] {f : α → α}, Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) _ (fun _ => true : Bool → Bool)) (by
  decide +kernel)

-- Nat.primeFactors_div_gcd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactors_div_gcd.h2 : ¬∀ {m n : ℕ}, n ≠ 0 → (m / m.gcd n).primeFactors = m.primeFactors \ n.primeFactors := fun hc_h => absurd (@hc_h (4) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.primeFactors_div_gcd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactors_div_gcd.h3 : ¬∀ {m n : ℕ}, Squarefree m → (m / m.gcd n).primeFactors = m.primeFactors \ n.primeFactors := fun hc_h => absurd (@hc_h (2) (0) (by
  decide +kernel)) (by
  decide +kernel)

-- Nat.not_exists_sq', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_exists_sq'.h2 : ¬∀ {m n : ℕ}, n < (m + 1) ^ 2 → ¬∃ (t : ℕ), t ^ 2 = n := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.not_exists_sq', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_exists_sq'.h3 : ¬∀ {m n : ℕ}, m ^ 2 < n → ¬∃ (t : ℕ), t ^ 2 = n := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.prod_primeFactors_sdiff_of_squarefree, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prod_primeFactors_sdiff_of_squarefree.h1 : ¬∀ {n : ℕ} {t : Finset ℕ}, t ⊆ n.primeFactors → ∏ a ∈ n.primeFactors \ t, a = n / ∏ a ∈ t, a := fun hc_h => absurd (@hc_h (0) ({ val := 0, nodup := of_decide_eq_true (id (Eq.refl Bool.true)) : Finset ℕ }) (by
  decide)) (by
  decide +kernel)

-- Set.codRestrict_restrict, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.codRestrict_restrict.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β} (x : ↑s), f ↑x ∈ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- List.IsPrefix.flatMap, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.flatMap.h4 : ¬∀ {α β : Type} {l₁ l₂ : List α} (f : α → List β), List.flatMap f l₁ <+: List.flatMap f l₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0]) ([]) (fun n => [n] : ℕ → List ℕ)) (by
  decide +kernel)

-- List.IsSuffix.flatMap, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsSuffix.flatMap.h4 : ¬∀ {α β : Type} {l₁ l₂ : List α} (f : α → List β), List.flatMap f l₁ <:+ List.flatMap f l₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ([0]) ([]) (fun n => [n] : ℕ → List ℕ)) (by
  decide +kernel)

-- Set.restrictPreimage_mk, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.restrictPreimage_mk.h5 : ¬∀ {α β : Type} (t : Set β) {f : α → β} {a : α}, a ∈ f ⁻¹' t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  simp)

-- List.mem_of_mem_dropSlice, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_of_mem_dropSlice.h5 : ¬∀ {α : Type} {n m : ℕ} {l : List α} {a : α}, a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (0) (0) ([]) (0)) (by
  decide +kernel)

-- Set.MapsTo.range_restrict, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.range_restrict.h5 : ¬∀ {α β : Type} (f : α → β) (s : Set α) (t : Set β), Set.MapsTo f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- Set.MapsTo.restrict_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.restrict_inj.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.MapsTo f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.MapsTo.image_subset, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.MapsTo.image_subset.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, f '' s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Subtype.coind_coe, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.coind_coe.h4 : ¬∀ {α β : Type} (f : α → β) {p : β → Prop} (a a : α), p (f a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n = 0 : ℕ → Prop) (0)) (by
  simp)

-- List.length_destutter_le_length_destutter_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_destutter_le_length_destutter_cons.h4 : ¬∀ {α : Type} {R : α → α → Prop} [inst : DecidableRel R] {a : α} {l : List α},
        (List.destutter R l).length ≤ (List.destutter R (a :: l)).length := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) (1) ([0, 1])) (by
  decide +kernel)

-- WithZeroMulInt.toNNReal_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithZeroMulInt.toNNReal_ne_zero.h2 : ¬∀ {e : NNReal} {m : WithZero (Multiplicative ℤ)}, m ≠ 0 → e ≠ 0 := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- WithZeroMulInt.toNNReal_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithZeroMulInt.toNNReal_ne_zero.h3 : ¬∀ {e : NNReal} {m : WithZero (Multiplicative ℤ)} (he : e ≠ 0), (WithZeroMulInt.toNNReal he) m ≠ 0 := fun hc_h => absurd (fun hc_k0 => @hc_h (1) (0) hc_k0) (by
  simp)

-- WithZeroMulInt.toNNReal_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithZeroMulInt.toNNReal_pos.h2 : ¬∀ {e : NNReal} {m : WithZero (Multiplicative ℤ)}, m ≠ 0 → e ≠ 0 := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- WithZeroMulInt.toNNReal_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithZeroMulInt.toNNReal_pos.h3 : ¬∀ {e : NNReal} {m : WithZero (Multiplicative ℤ)} (he : e ≠ 0), 0 < (WithZeroMulInt.toNNReal he) m := fun hc_h => absurd (fun hc_k0 => @hc_h (1) (0) hc_k0) (by
  simp)

-- ZMod.valMinAbs_natCast_of_half_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.valMinAbs_natCast_of_half_lt.h2 : Not
      (∀ {n a : Nat},
        @LT.lt Nat instLTNat a n →
          @Eq Int
            (@ZMod.valMinAbs n
              (@Nat.cast (ZMod n)
                (@AddMonoidWithOne.toNatCast (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
                a))
            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt a)
              (@Nat.cast Int instNatCastInt n))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- ZMod.valMinAbs_natCast_of_half_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.valMinAbs_natCast_of_half_lt.h3 : Not
      (∀ {n a : Nat},
        @LT.lt Nat instLTNat
            (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) n (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            a →
          @Eq Int
            (@ZMod.valMinAbs n
              (@Nat.cast (ZMod n)
                (@AddMonoidWithOne.toNatCast (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
                a))
            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt a)
              (@Nat.cast Int instNatCastInt n))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- ZMod.coe_int_val_inv_mul, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.coe_int_val_inv_mul.h1 : Not
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

-- ZMod.coe_int_val_inv_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.coe_int_val_inv_mul.h3 : Not
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

-- ZMod.intCast_mul_val_inv, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.intCast_mul_val_inv.h1 : Not
      (∀ {n : Nat} {m : Int},
        @IsCoprime Int Int.instCommSemiring m (@Nat.cast Int instNatCastInt n) →
          @Eq (ZMod n)
            (@HMul.hMul (ZMod n) (ZMod n) (ZMod n)
              (@instHMul (ZMod n)
                (@Distrib.toMul (ZMod n)
                  (@instDistribOfSemiring (ZMod n)
                    (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))))
              (@Int.cast (ZMod n)
                (@AddGroupWithOne.toIntCast (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
                m)
              (@Nat.cast (ZMod n)
                (@AddMonoidWithOne.toNatCast (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
                (@ZMod.val n
                  (@Inv.inv (ZMod n) (ZMod.instInv n)
                    (@Int.cast (ZMod n)
                      (@AddGroupWithOne.toIntCast (ZMod n)
                        (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
                      m)))))
            (@OfNat.ofNat (ZMod n) (nat_lit 1)
              (@One.toOfNat1 (ZMod n)
                (@AddMonoidWithOne.toOne (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  decide)) (by
  decide +kernel)

-- ZMod.intCast_mul_val_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.intCast_mul_val_inv.h3 : Not
      (∀ {n : Nat} [inst : @NeZero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) n] {m : Int},
        @Eq (ZMod n)
          (@HMul.hMul (ZMod n) (ZMod n) (ZMod n)
            (@instHMul (ZMod n)
              (@Distrib.toMul (ZMod n)
                (@instDistribOfSemiring (ZMod n)
                  (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))))
            (@Int.cast (ZMod n)
              (@AddGroupWithOne.toIntCast (ZMod n)
                (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
              m)
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              (@ZMod.val n
                (@Inv.inv (ZMod n) (ZMod.instInv n)
                  (@Int.cast (ZMod n)
                    (@AddGroupWithOne.toIntCast (ZMod n)
                      (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
                    m)))))
          (@OfNat.ofNat (ZMod n) (nat_lit 1)
            (@One.toOfNat1 (ZMod n)
              (@AddMonoidWithOne.toOne (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) _ (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- Set.BijOn.mapsTo, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.mapsTo.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.MapsTo f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.SurjOn.preimage, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.preimage.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.SurjOn f (f ⁻¹' t) t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- List.nextOr_infix_of_mem_dropLast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nextOr_infix_of_mem_dropLast.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {a : α} (d : α), [a, l.nextOr a d] <:+: l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0) (0)) (by
  decide +kernel)

-- List.nextOr_concat, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nextOr_concat.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {xs : List α} {x : α} (d : α), (xs ++ [x]).nextOr x d = d := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) (0) (1)) (by
  decide +kernel)

-- Set.SurjOn.subset_range, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.subset_range.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, t ⊆ Set.range f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Set.Finite.infinite_compl, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.infinite_compl.h1 : ¬∀ {α : Type} {s : Set α}, s.Finite → sᶜ.Infinite := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) (by
  simp)) (by
  simp)

-- Set.Finite.infinite_compl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.infinite_compl.h3 : ¬∀ {α : Type} [inst : Infinite α] {s : Set α}, sᶜ.Infinite := fun hc_h => absurd (@hc_h (ℕ) _ ({x : ℕ | True})) (by
  simp)

-- Set.injOn_insert, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.injOn_insert.h5 : ¬∀ {α β : Type} {f : α → β} {s : Set α} {a : α}, Set.InjOn f (Insert.insert a s) ↔ Set.InjOn f s ∧ f a ∉ f '' s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- List.nextOr_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nextOr_mem.h5 : ¬∀ {α : Type} [inst : DecidableEq α] {xs : List α} {x d : α}, xs.nextOr x d ∈ xs := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0) (0)) (by
  decide +kernel)

-- Set.infinite_of_finite_compl, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infinite_of_finite_compl.h1 : ¬∀ {α : Type} {s : Set α}, sᶜ.Finite → s.Infinite := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) (by
  simp)) (by
  simp)

-- Set.infinite_of_finite_compl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.infinite_of_finite_compl.h3 : ¬∀ {α : Type} [inst : Infinite α] {s : Set α}, s.Infinite := fun hc_h => absurd (@hc_h (ℕ) _ ({n : ℕ | n = 0})) (by
  simp)

-- List.nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nextOr_eq_getElem?_idxOf_succ_of_mem_dropLast.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {a : α} (d : α), Option.some (l.nextOr a d) = l[List.idxOf a l + 1]? := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0) (0)) (by
  decide +kernel)

-- Set.eq_preimage_iff_image_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_preimage_iff_image_eq.h3 : ¬∀ {α β : Type} {f : α → β} {s : Set α} {t : Set β}, s = f ⁻¹' t ↔ f '' s = t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- Nat.cast_eq_neg_cast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.cast_eq_neg_cast.h3 : Not
      (∀ {R : Type} [inst : Ring R] [inst_1 : PartialOrder R] {m n : Nat},
        Iff
          (@Eq R
            (@Nat.cast R
              (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R (@Ring.toAddGroupWithOne R inst))) m)
            (@Neg.neg R
              (@NegZeroClass.toNeg R
                (@SubNegZeroMonoid.toNegZeroClass R
                  (@SubtractionMonoid.toSubNegZeroMonoid R
                    (@SubtractionCommMonoid.toSubtractionMonoid R
                      (@AddCommGroup.toDivisionAddCommMonoid R (@Ring.toAddCommGroup R inst))))))
              (@Nat.cast R
                (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R (@Ring.toAddGroupWithOne R inst)))
                n)))
          (And (@Eq Nat m (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := fun hc_h => absurd (@hc_h (Bool) (@BooleanRing.toRing Bool instBooleanRingBool) (Bool.instPartialOrder) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (by
  decide +kernel)

-- Set.image_subset_infs_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_subset_infs_right.h5 : Not
      (∀ {α : Type} [inst : SemilatticeInf α] {s t : Set α} {a : α},
        @LE.le (Set α) (@Set.instLE α) (@Set.image α α (fun (x : α) => @Min.min α (@SemilatticeInf.toMin α inst) a x) t)
          (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s t)) := fun hc_h => absurd (@hc_h (Bool) (@Lattice.toSemilatticeInf Bool
      (@ConditionallyCompleteLattice.toLattice Bool
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Bool
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder Bool
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot Bool Bool.completeLinearOrder))))) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (Bool.false)) (by
  simp)

-- Set.image_subset_infs_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_subset_infs_left.h5 : Not
      (∀ {α : Type} [inst : SemilatticeInf α] {s t : Set α} {b : α},
        @LE.le (Set α) (@Set.instLE α) (@Set.image α α (fun (a : α) => @Min.min α (@SemilatticeInf.toMin α inst) a b) s)
          (@HasInfs.infs (Set α) (@Set.hasInfs α inst) s t)) := fun hc_h => absurd (@hc_h (Bool) (@Lattice.toSemilatticeInf Bool
      (@ConditionallyCompleteLattice.toLattice Bool
        (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice Bool
          (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder Bool
            (@CompleteLinearOrder.toConditionallyCompleteLinearOrderBot Bool Bool.completeLinearOrder))))) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (@Set.ofPred Bool fun (b : Bool) => @Eq Bool b Bool.true) (Bool.false)) (by
  simp)

-- Set.image_subset_sups_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_subset_sups_right.h5 : Not
      (∀ {α : Type} [inst : SemilatticeSup α] {s t : Set α} {a : α},
        @LE.le (Set α) (@Set.instLE α)
          (@Set.image α α ((fun (x1 x2 : α) => @Max.max α (@SemilatticeSup.toMax α inst) x1 x2) a) t)
          (@HasSups.sups (Set α) (@Set.hasSups α inst) s t)) := fun hc_h => absurd (@hc_h (Nat) (@Lattice.toSemilatticeSup Nat Nat.instLattice) (@Set.ofPred Nat fun (x : Nat) => False) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  simp)

-- Nat.neg_cast_eq_cast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.neg_cast_eq_cast.h3 : Not
      (∀ {R : Type} [inst : Ring R] [inst_1 : PartialOrder R] {m n : Nat},
        Iff
          (@Eq R
            (@Neg.neg R
              (@NegZeroClass.toNeg R
                (@SubNegZeroMonoid.toNegZeroClass R
                  (@SubtractionMonoid.toSubNegZeroMonoid R
                    (@SubtractionCommMonoid.toSubtractionMonoid R
                      (@AddCommGroup.toDivisionAddCommMonoid R (@Ring.toAddCommGroup R inst))))))
              (@Nat.cast R
                (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R (@Ring.toAddGroupWithOne R inst))) m))
            (@Nat.cast R
              (@AddMonoidWithOne.toNatCast R (@AddGroupWithOne.toAddMonoidWithOne R (@Ring.toAddGroupWithOne R inst))) n))
          (And (@Eq Nat m (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := fun hc_h => absurd (@hc_h (Bool) (@BooleanRing.toRing Bool instBooleanRingBool) (Bool.instPartialOrder) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (by
  decide +kernel)

-- Nat.cast_min, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.cast_min.h3 : Not
      (∀ {α : Type} [inst : Semiring α] [inst_1 : LinearOrder α] (m n : Nat),
        @Eq α
          (@Nat.cast α
            (@AddMonoidWithOne.toNatCast α
              (@AddCommMonoidWithOne.toAddMonoidWithOne α
                (@NonAssocSemiring.toAddCommMonoidWithOne α (@Semiring.toNonAssocSemiring α inst))))
            (@Min.min Nat instMinNat m n))
          (@Min.min α
            (@SemilatticeInf.toMin α
              (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))
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

-- List.IsChain.two_mul_count_bool_of_even, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.two_mul_count_bool_of_even.h1 : ¬∀ {l : List Bool}, Even l.length → ∀ (b : Bool), 2 * List.count b l = l.length := fun hc_h => absurd (@hc_h ([Bool.false, Bool.false]) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- List.IsChain.two_mul_count_bool_of_even, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.two_mul_count_bool_of_even.h2 : ¬∀ {l : List Bool}, List.IsChain (fun (x1 x2 : Bool) => x1 ≠ x2) l → ∀ (b : Bool), 2 * List.count b l = l.length := fun hc_h => absurd (@hc_h ([Bool.false]) (by
  decide) (Bool.false)) (by
  decide +kernel)

-- Nat.minFac_le_of_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.minFac_le_of_dvd.h2 : ¬∀ {n m : ℕ}, m ∣ n → n.minFac ≤ m := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.minFac_le_of_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.minFac_le_of_dvd.h3 : ¬∀ {n m : ℕ}, 2 ≤ m → n.minFac ≤ m := fun hc_h => absurd (@hc_h (3) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.prime_dvd_prime_iff_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prime_dvd_prime_iff_eq.h2 : ¬∀ {p q : ℕ}, Nat.Prime q → (p ∣ q ↔ p = q) := fun hc_h => absurd (@hc_h (1) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.prime_dvd_prime_iff_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prime_dvd_prime_iff_eq.h3 : ¬∀ {p q : ℕ}, Nat.Prime p → (p ∣ q ↔ p = q) := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.dvd_prime_two_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_prime_two_le.h2 : ¬∀ {p m : ℕ}, 2 ≤ m → (m ∣ p ↔ m = p) := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.dvd_prime_two_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_prime_two_le.h3 : ¬∀ {p m : ℕ}, Nat.Prime p → (m ∣ p ↔ m = p) := fun hc_h => absurd (@hc_h (2) (1) (by
  decide)) (by
  decide +kernel)

-- Fin.xor_assoc, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.xor_assoc.h2 : ¬∀ {n : ℕ} {k : ℕ} (a b c : Fin k), a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := fun hc_h => absurd (@hc_h (0) (3) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3)) ((⟨2, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3))) (by
  decide +kernel)

-- Fin.take_repeat, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.take_repeat.h4 : ¬∀ {n : ℕ} {α : Type} {n' : ℕ} (m : ℕ) (a : Fin n' → α), m ≤ n := fun hc_h => absurd (@hc_h (0) (ℕ) (0) (1) (fun (a : Fin 0) => 0)) (by
  decide +kernel)

-- AddCommGroup.intCast_modEq_intCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.AddCommGroup.intCast_modEq_intCast.h2 : Not
      (∀ {G : Type} [inst : AddCommGroupWithOne G] {a b z : Int},
        Iff
          (@AddCommGroup.ModEq G
            (@AddCommMonoidWithOne.toAddCommMonoid G (@AddCommGroupWithOne.toAddCommMonoidWithOne G inst))
            (@Int.cast G (@AddGroupWithOne.toIntCast G (@AddCommGroupWithOne.toAddGroupWithOne G inst)) z)
            (@Int.cast G (@AddGroupWithOne.toIntCast G (@AddCommGroupWithOne.toAddGroupWithOne G inst)) a)
            (@Int.cast G (@AddGroupWithOne.toIntCast G (@AddCommGroupWithOne.toAddGroupWithOne G inst)) b))
          (@AddCommGroup.ModEq Int Int.instAddCommMonoid z a b)) := fun hc_h => absurd (@hc_h (Bool) (@NonAssocRing.toAddCommGroupWithOne Bool
      (@NonAssocCommRing.toNonAssocRing Bool
        (@CommRing.toNonAssocCommRing Bool (@BooleanRing.toCommRing Bool instBooleanRingBool)))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  (simp <;> decide))

-- Set.BijOn.injOn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.injOn.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.InjOn f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | True}) ({n : ℕ | n = 0}) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Fintype.card_subtype_eq_or_eq_of_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_subtype_eq_or_eq_of_ne.h5 : ¬∀ {α : Type} [inst : Fintype α] [inst_1 : DecidableEq α] {a b : α}, Fintype.card { c : α // c = a ∨ c = b } = 2 := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype) (instDecidableEqBool) (Bool.false) (Bool.false)) (by
  decide +kernel)

-- Nat.coprime_of_lt_minFac, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_of_lt_minFac.h2 : ¬∀ {n m : ℕ}, m < n.minFac → n.Coprime m := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.coprime_of_lt_minFac, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_of_lt_minFac.h3 : ¬∀ {n m : ℕ}, m ≠ 0 → n.Coprime m := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Set.mem_image_of_mem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_image_of_mem.h5 : ¬∀ {α β : Type} (f : α → β) {x : α} {a : Set α}, f x ∈ f '' a := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (1) ({n : ℕ | n = 0})) (by
  simp)

-- Nat.perm_primeFactorsList_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.perm_primeFactorsList_mul.h2 : ¬∀ {a b : ℕ}, b ≠ 0 → (a * b).primeFactorsList.Perm (a.primeFactorsList ++ b.primeFactorsList) := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.perm_primeFactorsList_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.perm_primeFactorsList_mul.h3 : ¬∀ {a b : ℕ}, a ≠ 0 → (a * b).primeFactorsList.Perm (a.primeFactorsList ++ b.primeFactorsList) := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- List.dlookup_kerase, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dlookup_kerase.h5 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] (a : α) {l : List (Sigma β)},
        List.dlookup a (List.kerase a l) = Option.none := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ), (⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  decide +kernel)

-- List.lookupAll_nodup, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lookupAll_nodup.h5 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] (a : α) {l : List (Sigma β)}, (List.lookupAll a l).Nodup := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) (0) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ), (⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  decide +kernel)

-- Nat.mem_primeFactorsList_iff_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mem_primeFactorsList_iff_dvd.h2 : ¬∀ {n p : ℕ}, Nat.Prime p → (p ∈ n.primeFactorsList ↔ p ∣ n) := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.mem_primeFactorsList_iff_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mem_primeFactorsList_iff_dvd.h3 : ¬∀ {n p : ℕ}, n ≠ 0 → (p ∈ n.primeFactorsList ↔ p ∣ n) := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.disjoint_primeFactors, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.disjoint_primeFactors.h2 : ¬∀ {a b : ℕ}, b ≠ 0 → (Disjoint a.primeFactors b.primeFactors ↔ a.Coprime b) := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.disjoint_primeFactors, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.disjoint_primeFactors.h3 : ¬∀ {a b : ℕ}, a ≠ 0 → (Disjoint a.primeFactors b.primeFactors ↔ a.Coprime b) := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.primeFactors_gcd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactors_gcd.h2 : ¬∀ {a b : ℕ}, b ≠ 0 → (a.gcd b).primeFactors = a.primeFactors ∩ b.primeFactors := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.primeFactors_gcd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactors_gcd.h3 : ¬∀ {a b : ℕ}, a ≠ 0 → (a.gcd b).primeFactors = a.primeFactors ∩ b.primeFactors := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- AList.mk_cons_eq_insert, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.AList.mk_cons_eq_insert.h5 : ¬∀ {α : Type} {β : α → Type} [inst : DecidableEq α] (c : Sigma β) (l : List (Sigma β)), (c :: l).NodupKeys := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) (instDecidableEqNat) ((⟨0, 0⟩ : (_ : ℕ) × ℕ)) ([(⟨0, 0⟩ : (_ : ℕ) × ℕ)])) (by
  simp)

-- Set.range_subtype_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.range_subtype_map.h5 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} (f : α → β) (x : α), p x → q (f x) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Fintype.prod_eq_one, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.prod_eq_one.h5 : ¬∀ {α M : Type} [inst : Fintype α] [inst_1 : CommMonoid M] (f : α → M), ∏ a : α, f a = 1 := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (Nat.instCommMonoid) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  decide +kernel)

-- ZMod.isUnit_prime_of_not_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.isUnit_prime_of_not_dvd.h2 : Not
      (∀ {n p : Nat},
        Not (@Dvd.dvd Nat Nat.instDvd p n) →
          @IsUnit (ZMod n)
            (@Semiring.toMonoid (ZMod n)
              (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              p)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- ZMod.isUnit_prime_of_not_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.isUnit_prime_of_not_dvd.h3 : Not
      (∀ {n p : Nat},
        Nat.Prime p →
          @IsUnit (ZMod n)
            (@Semiring.toMonoid (ZMod n)
              (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              p)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Matrix.cons_val_succ', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Matrix.cons_val_succ'.h3 : ¬∀ {α : Type} {m i : ℕ} (x : α) (u : Fin m → α), i.succ < m.succ := fun hc_h => absurd (@hc_h (ℕ) (0) (0) (0) (fun (a : Fin 0) => 0)) (by
  decide +kernel)

-- Nat.choose_lt_descFactorial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_lt_descFactorial.h2 : ¬∀ {n k : ℕ}, k ≤ n → n.choose k < n.descFactorial k := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.choose_lt_descFactorial, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_lt_descFactorial.h3 : ¬∀ {n k : ℕ}, 2 ≤ k → n.choose k < n.descFactorial k := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- List.mapIdxM'_eq_mapIdxM, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mapIdxM'_eq_mapIdxM.h2 : ¬∀ {m : Type → Type} [inst : Monad m] {α : Type} (f : ℕ → α → m PUnit.{1}) (as : List α),
        List.mapIdxM' f as = List.mapIdxM f as *> Pure.pure PUnit.unit := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => ℕ × α) (ℕ) (fun (a a_1 : ℕ) => (0, PUnit.unit)) ([])) (by
  decide +kernel)

-- Part.mem_map, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.mem_map.h5 : ¬∀ {α β : Type} (f : α → β) {o : Part α} {a : α}, f a ∈ Part.map f o := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (0) (1)) (by
  nofun)

-- Nat.digits_of_two_le_of_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_of_two_le_of_pos.h2 : ¬∀ {n b : ℕ}, 0 < n → b.digits n = n % b :: b.digits (n / b) := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.digits_of_two_le_of_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_of_two_le_of_pos.h3 : ¬∀ {n b : ℕ}, 2 ≤ b → b.digits n = n % b :: b.digits (n / b) := fun hc_h => absurd (@hc_h (0) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.repr_length, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.repr_length.h2 : ¬∀ (n e : ℕ), n < 10 ^ e → n.repr.length ≤ e := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.repr_length, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.repr_length.h3 : ¬∀ (n e : ℕ), 0 < e → n.repr.length ≤ e := fun hc_h => absurd (@hc_h (10) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.digits_eq_cons_digits_div, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_eq_cons_digits_div.h2 : ¬∀ {b n : ℕ}, n ≠ 0 → b.digits n = n % b :: b.digits (n / b) := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.digits_eq_cons_digits_div, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_eq_cons_digits_div.h3 : ¬∀ {b n : ℕ}, 1 < b → b.digits n = n % b :: b.digits (n / b) := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ofDigits_div_eq_ofDigits_tail, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofDigits_div_eq_ofDigits_tail.h3 : ¬∀ {p : ℕ}, 0 < p → ∀ (digits : List ℕ), Nat.ofDigits p digits / p = Nat.ofDigits p digits.tail := fun hc_h => absurd (@hc_h (1) (by
  decide) ([1])) (by
  decide +kernel)

-- Rat.toNNRat_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.toNNRat_add.h2 : ¬∀ {p q : ℚ}, 0 ≤ p → (q + p).toNNRat = q.toNNRat + p.toNNRat := fun hc_h => absurd (@hc_h (1) (-1) (by
  decide)) (by
  decide +kernel)

-- Rat.toNNRat_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.toNNRat_add.h3 : ¬∀ {p q : ℚ}, 0 ≤ q → (q + p).toNNRat = q.toNNRat + p.toNNRat := fun hc_h => absurd (@hc_h (-1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.base_pow_length_digits_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.base_pow_length_digits_le.h3 : ¬∀ (b m : ℕ), 1 < b → b ^ (b.digits m).length ≤ b * m := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.not_dvd_divMaxPow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_dvd_divMaxPow.h2 : ¬∀ {p n : ℕ}, n ≠ 0 → ¬p ∣ n.divMaxPow p := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.not_dvd_divMaxPow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_dvd_divMaxPow.h3 : ¬∀ {p n : ℕ}, 1 < p → ¬p ∣ n.divMaxPow p := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- ENat.toNat_le_toNat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.toNat_le_toNat.h2 : ¬∀ {m n : ℕ∞}, n ≠ ⊤ → m.toNat ≤ n.toNat := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- ENat.toNat_le_toNat, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.toNat_le_toNat.h3 : ¬∀ {m n : ℕ∞}, m ≤ n → m.toNat ≤ n.toNat := fun hc_h => absurd (@hc_h (1) (⊤) (by
  decide)) (by
  decide +kernel)

-- PNat.mk_lt_mk, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.mk_lt_mk.h2 : ¬∀ (n k : ℕ), 0 < k → 0 < n := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- PNat.mk_lt_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.mk_lt_mk.h3 : ¬∀ (n k : ℕ), 0 < n → 0 < k := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.maxPowDvdDiv_base_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.maxPowDvdDiv_base_mul.h2 : ¬∀ {p n : ℕ}, n ≠ 0 → p.maxPowDvdDiv (p * n) = (multiplicity p n + 1, n.divMaxPow p) := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.maxPowDvdDiv_base_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.maxPowDvdDiv_base_mul.h3 : ¬∀ {p n : ℕ}, 1 < p → p.maxPowDvdDiv (p * n) = (multiplicity p n + 1, n.divMaxPow p) := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- padicValNat_base_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.padicValNat_base_mul.h2 : ¬∀ {p n : ℕ}, n ≠ 0 → multiplicity p (p * n) = multiplicity p n + 1 := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  simp)

-- Nat.eq_factorization_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.eq_factorization_iff.h2 : ¬∀ {n : ℕ} {f : ℕ →₀ ℕ},
        (∀ p ∈ f.support, Nat.Prime p) → (f = n.factorization ↔ (f.prod fun (x1 x2 : ℕ) => x1 ^ x2) = n) := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.ordProj_dvd_ordProj_iff_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordProj_dvd_ordProj_iff_dvd.h2 : ¬∀ {a b : ℕ}, b ≠ 0 → ((∀ (p : ℕ), p ^ a.factorization p ∣ p ^ b.factorization p) ↔ a ∣ b) := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- Nat.Prime.coprime_factorial_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.coprime_factorial_of_lt.h2 : ¬∀ {p n : ℕ}, n < p → p.Coprime n.factorial := fun hc_h => absurd (@hc_h (4) (2) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.coprime_factorial_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.coprime_factorial_of_lt.h3 : ¬∀ {p n : ℕ}, Nat.Prime p → p.Coprime n.factorial := fun hc_h => absurd (@hc_h (2) (2) (by
  decide)) (by
  decide +kernel)

-- ENat.sub_sub_cancel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.sub_sub_cancel.h2 : ¬∀ {a b : ℕ∞}, b ≤ a → a - (a - b) = b := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  decide +kernel)

-- ENat.sub_sub_cancel, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.sub_sub_cancel.h3 : ¬∀ {a b : ℕ∞}, a ≠ ⊤ → a - (a - b) = b := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- ENat.lt_add_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.lt_add_left.h2 : ¬∀ {n k : ℕ∞}, 0 < k → n < k + n := fun hc_h => absurd (@hc_h (⊤) (1) (by
  decide)) (by
  decide +kernel)

-- ENat.lt_add_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.lt_add_left.h3 : ¬∀ {n k : ℕ∞}, n ≠ ⊤ → n < k + n := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- Subtype.map_def, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.map_def.h5 : ¬∀ {α β : Type} {p : α → Prop} {q : β → Prop} (f : α → β) (a : α), p a → q (f a) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n = 0 : ℕ → Prop) (fun n => n = 0 : ℕ → Prop) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Nat.Prime.eq_of_factorization_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.eq_of_factorization_pos.h2 : ¬∀ {p q : ℕ}, p.factorization q ≠ 0 → p = q := fun hc_h => absurd (@hc_h (4) (2) (by
  decide +kernel)) (by
  decide +kernel)

-- Nat.Prime.eq_of_factorization_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.eq_of_factorization_pos.h3 : ¬∀ {p q : ℕ}, Nat.Prime p → p = q := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.dvd_pow_self_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_pow_self_iff.h2 : ¬∀ {n k : ℕ}, k ≠ 0 → (n ∣ k ^ n ↔ n.primeFactors ⊆ k.primeFactors) := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.dvd_pow_self_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_pow_self_iff.h3 : ¬∀ {n k : ℕ}, n ≠ 0 → (n ∣ k ^ n ↔ n.primeFactors ⊆ k.primeFactors) := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- ENat.map_natCast_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.map_natCast_mul.h3 : Not
      (∀ {R : Type} [inst : NonAssocSemiring R] [inst_1 : DecidableEq R] (a b : ENat),
        @Eq (WithTop R)
          (@ENat.map R
            (@Nat.cast R
              (@AddMonoidWithOne.toNatCast R
                (@AddCommMonoidWithOne.toAddMonoidWithOne R (@NonAssocSemiring.toAddCommMonoidWithOne R inst))))
            (@HMul.hMul ENat ENat ENat
              (@instHMul ENat
                (@Distrib.toMul ENat (@instDistribOfSemiring ENat (@CommSemiring.toSemiring ENat instCommSemiringENat))))
              a b))
          (@HMul.hMul (WithTop R) (WithTop R) (WithTop R)
            (@instHMul (WithTop R)
              (@MulZeroClass.toMul (WithTop R)
                (@WithTop.instMulZeroClass R inst_1
                  (@NonUnitalNonAssocSemiring.toMulZeroClass R (@NonAssocSemiring.toNonUnitalNonAssocSemiring R inst)))))
            (@ENat.map R
              (@Nat.cast R
                (@AddMonoidWithOne.toNatCast R
                  (@AddCommMonoidWithOne.toAddMonoidWithOne R (@NonAssocSemiring.toAddCommMonoidWithOne R inst))))
              a)
            (@ENat.map R
              (@Nat.cast R
                (@AddMonoidWithOne.toNatCast R
                  (@AddCommMonoidWithOne.toAddMonoidWithOne R (@NonAssocSemiring.toAddCommMonoidWithOne R inst))))
              b))) := fun hc_h => absurd (@hc_h (Bool) (@Semiring.toNonAssocSemiring Bool
      (@CommSemiring.toSemiring Bool (@CommRing.toCommSemiring Bool (@BooleanRing.toCommRing Bool instBooleanRingBool)))) (instDecidableEqBool) (@OfNat.ofNat ENat (nat_lit 2)
      (@instOfNatAtLeastTwo ENat (nat_lit 2) ENat.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) (@Top.top ENat instTopENat)) (by
  decide +kernel)

-- List.IsZeckendorfRep.sum_fib_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsZeckendorfRep.sum_fib_lt.h2 : ¬∀ {n : ℕ} {l : List ℕ}, (∀ a ∈ (l ++ [0]).head?, a < n) → (List.map Nat.fib l).sum < Nat.fib n := fun hc_h => absurd (@hc_h (1) ([0, 1]) (by
  decide)) (by
  decide +kernel)

-- List.IsZeckendorfRep.sum_fib_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsZeckendorfRep.sum_fib_lt.h3 : ¬∀ {n : ℕ} {l : List ℕ}, l.IsZeckendorfRep → (List.map Nat.fib l).sum < Nat.fib n := fun hc_h => absurd (@hc_h (0) ([]) (by
  simp)) (by
  decide +kernel)

-- Nat.prod_pow_prime_padicValNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prod_pow_prime_padicValNat.h1 : ¬∀ (n m : ℕ), n < m → ∏ p ∈ Finset.range m with Nat.Prime p, p ^ multiplicity p n = n := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.prod_pow_prime_padicValNat, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prod_pow_prime_padicValNat.h3 : ¬∀ (n : ℕ), n ≠ 0 → ∀ (m : ℕ), ∏ p ∈ Finset.range m with Nat.Prime p, p ^ multiplicity p n = n := fun hc_h => absurd (@hc_h (2) (by
  decide) (0)) (by
  decide +kernel)

-- Option.map₂_right_identity, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.map₂_right_identity.h4 : ¬∀ {α β : Type} {f : α → β → α} {b : β} (o : Option α), Option.map₂ f o (Option.some b) = o := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun (a : Bool) (n : ℕ) => n % 2 == 0) (0) (Option.some Bool.false)) (by
  decide +kernel)

-- Nat.exists_dvd_pow_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_dvd_pow_iff.h2 : ¬∀ {n k : ℕ}, k ≠ 0 → ((∃ (m : ℕ), n ∣ k ^ m) ↔ n.primeFactors ⊆ k.primeFactors) := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  simp)

-- Nat.Prime.dvd_iff_one_le_factorization, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_iff_one_le_factorization.h2 : ¬∀ {p n : ℕ}, n ≠ 0 → (p ∣ n ↔ 1 ≤ n.factorization p) := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.Prime.dvd_iff_one_le_factorization, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_iff_one_le_factorization.h3 : ¬∀ {p n : ℕ}, Nat.Prime p → (p ∣ n ↔ 1 ≤ n.factorization p) := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Option.map₂_left_identity, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Option.map₂_left_identity.h4 : ¬∀ {α β : Type} {f : α → β → β} {a : α} (o : Option β), Option.map₂ f (Option.some a) o = o := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a - b : ℕ → ℕ → ℕ) (0) (Option.some 1)) (by
  decide +kernel)

-- Nat.nth_add_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_add_one.h2 : ¬∀ {p : ℕ → Prop} {n : ℕ}, Nat.nth p n ≠ 0 → Nat.nth (fun (i : ℕ) => p (i + 1)) n + 1 = Nat.nth p n := fun hc_h => absurd (@hc_h (fun _ => True : ℕ → Prop) (1) (by
  simp)) (by
  simp)

-- Nat.nth_add_one, hypothesis 3: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.nth_add_one.h3.inst : ¬Nat.nth (fun (i : ℕ) => (fun (x : ℕ) => False) (i + 1)) 0 + 1 = Nat.nth (fun (x : ℕ) => False) 0 := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Nat.nth_add_one.h3.prem0 : ¬(fun (x : ℕ) => False) 0 := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Nat.nth_add_one.h3 : ¬∀ {p : ℕ → Prop} {n : ℕ}, ¬p 0 → Nat.nth (fun (i : ℕ) => p (i + 1)) n + 1 = Nat.nth p n := fun hc_h => HypCheckProof.Nat.nth_add_one.h3.inst (@hc_h (fun (x : ℕ) => False) (0) HypCheckProof.Nat.nth_add_one.h3.prem0)

-- Set.EqOn.image_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.EqOn.image_eq.h5 : ¬∀ {α β : Type} {s : Set α} {f₁ f₂ : α → β}, f₁ '' s = f₂ '' s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Nat.nth_add_one_eq_sub, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_add_one_eq_sub.h2 : ¬∀ {p : ℕ → Prop} {n : ℕ}, Nat.nth p n ≠ 0 → Nat.nth (fun (i : ℕ) => p (i + 1)) n = Nat.nth p n - 1 := fun hc_h => absurd (@hc_h (fun _ => True : ℕ → Prop) (1) (by
  simp)) (by
  simp)

-- ZNum.cast_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZNum.cast_le.h3 : Not
      (∀ {α : Type} [inst : Ring α] [inst_1 : LinearOrder α] {m n : ZNum},
        Iff
          (@LE.le α
            (@Preorder.toLE α
              (@PartialOrder.toPreorder α
                (@SemilatticeInf.toPartialOrder α
                  (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
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
          (@LE.le ZNum ZNum.instLE m n)) := fun hc_h => absurd (@hc_h (Bool) (@BooleanRing.toRing Bool instBooleanRingBool) (Bool.linearOrder) (ZNum.zero) (ZNum.neg PosNum.one)) (by
  decide +kernel)

-- ZNum.cast_inj, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZNum.cast_inj.h3 : Not
      (∀ {α : Type} [inst : Ring α] [inst_1 : PartialOrder α] {m n : ZNum},
        Iff
          (@Eq α
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
          (@Eq ZNum m n)) := fun hc_h => absurd (@hc_h (Bool) (@BooleanRing.toRing Bool instBooleanRingBool) (Bool.instPartialOrder) (ZNum.pos PosNum.one) (ZNum.neg PosNum.one)) (by
  decide +kernel)

-- Set.BijOn.surjOn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.surjOn.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, Set.SurjOn f s t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Ordnode.delta_lt_false, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.delta_lt_false.h2 : ¬∀ {a b : ℕ}, Ordnode.delta * b < a → False := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- Ordnode.delta_lt_false, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.delta_lt_false.h3 : ¬∀ {a b : ℕ}, Ordnode.delta * a < b → False := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Set.SurjOn.nonempty_or_eq_empty, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.SurjOn.nonempty_or_eq_empty.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {f : α → β}, s.Nonempty ∨ t = ∅ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Ordnode.Sized.size_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.size_eq.h5 : ¬∀ {α : Type} {s : ℕ} {l : Ordnode α} {x : α} {r : Ordnode α}, (Ordnode.node s l x r).size = l.size + r.size + 1 := fun hc_h => absurd (@hc_h (ℕ) (0) (Ordnode.nil) (0) (Ordnode.nil)) (by
  decide +kernel)

-- AddCommGroup.ModEq.natCast, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.AddCommGroup.ModEq.natCast.h5 : Not
      (∀ {M : Type} [inst : AddCommMonoidWithOne M] {a b n : Nat},
        @AddCommGroup.ModEq M (@AddCommMonoidWithOne.toAddCommMonoid M inst)
          (@Nat.cast M (@AddMonoidWithOne.toNatCast M (@AddCommMonoidWithOne.toAddMonoidWithOne M inst)) n)
          (@Nat.cast M (@AddMonoidWithOne.toNatCast M (@AddCommMonoidWithOne.toAddMonoidWithOne M inst)) a)
          (@Nat.cast M (@AddMonoidWithOne.toNatCast M (@AddCommMonoidWithOne.toAddMonoidWithOne M inst)) b)) := fun hc_h => absurd (@hc_h (Nat) (Nat.instAddCommMonoidWithOne) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  simp)

-- Set.image_prodMk_subset_prod_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_prodMk_subset_prod_right.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {a : α}, Prod.mk a '' t ⊆ s ×ˢ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- Function.Semiconj.mapsTo_range, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Semiconj.mapsTo_range.h5 : ¬∀ {α β : Type} {fa : α → α} {fb : β → β} {f : α → β}, Set.MapsTo fb (Set.range f) (Set.range f) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) (fun n => n + 1 : ℕ → ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Nat.odd_mul_odd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.odd_mul_odd.h2 : ¬∀ {n m : ℕ}, m % 2 = 1 → n * m % 2 = 1 := fun hc_h => absurd (@hc_h (0) (1) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Nat.odd_mul_odd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.odd_mul_odd.h3 : ¬∀ {n m : ℕ}, n % 2 = 1 → n * m % 2 = 1 := fun hc_h => absurd (@hc_h (1) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Quot.lift_mk, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Quot.lift_mk.h4 : ¬∀ {α γ : Type} {r : α → α → Prop} (f : α → γ) (a a₁ a₂ : α), r a₁ a₂ → f a₁ = f a₂ := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ _ => True : Bool → Bool → Prop) (fun b => if b then 1 else 0 : Bool → ℕ) (Bool.false)) (by
  decide +kernel)

-- List.getLast_getLast_eq_getLast_flatten, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getLast_getLast_eq_getLast_flatten.h2 : ¬∀ {α : Type} {l : List (List α)}, l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- List.getLast_getLast_eq_getLast_flatten, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getLast_getLast_eq_getLast_flatten.h3 : ¬∀ {α : Type} {l : List (List α)} (hl : l ≠ []), l.getLast hl ≠ [] := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) ([[]]) hc_k0) (by
  decide +kernel)

-- List.head_head_eq_head_flatten, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.head_head_eq_head_flatten.h2 : ¬∀ {α : Type} {l : List (List α)}, l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- List.head_head_eq_head_flatten, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.head_head_eq_head_flatten.h3 : ¬∀ {α : Type} {l : List (List α)} (hl : l ≠ []), l.head hl ≠ [] := fun hc_h => absurd (fun hc_k0 => @hc_h (ℕ) ([[]]) hc_k0) (by
  decide +kernel)

-- Ordnode.Sized.pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.pos.h5 : ¬∀ {α : Type} {s : ℕ} {l : Ordnode α} {x : α} {r : Ordnode α}, 0 < s := fun hc_h => absurd (@hc_h (ℕ) (0) (Ordnode.nil) (0) (Ordnode.nil)) (by
  decide +kernel)

-- Nat.ModEq.add_iff_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.add_iff_right.h5 : ¬∀ {n a b c d : ℕ}, a + c ≡ b + d [MOD n] ↔ a ≡ b [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (0) (0) (1)) (by
  decide +kernel)

-- Nat.odd_mul_odd_div_two, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.odd_mul_odd_div_two.h3 : ¬∀ {m n : ℕ}, m % 2 = 1 → m * n / 2 = m * (n / 2) + m / 2 := fun hc_h => absurd (@hc_h (3) (0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- Nat.dvd_factorial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_factorial.h2 : ¬∀ {m n : ℕ}, m ≤ n → m ∣ n.factorial := fun hc_h => absurd (@hc_h (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.dvd_factorial, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_factorial.h3 : ¬∀ {m n : ℕ}, 0 < m → m ∣ n.factorial := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.add_factorial_lt_factorial_add, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_factorial_lt_factorial_add.h2 : ¬∀ {i n : ℕ}, 1 ≤ n → i + n.factorial < (i + n).factorial := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.add_factorial_lt_factorial_add, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_factorial_lt_factorial_add.h3 : ¬∀ {i n : ℕ}, 2 ≤ i → i + n.factorial < (i + n).factorial := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.iterate, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.iterate.h4 : ¬∀ {α : Type} {r : α → α → Prop} {f : α → α} {a : α} {n : ℕ}, List.IsChain r (List.iterate f a n) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun _ => 0 : ℕ → ℕ) (0) (2)) (by
  decide +kernel)

-- Nat.exists_mul_mod_eq_one_of_coprime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_mul_mod_eq_one_of_coprime.h2 : ¬∀ {k n : ℕ}, 1 < k → ∃ m < k, n * m % k = 1 := fun hc_h => absurd (@hc_h (2) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.exists_mul_mod_eq_one_of_coprime, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_mul_mod_eq_one_of_coprime.h3 : ¬∀ {k n : ℕ}, n.Coprime k → ∃ m < k, n * m % k = 1 := fun hc_h => absurd (@hc_h (0) (1) (by
  decide)) (by
  decide +kernel)

-- Set.prod_subset_prod_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.prod_subset_prod_right.h5 : ¬∀ {α β : Type} {s : Set α} {t₁ t₂ : Set β}, s ×ˢ t₁ ⊆ s ×ˢ t₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Quot.liftOn_mk, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Quot.liftOn_mk.h5 : ¬∀ {α γ : Type} {r : α → α → Prop} (a : α) (f : α → γ) (a₁ a₂ : α), r a₁ a₂ → f a₁ = f a₂ := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ _ => True : Bool → Bool → Prop) (Bool.false) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  decide +kernel)

-- nsmul_eq_zero_iff_of_coprime, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.nsmul_eq_zero_iff_of_coprime.h5 : ¬∀ {M : Type} [inst : AddMonoid M] {a : M} {m n : ℕ}, m • a = 0 ∧ n • a = 0 ↔ a = 0 := fun hc_h => absurd (@hc_h (ℕ) (Nat.instAddMonoid) (1) (0) (0)) (by
  decide +kernel)

-- Fintype.leftInverse_bijInv, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.leftInverse_bijInv.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst : DecidableEq β] {f : α → β}, Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (instDecidableEqNat) (fun _ => 0 : Bool → ℕ)) (by
  nofun)

-- Fintype.bijective_bijInv, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.bijective_bijInv.h5 : ¬∀ {α β : Type} [inst : Fintype α] [inst : DecidableEq β] {f : α → β}, Function.Bijective f := fun hc_h => absurd (@hc_h (Bool) (ℕ) (Bool.fintype) (instDecidableEqNat) (fun _ => 0 : Bool → ℕ)) (by
  nofun)

-- Set.image_prodMk_subset_prod_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_prodMk_subset_prod_left.h5 : ¬∀ {α β : Type} {s : Set α} {t : Set β} {b : β}, (fun (a : α) => (a, b)) '' s ⊆ s ×ˢ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- Set.Nonempty.ncard_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.ncard_pos.h2 : ¬∀ {α : Type} {s : Set α}, s.Nonempty → 0 < s.ncard := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True}) (by
  simp)) (by
  simp)

-- Set.Nonempty.ncard_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.ncard_pos.h3 : ¬∀ {α : Type} {s : Set α}, autoParam s.Finite Set.ncard_pos._auto_1 → 0 < s.ncard := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (by
  simp)) (by
  simp)

-- pow_mem_range_pow_of_coprime, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.pow_mem_range_pow_of_coprime.h4 : ¬∀ {α : Type} [inst : CommGroupWithZero α] {m n : ℕ} (a : α),
        (a ^ m ∈ Set.range fun (x : α) => x ^ n) ↔ a ∈ Set.range fun (x : α) => x ^ n := fun hc_h => absurd (@hc_h (ℚ) (Rat.commGroupWithZero) (0) (0) (0)) (by
  simp)

-- Set.mem_range_of_mem_image, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_range_of_mem_image.h5 : ¬∀ {α β : Type} (f : α → β) (s : Set α) {x : β}, x ∈ Set.range f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- Set.image_eq_image, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_eq_image.h5 : ¬∀ {α β : Type} {s t : Set α} {f : α → β}, f '' s = f '' t ↔ s = t := fun hc_h => absurd (@hc_h (Bool) (ℕ) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (fun _ => 0 : Bool → ℕ)) (by
  simp)

-- Set.even_ncard_compl_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.even_ncard_compl_iff.h1 : ¬∀ {α : Type}, Even (Nat.card α) → ∀ (s : Set α), Even sᶜ.ncard ↔ Even s.ncard := fun hc_h => absurd (@hc_h (ℕ) (by
  simp) ({n : ℕ | n = 0})) (by
  simp)

-- Set.Nonempty.of_sUnion_eq_univ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.of_sUnion_eq_univ.h3 : ¬∀ {α : Type} [inst : Nonempty α] {s : Set (Set α)}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) _ (∅)) (by
  simp)

-- Set.biUnion_subset_biUnion_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.biUnion_subset_biUnion_left.h5 : ¬∀ {α β : Type} {s s' : Set α} {t : α → Set β}, ⋃ x ∈ s, t x ⊆ ⋃ x ∈ s', t x := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) (fun (a : ℕ) => {n : ℕ | n = 0})) (by
  simp)

-- DFinsupp.Lex.isOrderedCancelAddMonoid, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.DFinsupp.Lex.isOrderedCancelAddMonoid.h5 : ¬∀ {ι : Type} {α : ι → Type} [inst : LinearOrder ι] [inst_1 : (i : ι) → AddCommMonoid (α i)]
        [inst_2 : (i : ι) → PartialOrder (α i)], IsOrderedCancelAddMonoid (Lex (Π₀ (i : ι), α i)) := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Bool) (Bool.linearOrder) (fun (i : Bool) => CommRing.toCommSemiring.toAddCommMonoid) (fun (i : Bool) => Bool.instPartialOrder)) (by
  nofun)

-- Set.prod_mono_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.prod_mono_left.h5 : ¬∀ {α β : Type} {s₁ s₂ : Set α} {t : Set β}, s₁ ×ˢ t ⊆ s₂ ×ˢ t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- Nat.count_mono_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_mono_left.h5 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {q : ℕ → Prop} [inst_1 : DecidablePred q] {n : ℕ},
        Nat.count p n ≤ Nat.count q n := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (1)) (by
  decide +kernel)

-- Set.BijOn.ncard_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.BijOn.ncard_eq.h5 : ¬∀ {α β : Type} {s : Set α} {f : α → β} {t : Set β}, s.ncard = t.ncard := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ) ({x : ℕ | False})) (by
  simp)

-- Nat.totient_prime_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_prime_pow.h1 : ¬∀ {p n : ℕ}, 0 < n → (p ^ n).totient = p ^ (n - 1) * (p - 1) := fun hc_h => absurd (@hc_h (1) (1) (by
  decide)) (by
  decide +kernel)

-- Nat.totient_prime_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_prime_pow.h3 : ¬∀ {p : ℕ}, Nat.Prime p → ∀ {n : ℕ}, (p ^ n).totient = p ^ (n - 1) * (p - 1) := fun hc_h => absurd (@hc_h (3) (by
  decide) (0)) (by
  decide +kernel)

-- Set.ncard_add_ncard_compl, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_add_ncard_compl.h3 : ¬∀ {α : Type} (s : Set α), autoParam s.Finite Set.ncard_add_ncard_compl._auto_1 → s.ncard + sᶜ.ncard = Nat.card α := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (by
  simp)) (by
  simp)

-- ZMod.eq_zero_of_gcd_ne_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.eq_zero_of_gcd_ne_one.h2 : Not
      (∀ {a : Int} {p : Nat},
        @Ne Nat (a.gcd (@Nat.cast Int instNatCastInt p)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq (ZMod p)
            (@Int.cast (ZMod p)
              (@AddGroupWithOne.toIntCast (ZMod p)
                (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p))))
              a)
            (@OfNat.ofNat (ZMod p) (nat_lit 0)
              (@Zero.toOfNat0 (ZMod p)
                (@MulZeroClass.toZero (ZMod p)
                  (@instMulZeroClassOfSemiring (ZMod p)
                    (@CommSemiring.toSemiring (ZMod p) (@CommRing.toCommSemiring (ZMod p) (ZMod.commRing p)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by
  decide)) (by
  decide +kernel)

-- ZMod.eq_zero_of_gcd_ne_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.eq_zero_of_gcd_ne_one.h3 : Not
      (∀ {a : Int} {p : Nat},
        Nat.Prime p →
          @Eq (ZMod p)
            (@Int.cast (ZMod p)
              (@AddGroupWithOne.toIntCast (ZMod p)
                (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p))))
              a)
            (@OfNat.ofNat (ZMod p) (nat_lit 0)
              (@Zero.toOfNat0 (ZMod p)
                (@MulZeroClass.toZero (ZMod p)
                  (@instMulZeroClassOfSemiring (ZMod p)
                    (@CommSemiring.toSemiring (ZMod p) (@CommRing.toCommSemiring (ZMod p) (ZMod.commRing p)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (by
  decide)) (by
  decide +kernel)

-- Set.subset_union_of_subset_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_union_of_subset_left.h3 : ¬∀ {α : Type} {s t : Set α} (u : Set α), s ⊆ t ∪ u := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true})) (by
  simp)

-- Int.modEq_and_modEq_iff_modEq_mul, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.modEq_and_modEq_iff_modEq_mul.h4 : ¬∀ {a b m n : ℤ}, a ≡ b [ZMOD m] ∧ a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD m * n] := fun hc_h => absurd (@hc_h (0) (2) (2) (2)) (by
  decide +kernel)

-- Int.ModEq.mul_right', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.mul_right'.h4 : ¬∀ {n a b c : ℤ}, a * c ≡ b * c [ZMOD n * c] := fun hc_h => absurd (@hc_h (0) (0) (1) (1)) (by
  decide +kernel)

-- Subtype.coe_eq_of_eq_mk, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.coe_eq_of_eq_mk.h4 : ¬∀ {α : Type} {p : α → Prop} {a : { a : α // p a }} {b : α}, ↑a = b := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : { a : ℕ // (fun (n : ℕ) => n = 0) a })) (1)) (by
  decide +kernel)

-- pow_zmod_val_inv_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.pow_zmod_val_inv_pow.h3 : Not
      (∀ {α : Type} [inst : Group α] {n : Nat} (a : α),
        @Eq α
          (@HPow.hPow α Nat α
            (@instHPow α Nat (@NPow.toPow α (@Monoid.toNPow α (@DivInvMonoid.toMonoid α (@Group.toDivInvMonoid α inst)))))
            (@HPow.hPow α Nat α
              (@instHPow α Nat (@NPow.toPow α (@Monoid.toNPow α (@DivInvMonoid.toMonoid α (@Group.toDivInvMonoid α inst)))))
              a
              (@ZMod.val (Nat.card α)
                (@Inv.inv (ZMod (Nat.card α)) (ZMod.instInv (Nat.card α))
                  (@Nat.cast (ZMod (Nat.card α))
                    (@AddMonoidWithOne.toNatCast (ZMod (Nat.card α))
                      (@AddGroupWithOne.toAddMonoidWithOne (ZMod (Nat.card α))
                        (@Ring.toAddGroupWithOne (ZMod (Nat.card α))
                          (@CommRing.toRing (ZMod (Nat.card α)) (ZMod.commRing (Nat.card α))))))
                    n))))
            n)
          a) := fun hc_h => absurd (@hc_h (QuaternionGroup (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@QuaternionGroup.instGroup (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@QuaternionGroup.xa (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@OfNat.ofNat
        (ZMod
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (nat_lit 0)
        (@Zero.toOfNat0
          (ZMod
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@MulZeroClass.toZero
            (ZMod
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@instMulZeroClassOfSemiring
              (ZMod
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@CommSemiring.toSemiring
                (ZMod
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@CommRing.toCommSemiring
                  (ZMod
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (ZMod.commRing
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))) (by
  decide +kernel)

-- pow_pow_zmod_val_inv, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.pow_pow_zmod_val_inv.h3 : Not
      (∀ {α : Type} [inst : Group α] {n : Nat} (a : α),
        @Eq α
          (@HPow.hPow α Nat α
            (@instHPow α Nat (@NPow.toPow α (@Monoid.toNPow α (@DivInvMonoid.toMonoid α (@Group.toDivInvMonoid α inst)))))
            (@HPow.hPow α Nat α
              (@instHPow α Nat (@NPow.toPow α (@Monoid.toNPow α (@DivInvMonoid.toMonoid α (@Group.toDivInvMonoid α inst)))))
              a n)
            (@ZMod.val (Nat.card α)
              (@Inv.inv (ZMod (Nat.card α)) (ZMod.instInv (Nat.card α))
                (@Nat.cast (ZMod (Nat.card α))
                  (@AddMonoidWithOne.toNatCast (ZMod (Nat.card α))
                    (@AddGroupWithOne.toAddMonoidWithOne (ZMod (Nat.card α))
                      (@Ring.toAddGroupWithOne (ZMod (Nat.card α))
                        (@CommRing.toRing (ZMod (Nat.card α)) (ZMod.commRing (Nat.card α))))))
                  n))))
          a) := fun hc_h => absurd (@hc_h (QuaternionGroup (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@QuaternionGroup.instGroup (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@QuaternionGroup.xa (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@OfNat.ofNat
        (ZMod
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (nat_lit 0)
        (@Zero.toOfNat0
          (ZMod
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@MulZeroClass.toZero
            (ZMod
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@instMulZeroClassOfSemiring
              (ZMod
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@CommSemiring.toSemiring
                (ZMod
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@CommRing.toCommSemiring
                  (ZMod
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (ZMod.commRing
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))) (by
  (simp <;> decide))

-- Nat.ofDigits_zmodeq', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofDigits_zmodeq'.h3 : ¬∀ (b b' : ℤ) (k : ℕ) (L : List ℕ), Nat.ofDigits b L ≡ Nat.ofDigits b' L [ZMOD ↑k] := fun hc_h => absurd (@hc_h (0) (1) (0) ([0, 1])) (by
  decide +kernel)

-- Nat.shiftLeft'_sub, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.shiftLeft'_sub.h4 : ¬∀ (b : Bool) (m : ℕ) {n k : ℕ}, Nat.shiftLeft' b m (n - k) = Nat.shiftLeft' b m n >>> k := fun hc_h => absurd (@hc_h (Bool.false) (1) (0) (1)) (by
  decide +kernel)

-- Nat.zmodeq_ofDigits_digits, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.zmodeq_ofDigits_digits.h3 : ¬∀ (b b' : ℕ) (c : ℤ) (n : ℕ), ↑n ≡ Nat.ofDigits c (b'.digits n) [ZMOD ↑b] := fun hc_h => absurd (@hc_h (0) (1) (0) (2)) (by
  decide +kernel)

-- Nat.ofDigits_modEq', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofDigits_modEq'.h3 : ¬∀ (b b' k : ℕ) (L : List ℕ), Nat.ofDigits b L ≡ Nat.ofDigits b' L [MOD k] := fun hc_h => absurd (@hc_h (0) (1) (0) ([0, 1])) (by
  decide +kernel)

-- Nat.mem_digitsAppend_of_mem_digits, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mem_digitsAppend_of_mem_digits.h4 : ¬∀ {b n : ℕ} (l d : ℕ), d ∈ b.digitsAppend l n := fun hc_h => absurd (@hc_h (0) (0) (0) (0)) (by
  decide +kernel)

-- Nat.bit_lt_bit, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bit_lt_bit.h4 : ¬∀ {m n : ℕ} (a b : Bool), Nat.bit a m < Nat.bit b n := fun hc_h => absurd (@hc_h (0) (0) (Bool.false) (Bool.false)) (by
  decide +kernel)

-- List.minimum_anti, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minimum_anti.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l₁ l₂ : List α}, l₂.minimum ≤ l₁.minimum := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([0]) ([])) (by
  decide +kernel)

-- List.minimum_le_of_mem', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minimum_le_of_mem'.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α} {a : α}, l.minimum ≤ ↑a := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([]) (0)) (by
  decide +kernel)

-- List.Perm.maximum_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.maximum_eq.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l l' : List α}, l.maximum = l'.maximum := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([]) ([0])) (by
  decide +kernel)

-- List.Perm.minimum_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.minimum_eq.h4 : ¬∀ {α : Type} [inst : LinearOrder α] {l l' : List α}, l.minimum = l'.minimum := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([]) ([0])) (by
  decide +kernel)

-- Set.fst_image_prod, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.fst_image_prod.h4 : ¬∀ {α β : Type} (s : Set β) {t : Set α}, Prod.fst '' s ×ˢ t = s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Sym2.attachWith_mk, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.attachWith_mk.h4 : ¬∀ {α : Type} {P : α → Prop} (a b x : α), x ∈ s(a, b) → P x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (0) (1)) (by
  simp)

-- Set.exists_ne_mem_inter_of_not_pairwiseDisjoint, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_ne_mem_inter_of_not_pairwiseDisjoint.h4 : ¬∀ {α ι : Type} {s : Set ι} {f : ι → Set α}, ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ ∃ (x : α), x ∈ f i ∩ f j := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun (a : ℕ) => {n : ℕ | n = 0})) (by
  simp)

-- Set.union_subset_union_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.union_subset_union_right.h4 : ¬∀ {α : Type} {t₁ t₂ : Set α} (s : Set α), s ∪ t₁ ⊆ s ∪ t₂ := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.false}) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.true})) (by
  simp)

-- Decidable.List.Lex.ne_iff, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Decidable.List.Lex.ne_iff.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l₁ l₂ : List α}, List.Lex (fun (x1 x2 : α) => x1 ≠ x2) l₁ l₂ ↔ l₁ ≠ l₂ := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([])) (by
  decide +kernel)

-- List.right_mem_of_mk_mem_sym2, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.right_mem_of_mk_mem_sym2.h4 : ¬∀ {α : Type} {xs : List α} {a : α} {b : α}, b ∈ xs := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (0)) (by
  decide +kernel)

-- List.left_mem_of_mk_mem_sym2, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.left_mem_of_mk_mem_sym2.h4 : ¬∀ {α : Type} {xs : List α} {a : α} {b : α}, a ∈ xs := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (0)) (by
  decide +kernel)

-- Set.restrict₂_def, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.restrict₂_def.h4 : ¬∀ {α : Type} {π : α → Type} {s t : Set α}, s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Set.prod_surjOn_fst, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.prod_surjOn_fst.h4 : ¬∀ {β₁ β₂ : Type} {t₁ : Set β₁} {t₂ : Set β₂}, Set.SurjOn Prod.fst (t₁ ×ˢ t₂) t₁ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- List.IsChain.iff_of_mem_tail_imp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.iff_of_mem_tail_imp.h4 : ¬∀ {α : Type} {R S : α → α → Prop} {l : List α}, List.IsChain R l ↔ List.IsChain S l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a = b : ℕ → ℕ → Prop) ([0, 1])) (by
  decide +kernel)

-- List.subperm.of_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.subperm.of_cons.h4 : ¬∀ {α : Type} (a : α) {l₁ l₂ : List α}, l₁.Subperm l₂ := fun hc_h => absurd (@hc_h (ℕ) (0) ([0]) ([])) (by
  decide +kernel)

-- List.isChain_replicate_of_rel, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isChain_replicate_of_rel.h4 : ¬∀ {α : Type} {r : α → α → Prop} (n : ℕ) {a : α}, List.IsChain r (List.replicate n a) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (2) (0)) (by
  decide +kernel)

-- List.subperm.cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.subperm.cons.h4 : ¬∀ {α : Type} (a : α) {l₁ l₂ : List α}, (a :: l₁).Subperm (a :: l₂) := fun hc_h => absurd (@hc_h (ℕ) (0) ([0]) ([])) (by
  decide +kernel)

-- Set.restrict₂_comp_restrict, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.restrict₂_comp_restrict.h4 : ¬∀ {α : Type} {π : α → Type} {s t : Set α}, s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- List.IsChain.right_of_append, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.right_of_append.h4 : ¬∀ {α : Type} {R : α → α → Prop} {l₁ : List α} {l₂ : List α}, List.IsChain R l₂ := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([]) ([1, 0])) (by
  decide +kernel)

-- Set.prod_surjOn_snd, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.prod_surjOn_snd.h4 : ¬∀ {β₁ β₂ : Type} {t₁ : Set β₁} {t₂ : Set β₂}, Set.SurjOn Prod.snd (t₁ ×ˢ t₂) t₂ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- Set.surjective_codRestrict, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.surjective_codRestrict.h4 : ¬∀ {α ι : Type} {f : ι → α} {s : Set α} (x : ι), f x ∈ s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Finset.noncommSum_empty, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finset.noncommSum_empty.h4.der.{u_3, u_4} : ∀ {α : Type u_3} {β : Type u_4} [inst : AddMonoid β] (f : α → β),
      @Set.Pairwise α
        (@SetLike.coe (Finset α) α (@Finset.instSetLike α)
          (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α)))
        (@Function.onFun α β Prop
          (@AddCommute β (@AddZero.toAdd β (@AddZeroClass.toAddZero β (@AddMonoid.toAddZeroClass β inst)))) f) := by
  (intros; simp; done)
theorem HypCheckProof.Finset.noncommSum_empty.h4.{u_3, u_4} : ∀ {α : Type u_3} {β : Type u_4} [inst : AddMonoid β] (f : α → β),
      @Eq β
        (@Finset.noncommSum α β inst (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α)) f
          (@HypCheckProof.Finset.noncommSum_empty.h4.der α β inst f))
        (@OfNat.ofNat β (nat_lit 0)
          (@Zero.toOfNat0 β (@AddZero.toZero β (@AddZeroClass.toAddZero β (@AddMonoid.toAddZeroClass β inst))))) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Finset.noncommSum_empty hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.Finset.noncommSum_empty.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- Set.mem_union_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_union_right.h4 : ¬∀ {α : Type} {x : α} {b : Set α} (a : Set α), x ∈ a ∪ b := fun hc_h => absurd (@hc_h (ℕ) (1) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  decide +kernel)

-- List.IsChain.drop, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.drop.h3 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} (n : ℕ), List.IsChain R (List.drop n l) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([1, 0]) (0)) (by
  decide +kernel)

-- Bool.decide_congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.decide_congr.h4 : ¬∀ {p q : Prop} [inst : Decidable p] [inst_1 : Decidable q], Decidable.decide p = Decidable.decide q := fun hc_h => absurd (@hc_h (True) (False) (instDecidableTrue) (instDecidableFalse)) (by
  decide +kernel)

-- List.getElem?_rotate, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem?_rotate.h4 : ¬∀ {α : Type} {l : List α} {n m : ℕ}, (l.rotate n)[m]? = l[(m + n) % l.length]? := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (1)) (by
  decide +kernel)

-- List.getElem_rotate, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_rotate.h4 : ¬∀ {α : Type} (l : List α) (n k : ℕ), k < (l.rotate n).length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (0)) (by
  decide +kernel)

-- Multiset.noncommFoldr_empty, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Multiset.noncommFoldr_empty.h3.der.{u_3, u_4} : ∀ {α : Type u_3} {β : Type u_4} (f : α → β → β) (b : β),
      @Set.Pairwise α
        (@Set.ofPred α fun (x : α) =>
          @Membership.mem α (Multiset α) (@Multiset.instMembership α)
            (@OfNat.ofNat (Multiset α) (nat_lit 0) (@Zero.toOfNat0 (Multiset α) (@Multiset.instZero α))) x)
        fun (x y : α) => ∀ (b : β), @Eq β (f x (f y b)) (f y (f x b)) := by
  (intros; simp; done)
theorem HypCheckProof.Multiset.noncommFoldr_empty.h3.{u_3, u_4} : ∀ {α : Type u_3} {β : Type u_4} (f : α → β → β) (b : β),
      @Eq β
        (@Multiset.noncommFoldr α β f
          (@OfNat.ofNat (Multiset α) (nat_lit 0) (@Zero.toOfNat0 (Multiset α) (@Multiset.instZero α)))
          (@HypCheckProof.Multiset.noncommFoldr_empty.h3.der α β f b) b)
        b := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @Multiset.noncommFoldr_empty hc_x0 hc_x1 hc_x2 (@HypCheckProof.Multiset.noncommFoldr_empty.h3.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x3

-- List.IsRotated.mem_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsRotated.mem_iff.h3 : ¬∀ {α : Type} {l l' : List α} {a : α}, a ∈ l ↔ a ∈ l' := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0]) (0)) (by
  decide +kernel)

-- List.getElem_eq_getElem_rotate, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_eq_getElem_rotate.h4 : ¬∀ {α : Type} (l : List α) (n k : ℕ), k < l.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (0)) (by
  decide +kernel)

-- Nat.exists_of_count_lt_count, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_of_count_lt_count.h4 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {a b : ℕ}, ∃ x ∈ Set.Ico a b, p x := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0) (0)) (by
  simp)

-- Nat.lt_of_count_lt_count, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_of_count_lt_count.h4 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {a b : ℕ}, a < b := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0) (0)) (by
  decide +kernel)

-- Function.Periodic.map_mod_nat, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Periodic.map_mod_nat.h3 : ¬∀ {α : Type} {f : ℕ → α} {a : ℕ} (n : ℕ), f (n % a) = f n := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (1) (1)) (by
  decide +kernel)

-- Nat.filter_multiset_Ico_card_eq_of_periodic, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.filter_multiset_Ico_card_eq_of_periodic.h4 : ¬∀ (n a : ℕ) (p : ℕ → Prop) [inst : DecidablePred p], (Multiset.filter p (Multiset.Ico n (n + a))).card = Nat.count p a := fun hc_h => absurd (@hc_h (1) (1) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0)) (by
  decide +kernel)

-- Set.mem_of_mem_coe, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_of_mem_coe.h4 : Not
      (∀ {α : Type} {β : Set α} {γ : Set (@Set.Elem α β)} {a : α},
        @Membership.mem α (Set α) (@Set.instMembership α)
          (@Bind.bind Set (@Monad.toBind Set (@AlternativeMonad.toMonad Set Set.monad)) (@Set.Elem α β) α γ
            fun (a : @Set.Elem α β) =>
            @Pure.pure Set (@Applicative.toPure Set (@Monad.toApplicative Set (@AlternativeMonad.toMonad Set Set.monad))) α
              (@Subtype.val α (fun (x : α) => @Membership.mem α (Set α) (@Set.instMembership α) β x) a))
          a) := fun hc_h => absurd (@hc_h (Nat) (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@EmptyCollection.emptyCollection
      (Set
        (@Set.Elem Nat
          (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@Set.instEmptyCollection
        (@Set.Elem Nat
          (@Set.ofPred Nat fun (n : Nat) => @Eq Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  norm_num)

-- Set.mem_of_mem_image_val, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_of_mem_image_val.h4 : ¬∀ {α : Type} {β : Set α} {γ : Set ↑β} {a : α}, a ∈ Subtype.val '' γ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (∅) (0)) (by
  simp)

-- Set.image_val_mono, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_val_mono.h4 : ¬∀ {α : Type} {A : Set α} {D E : Set ↑A}, Subtype.val '' D ⊆ Subtype.val '' E := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (⊤) (∅)) (by
  norm_num)

-- Set.domRestrict₂_def, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.domRestrict₂_def.h4 : ¬∀ {α : Type} {π : α → Type} {s t : Set α}, s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- List.find?_congr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.find?_congr.h4 : ¬∀ {α : Type} {p₁ p₂ : α → Bool} {l : List α}, List.find? p₁ l = List.find? p₂ l := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) (fun _ => true : ℕ → Bool) ([1])) (by
  decide +kernel)

-- Set.domRestrict₂_comp_domRestrict, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.domRestrict₂_comp_domRestrict.h4 : ¬∀ {α : Type} {π : α → Type} {s t : Set α}, s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) (fun (a : ℕ) => ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- List.Nodup.of_map, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.of_map.h4 : ¬∀ {α β : Type} (f : α → β) {l : List α}, l.Nodup := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ([0, 0])) (by
  decide +kernel)

-- List.Nodup.inter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.inter.h4 : ¬∀ {α : Type} {l₁ : List α} [inst : BEq α] (l₂ : List α), (l₁ ∩ l₂).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (instBEqOfDecidableEq) ([0])) (by
  decide +kernel)

-- Set.image_compl_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_compl_subset.h4 : ¬∀ {α β : Type} {f : α → β} {s : Set α}, f '' sᶜ ⊆ (f '' s)ᶜ := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun _ => true : ℕ → Bool) ({n : ℕ | n = 0})) (by
  simp)

-- Set.mem_of_mem_inter_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_of_mem_inter_left.h4 : ¬∀ {α : Type} {x : α} {a : Set α} {b : Set α}, x ∈ a := fun hc_h => absurd (@hc_h (ℕ) (1) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  decide +kernel)

-- Fin.castLE_inj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castLE_inj.h2 : ¬∀ {n m : ℕ} {a b : Fin m}, m ≤ n := fun hc_h => absurd (@hc_h (0) (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Part.div_get_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.div_get_eq.h4 : ¬∀ {α : Type} [inst : Div α] (a b : Part α), (a / b).Dom := fun hc_h => absurd (@hc_h (ℕ) (Nat.instDiv) (0) (⊥)) (by
  nofun)

-- Part.inter_get_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.inter_get_eq.h4 : ¬∀ {α : Type} [inst : Inter α] (a b : Part α), (a ∩ b).Dom := fun hc_h => absurd (@hc_h (Lean.NameSet) (Lean.NameSet.instInter_batteries) (⊥) (⊥)) (by
  nofun)

-- Part.inv_mem_inv, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.inv_mem_inv.h4 : ¬∀ {α : Type} [inst : Inv α] (a : Part α) (ma : α), ma⁻¹ ∈ a⁻¹ := fun hc_h => absurd (@hc_h (Unit) (PUnit.instInv_mathlib) (⊥) (PUnit.unit)) (by
  nofun)

-- Part.left_dom_of_div_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.left_dom_of_div_dom.h4 : ¬∀ {α : Type} [inst : Div α] {a : Part α} {b : Part α}, a.Dom := fun hc_h => absurd (@hc_h (ℕ) (Nat.instDiv) (⊥) (0)) (by
  nofun)

-- Part.left_dom_of_inter_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.left_dom_of_inter_dom.h4 : ¬∀ {α : Type} [inst : Inter α] {a : Part α} {b : Part α}, a.Dom := fun hc_h => absurd (@hc_h (Lean.NameSet) (Lean.NameSet.instInter_batteries) (⊥) (⊥)) (by
  nofun)

-- Part.right_dom_of_mul_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.right_dom_of_mul_dom.h4 : ¬∀ {α : Type} [inst : Mul α] {a : Part α} {b : Part α}, b.Dom := fun hc_h => absurd (@hc_h (ℕ) (instMulNat) (0) (⊥)) (by
  nofun)

-- List.Subset.dedup_append_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subset.dedup_append_left.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {s t : List α}, (s ++ t).dedup.Perm s.dedup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) ([0])) (by
  decide +kernel)

-- Part.right_dom_of_sub_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.right_dom_of_sub_dom.h4 : ¬∀ {α : Type} [inst : Sub α] {a : Part α} {b : Part α}, b.Dom := fun hc_h => absurd (@hc_h (ℕ) (instSubNat) (0) (⊥)) (by
  nofun)

-- Part.left_dom_of_add_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.left_dom_of_add_dom.h4 : ¬∀ {α : Type} [inst : Add α] {a : Part α} {b : Part α}, a.Dom := fun hc_h => absurd (@hc_h (ℕ) (instAddNat) (⊥) (0)) (by
  nofun)

-- Part.left_dom_of_mod_dom, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.left_dom_of_mod_dom.h4 : ¬∀ {α : Type} [inst : Mod α] {a : Part α} {b : Part α}, a.Dom := fun hc_h => absurd (@hc_h (ℕ) (Nat.instMod) (⊥) (0)) (by
  nofun)

-- Fintype.card_congr', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_congr'.h4 : ¬∀ {α β : Type} [inst : Fintype α] [inst_1 : Fintype β], Fintype.card α = Fintype.card β := fun hc_h => absurd (@hc_h (Bool) (Fin 3) (Bool.fintype) (Fin.fintype 3)) (by
  decide +kernel)

-- Function.Injective.preimage_image, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.preimage_image.h3 : ¬∀ {α β : Type} {f : α → β} (s : Set α), f ⁻¹' f '' s = s := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ => 0 : Bool → ℕ) ({b : Bool | b = Bool.true})) (by
  simp)

-- Fin.val_eq_val_of_heq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_eq_val_of_heq.h4 : Not (∀ {k l : Nat} {i : Fin k} {j : Fin l}, @Eq Nat (@Fin.val k i) (@Fin.val l j)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- List.pairwise_replicate_of_refl, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwise_replicate_of_refl.h4 : ¬∀ {α : Type} {R : α → α → Prop} {a : α} {n : ℕ}, List.Pairwise R (List.replicate n a) := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (2)) (by
  decide +kernel)

-- List.destutter_of_isChain, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.destutter_of_isChain.h4 : ¬∀ {α : Type} (R : α → α → Prop) [inst : DecidableRel R] (l : List α), List.destutter R l = l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) ([1, 0])) (by
  decide +kernel)

-- List.Pairwise.decide, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.decide.h4 : ¬∀ {α : Type} {R : α → α → Prop} [inst : DecidableRel R] (l : List α),
        List.Pairwise (fun (a b : α) => Decidable.decide (R a b) = Bool.true) l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (Nat.decLt) ([1, 0])) (by
  decide +kernel)

-- List.Duplicate.duplicate_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Duplicate.duplicate_cons.h3 : ¬∀ {α : Type} {l : List α} {x : α} (y : α), List.Duplicate x (y :: l) := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (0)) (by
  decide +kernel)

-- List.Duplicate.ne_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Duplicate.ne_singleton.h3 : ¬∀ {α : Type} {l : List α} {x : α} (y : α), l ≠ [y] := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (0)) (by
  decide +kernel)

-- List.duplicate_cons_iff_of_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.duplicate_cons_iff_of_ne.h4 : ¬∀ {α : Type} {l : List α} {x y : α}, List.Duplicate x (y :: l) ↔ List.Duplicate x l := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0) (0)) (by
  decide +kernel)

-- Tuple.antitone_pair_of_not_sorted, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Tuple.antitone_pair_of_not_sorted.h4 : ¬∀ {n : ℕ} {α : Type} [inst : LinearOrder α] {f : Fin n → α}, ∃ (i : Fin n) (j : Fin n), i < j ∧ f j < f i := fun hc_h => absurd (@hc_h (0) (ℕ) (Nat.instLinearOrder) (fun (a : Fin 0) => 0)) (by
  decide +kernel)

-- List.SortedGE.antitone, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGE.antitone.h4 : ¬∀ {α : Type} [inst : Preorder α] {n : ℕ} {f : Fin n → α}, Antitone f := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (2) (fun (a : Fin 2) => if a = (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2) then 0 else 1)) (by
  decide +kernel)

-- Nat.ModEq.of_mul_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.of_mul_right.h4 : ¬∀ {n a b : ℕ} (m : ℕ), a ≡ b [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- Nat.ModEq.of_mul_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.of_mul_left.h4 : ¬∀ {n a b : ℕ} (m : ℕ), a ≡ b [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (0)) (by
  decide +kernel)

-- PNat.Coprime.pow, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.pow.h4 : Not
      (∀ {m n : PNat} (k l : Nat),
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) (↑m) k).Coprime
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) (↑n) l)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat PNat (nat_lit 2)
      (@instOfNatPNatOfNeZeroNat (nat_lit 2)
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) (@OfNat.ofNat PNat (nat_lit 2)
      (@instOfNatPNatOfNeZeroNat (nat_lit 2)
        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Multiset.foldl_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.foldl_zero.h3 : ¬∀ {α β : Type} (f : β → α → β) (b : β), RightCommutative f := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun (a : Bool) (n : ℕ) => n % 2 == 0) (Bool.false)) (by
  exact fun hc_c =>
    absurd (hc_c.right_comm (Bool.false : Bool) (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.ModEq.mul_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.mul_left.h4 : ¬∀ {n a b : ℕ} (c : ℕ), c * a ≡ c * b [MOD n] := fun hc_h => absurd (@hc_h (0) (0) (1) (1)) (by
  decide +kernel)

-- Nat.modEq_and_modEq_iff_modEq_mul, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.modEq_and_modEq_iff_modEq_mul.h4 : ¬∀ {a b m n : ℕ}, a ≡ b [MOD m] ∧ a ≡ b [MOD n] ↔ a ≡ b [MOD m * n] := fun hc_h => absurd (@hc_h (0) (2) (2) (2)) (by
  decide +kernel)

-- Set.mem_or_mem_of_mem_union, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_or_mem_of_mem_union.h4 : ¬∀ {α : Type} {x : α} {a b : Set α}, x ∈ a ∨ x ∈ b := fun hc_h => absurd (@hc_h (ℕ) (1) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  decide +kernel)

-- List.Subset.inter_eq_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subset.inter_eq_left.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {xs ys : List α}, xs ∩ ys = xs := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([])) (by
  decide +kernel)

-- List.Nodup.bagInter_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.bagInter_left.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : DecidableEq α], (l₁.bagInter l₂).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) ([0, 0]) (instDecidableEqNat)) (by
  decide +kernel)

-- PosNum.cast_inj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PosNum.cast_inj.h2 : Not
      (∀ {α : Type} [inst : AddMonoidWithOne α] {m n : PosNum},
        Iff
          (@Eq α
            (@castPosNum α (@AddMonoidWithOne.toOne α inst)
              (@AddSemigroup.toAdd α (@AddMonoid.toAddSemigroup α (@AddMonoidWithOne.toAddMonoid α inst))) m)
            (@castPosNum α (@AddMonoidWithOne.toOne α inst)
              (@AddSemigroup.toAdd α (@AddMonoid.toAddSemigroup α (@AddMonoidWithOne.toAddMonoid α inst))) n))
          (@Eq PosNum m n)) := fun hc_h => absurd (@hc_h (Bool) (@AddGroupWithOne.toAddMonoidWithOne Bool (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool))) (PosNum.one) (PosNum.one.bit1)) (by
  decide +kernel)

-- Prod.instReflLex_mathlib, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.instReflLex_mathlib.h4 : ¬∀ {α β : Type} {r : α → α → Prop} {s : β → β → Prop}, Std.Refl (Prod.Lex r s) := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  exact fun hc_c =>
    absurd (hc_c.refl ((0, 0) : ℕ × ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Function.Surjective.surjOn_preimage, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.surjOn_preimage.h4 : ¬∀ {α β : Type} {t : Set β} {f : α → β}, Set.SurjOn f (f ⁻¹' t) t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({n : ℕ | n = 0}) (fun n => n + 1 : ℕ → ℕ)) (by
  simp)

-- Monotone.sortedLE_ofFn, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Monotone.sortedLE_ofFn.h4 : ¬∀ {α : Type} [inst : Preorder α] {n : ℕ} {f : Fin n → α}, (List.ofFn f).SortedLE := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (2) (fun (a : Fin 2) => if a = (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2) then 1 else 0)) (by
  decide +kernel)

-- StrictMono.sortedLT_ofFn, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.StrictMono.sortedLT_ofFn.h4 : ¬∀ {α : Type} [inst : Preorder α] {n : ℕ} {f : Fin n → α}, (List.ofFn f).SortedLT := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) (2) (fun (a : Fin 2) => 0)) (by
  decide +kernel)

-- List.getEquivOfForallCountEqOne_apply, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getEquivOfForallCountEqOne_apply.h3 : ¬∀ {α : Type} [inst : DecidableEq α] (l : List α) (i : Fin l.length) (x : α), List.count x l = 1 := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) ([Bool.false]) (0)) (by
  decide +kernel)

-- Set.preimage_image_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.preimage_image_eq.h4 : ¬∀ {α β : Type} {f : α → β} (s : Set α), f ⁻¹' f '' s = s := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun _ => 0 : Bool → ℕ) ({b : Bool | b = Bool.true})) (by
  simp)

-- List.sublist_of_orderEmbedding_getElem?_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sublist_of_orderEmbedding_getElem?_eq.h4 : ¬∀ {α : Type} {l l' : List α} (f : ℕ ↪o ℕ), l.Sublist l' := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (1)) (by
  decide +kernel)

-- Fin.Embedding.tail_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.Embedding.tail_cons.h4 : ¬∀ {α : Type} {n : ℕ} (x : Fin n ↪ α) {a : α}, a ∉ Set.range ⇑x := fun hc_h => absurd (@hc_h (ℕ) (1) ({ toFun := fun (a : Fin 1) => 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Fin 1 ↪ ℕ }) (0)) (by
  decide +kernel)

-- Fin.Embedding.snoc_last, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.Embedding.snoc_last.h4 : ¬∀ {α : Type} {n : ℕ} {x : Fin n ↪ α} {a : α}, a ∉ Set.range ⇑x := fun hc_h => absurd (@hc_h (ℕ) (1) ({ toFun := fun (a : Fin 1) => 0, inj' := of_decide_eq_true (id (Eq.refl Bool.true)) : Fin 1 ↪ ℕ }) (0)) (by
  decide +kernel)

-- Fin.ofFn_take_eq_take_ofFn, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.ofFn_take_eq_take_ofFn.h3 : ¬∀ {n : ℕ} {α : Type} {m : ℕ} (v : Fin n → α), m ≤ n := fun hc_h => absurd (@hc_h (0) (ℕ) (1) (fun (a : Fin 0) => 0)) (by
  decide +kernel)

-- List.Subset.dedup_append_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subset.dedup_append_right.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {xs ys : List α}, (xs ++ ys).dedup = ys.dedup := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0]) ([])) (by
  decide +kernel)

-- Commute.ofNat_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Commute.ofNat_right.h4 : ¬∀ {α : Type} [inst : NonAssocSemiring α] (x : α) (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (Nat.instNonAssocSemiring) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- DFinsupp.mapRange_id, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.DFinsupp.mapRange_id.h3.der.{u, v₁} : ∀ {ι : Type u} {β₁ : ι → Type v₁} [inst : (i : ι) → Zero (β₁ i)] (g : @DFinsupp ι (fun (i : ι) => β₁ i) inst) (i : ι),
      @Eq (β₁ i) (@id (β₁ i) (@OfNat.ofNat (β₁ i) (nat_lit 0) (@Zero.toOfNat0 (β₁ i) (inst i))))
        (@OfNat.ofNat (β₁ i) (nat_lit 0) (@Zero.toOfNat0 (β₁ i) (inst i))) := by
  (intros; trivial)
theorem HypCheckProof.DFinsupp.mapRange_id.h3.{u, v₁} : ∀ {ι : Type u} {β₁ : ι → Type v₁} [inst : (i : ι) → Zero (β₁ i)] (g : @DFinsupp ι (fun (i : ι) => β₁ i) inst),
      @Eq (@DFinsupp ι (fun (i : ι) => β₁ i) inst)
        (@DFinsupp.mapRange ι β₁ β₁ inst inst (fun (i : ι) => @id (β₁ i))
          (@HypCheckProof.DFinsupp.mapRange_id.h3.der ι β₁ inst g) g)
        g := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @DFinsupp.mapRange_id hc_x0 hc_x1 hc_x2 (@HypCheckProof.DFinsupp.mapRange_id.h3.der hc_x0 hc_x1 hc_x2 hc_x3) hc_x3

-- Int.Ioc_filter_modEq_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.Ioc_filter_modEq_card.h3 : Not
      (∀ (a b : Int) {r : Int} (v : Int),
        @Eq Int
          (@Nat.cast Int instNatCastInt
            (@Finset.card Int ({x ∈ @Finset.Ioc Int Int.instPreorder Int.instLocallyFiniteOrder a b | r.ModEq x v})))
          (@Max.max Int Int.instMax
            (@HSub.hSub Int Int Int (@instHSub Int Int.instSub)
              (@Int.floor Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing
                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                  (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) (@Int.cast Rat Rat.instIntCast b)
                    (@Int.cast Rat Rat.instIntCast v))
                  (@Int.cast Rat Rat.instIntCast r)))
              (@Int.floor Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing
                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                  (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) (@Int.cast Rat Rat.instIntCast a)
                    (@Int.cast Rat Rat.instIntCast v))
                  (@Int.cast Rat Rat.instIntCast r))))
            (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) (by
  decide +kernel)

-- Function.LeftInverse.list_map, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.LeftInverse.list_map.h4 : ¬∀ {α β : Type} {f : α → β} {g : β → α}, Function.LeftInverse (List.map f) (List.map g) := fun hc_h => absurd (@hc_h (ℕ) (Bool) (fun n => n % 2 == 0 : ℕ → Bool) (fun b => if b then 1 else 0 : Bool → ℕ)) (by
  (simp <;> decide))

-- Trunc.lift_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Trunc.lift_mk.h3 : ¬∀ {α β : Type} (f : α → β) (a a b : α), f a = f b := fun hc_h => absurd (@hc_h (Bool) (ℕ) (fun b => if b then 1 else 0 : Bool → ℕ) (Bool.false)) (by
  decide +kernel)

-- List.head!_append, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.head!_append.h4 : ¬∀ {α : Type} [inst : Inhabited α] (t : List α) {s : List α}, (s ++ t).head! = s.head! := fun hc_h => absurd (@hc_h (ℕ) (instInhabitedNat) ([1]) ([])) (by
  decide +kernel)

-- Set.Infinite.of_image, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.of_image.h4 : ¬∀ {α β : Type} (f : α → β) {s : Set α}, s.Infinite := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun n => n + 1 : ℕ → ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Disjoint.inter_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.inter_left.h4 : ¬∀ {α : Type} {s t : Set α} (u : Set α), Disjoint (s ∩ u) t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- List.rtakeWhile_concat_neg, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.rtakeWhile_concat_neg.h4 : ¬∀ {α : Type} (p : α → Bool) (l : List α) (x : α), List.rtakeWhile p (l ++ [x]) = [] := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) ([]) (0)) (by
  decide +kernel)

-- List.mem_rtakeWhile_imp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_rtakeWhile_imp.h4 : ¬∀ {α : Type} {p : α → Bool} {l : List α} {x : α}, p x = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) ([]) (1)) (by
  decide +kernel)

-- Set.image_preimage_eq_of_subset, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image_preimage_eq_of_subset.h4 : ¬∀ {α β : Type} {f : α → β} {s : Set β}, f '' f ⁻¹' s = s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ) ({x : ℕ | True})) (by
  simp)

-- List.left_le_of_mem_range', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.left_le_of_mem_range'.h4 : ¬∀ {a : ℕ} {b s : ℕ} {x : ℕ}, a ≤ x := fun hc_h => absurd (@hc_h (1) (0) (0) (0)) (by
  decide +kernel)

-- Finset.Nonempty.snd, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.Nonempty.snd.h4.{u_1, u_2} : ¬∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : Finset β}, t.Nonempty := by
  (simp_all; done)

-- List.isChain_of_mem_splitBy, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isChain_of_mem_splitBy.h4 : ¬∀ {α : Type} {m : List α} {r : α → α → Bool} {l : List α}, List.IsChain (fun (x y : α) => r x y = Bool.true) m := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (fun a b => a < b : ℕ → ℕ → Bool) ([])) (by
  decide +kernel)

-- List.IsPrefix.drop, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.drop.h3 : ¬∀ {α : Type} {l₁ l₂ : List α} (n : ℕ), List.drop n l₁ <+: List.drop n l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([]) (0)) (by
  decide +kernel)

-- List.splitBy_append, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.splitBy_append.h4 : ¬∀ {α : Type} {r : α → α → Bool} {l m : List α}, List.splitBy r (l ++ m) = List.splitBy r l ++ List.splitBy r m := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Bool) ([0]) ([1])) (by
  decide +kernel)

-- Choose.choose_modEq_choose_mul_prod_range_choose, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.choose_modEq_choose_mul_prod_range_choose.h3 : ¬∀ {n k p : ℕ} (a : ℕ),
        ↑(n.choose k) ≡
          ↑((n / p ^ a).choose (k / p ^ a)) * ↑(∏ i ∈ Finset.range a, (n / p ^ i % p).choose (k / p ^ i % p)) [ZMOD ↑p] := fun hc_h => absurd (@hc_h (4) (2) (4) (1)) (by
  decide +kernel)

-- ENat.biSup_add', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.biSup_add'.h3 : ¬∀ {ι : Type} {a : ℕ∞} {p : ι → Prop} (f : ι → ℕ∞), (⨆ (i : ι), ⨆ (_ : p i), f i) + a = ⨆ (i : ι), ⨆ (_ : p i), f i + a := fun hc_h => absurd (@hc_h (ℕ) (1) (fun _ => False : ℕ → Prop) (fun (a : ℕ) => 0)) (by
  simp)

-- Nat.count_le_iff_le_nth, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_le_iff_le_nth.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {a b : ℕ}, Nat.count p a ≤ b ↔ a ≤ Nat.nth p b := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (1) (0)) (by
  simp)

-- List.mem_head?_append_of_mem_head?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_head?_append_of_mem_head?.h4 : ¬∀ {α : Type} {s t : List α} {x : α}, x ∈ (s ++ t).head? := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) (0)) (by
  decide +kernel)

-- Set.insert_subset_insert, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.insert_subset_insert.h4 : ¬∀ {α : Type} {s t : Set α} {a : α}, Insert.insert a s ⊆ Insert.insert a t := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false}) (Bool.false)) (by
  simp)

-- List.mem_permutationsAux_of_perm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_permutationsAux_of_perm.h4 : ¬∀ {α : Type} {ts is l : List α}, (∃ (is' : List α) (_ : is'.Perm is), l = is' ++ ts) ∨ l ∈ ts.permutationsAux is := fun hc_h => absurd (@hc_h (ℕ) ([]) ([]) ([0])) (by
  simp)

-- List.get_permutations'Aux, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.get_permutations'Aux.h4 : ¬∀ {α : Type} (s : List α) (x : α) (n : ℕ), n < (List.permutations'Aux x s).length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0) (1)) (by
  decide +kernel)

-- Equivalence.quot_mk_eq_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Equivalence.quot_mk_eq_iff.h2 : ¬∀ {α : Type} {r : α → α → Prop} (x y : α), Quot.mk r x = Quot.mk r y ↔ r x y := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) (0) (0)) (by
  simp)

-- List.prev_getLast_cons, hypothesis 4: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.prev_getLast_cons.h4.der.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x : α), x ∈ x :: l := by
  (intros; solve_by_elim)
theorem HypCheckProof.List.prev_getLast_cons.h4.{u_1} : ∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x : α),
      (x :: l).prev x (HypCheckProof.List.prev_getLast_cons.h4.der l x) = (x :: l).getLast (List.cons_ne_nil x l) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @List.prev_getLast_cons hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.List.prev_getLast_cons.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- List.doubleton_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.doubleton_eq.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {x y : α}, {x, y} = [x, y] := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) (0) (0)) (by
  decide +kernel)

-- List.exists_mem_cons_of, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.exists_mem_cons_of.h4 : ¬∀ {α : Type} {p : α → Prop} {a : α} (l : List α), ∃ x ∈ a :: l, p x := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (1) ([])) (by
  decide +kernel)

-- List.next_eq_getElem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.next_eq_getElem.h4 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α} {a : α}, a ∈ l := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([]) (0)) (by
  decide +kernel)

-- Set.mem_insert_of_mem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_insert_of_mem.h4 : ¬∀ {α : Type} {x : α} {s : Set α} (y : α), x ∈ Insert.insert y s := fun hc_h => absurd (@hc_h (ℕ) (1) ({n : ℕ | n = 0}) (0)) (by
  decide +kernel)

-- Set.Subsingleton.injOn, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Subsingleton.injOn.h3 : ¬∀ {α β : Type} {s : Set α} (f : α → β), Set.InjOn f s := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | True}) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Set.image2_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.image2_right.h4 : ¬∀ {α β : Type} {s : Set α} {t : Set β}, Set.image2 (fun (x : α) (y : β) => y) s t = t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- Set.snd_image_prod, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.snd_image_prod.h3 : ¬∀ {α β : Type} {s : Set α} (t : Set β), Prod.snd '' s ×ˢ t = t := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- Set.Nonempty.fst, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.fst.h4 : ¬∀ {α β : Type} {s : Set α} {t : Set β}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- Nat.le_sqrt_of_eq_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_sqrt_of_eq_mul.h3 : ¬∀ {a b c : ℕ}, b ≤ a.sqrt ∨ c ≤ a.sqrt := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- Int.ModEq.eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.eq.h3 : ¬∀ {n a b : ℤ}, a % n = b % n := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- List.toFinset_card_of_nodup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.toFinset_card_of_nodup.h3 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α}, l.toFinset.card = l.length := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0, 0])) (by
  decide +kernel)

-- List.Nodup.length_le_card, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.length_le_card.h3 : ¬∀ {α : Type} [inst : Fintype α] {l : List α}, l.length ≤ Fintype.card α := fun hc_h => absurd (@hc_h (Unit) (PUnit.fintype) ([PUnit.unit, PUnit.unit])) (by
  decide +kernel)

-- Set.Nontrivial.exists_ne, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.exists_ne.h2 : ¬∀ {α : Type} {s : Set α} (z : α), ∃ x ∈ s, x ≠ z := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- Part.eq_get_iff_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.eq_get_iff_mem.h3 : ¬∀ {α : Type} {o : Part α} {a : α}, o.Dom := fun hc_h => absurd (@hc_h (ℕ) (⊥) (0)) (by
  nofun)

-- ENat.map_ofNat, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.map_ofNat.h3 : ¬∀ {α : Type} (f : ℕ → α) (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (ℕ) (fun n => n + 1 : ℕ → ℕ) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENat.add_le_add_iff_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.add_le_add_iff_right.h3 : ¬∀ {m n k : ℕ∞}, n + k ≤ m + k ↔ n ≤ m := fun hc_h => absurd (@hc_h (0) (1) (⊤)) (by
  decide +kernel)

-- List.maximum_ne_bot_of_length_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.maximum_ne_bot_of_length_pos.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α}, l.maximum ≠ ⊥ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([])) (by
  decide +kernel)

-- ENat.WithBot.ofNat_add_cancel, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.WithBot.ofNat_add_cancel.h3 : ¬∀ {a b : WithBot ℕ∞} {c : ℕ}, c.AtLeastTwo := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.inclusion_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inclusion_injective.h3 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Nat.coprime_pow_right_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_pow_right_iff.h1 : ¬∀ {n : ℕ} (a b : ℕ), a.Coprime (b ^ n) ↔ a.Coprime b := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- Nat.dvd_of_lcm_left_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_of_lcm_left_dvd.h3 : ¬∀ {a : ℕ} {b c : ℕ}, b ∣ c := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- List.Duplicate.not_nodup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Duplicate.not_nodup.h3 : ¬∀ {α : Type} {l : List α} {x : α}, ¬l.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- Nat.Dvd.dvd.nat_lcm_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Dvd.dvd.nat_lcm_right.h2 : ¬∀ {a b : ℕ} (c : ℕ), a ∣ b.lcm c := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- List.Duplicate.mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Duplicate.mem.h3 : ¬∀ {α : Type} {l : List α} {x : α}, x ∈ l := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- Nat.coprime_add_iff_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_add_iff_right.h3 : ¬∀ {a b c : ℕ}, a.Coprime (b + c) ↔ a.Coprime c := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- List.SortedGT.isChain, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.isChain.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], List.IsChain (fun (x1 x2 : α) => x1 > x2) l := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- Nat.add_coprime_iff_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_coprime_iff_right.h3 : ¬∀ {a b c : ℕ}, (a + b).Coprime c ↔ b.Coprime c := fun hc_h => absurd (@hc_h (1) (0) (0)) (by
  decide +kernel)

-- List.getElem_range'_1, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_range'_1.h3 : ¬∀ {n m : ℕ} (i : ℕ), i < (List.range' n m).length := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- List.SortedGT.reverse, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.reverse.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.reverse.SortedLT := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.IsRotated.cyclicPermutations, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsRotated.cyclicPermutations.h3 : ¬∀ {α : Type} {l l' : List α}, l.cyclicPermutations ~r l'.cyclicPermutations := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  decide +kernel)

-- List.SortedGT.sortedGE, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.sortedGE.h3 : ¬∀ {α : Type} [inst : Preorder α] {l : List α}, l.SortedGE := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) ([0, 1])) (by
  decide +kernel)

-- List.IsRotated.symm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsRotated.symm.h3 : ¬∀ {α : Type} {l l' : List α}, l' ~r l := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  decide +kernel)

-- List.SortedGT.pairwise, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.pairwise.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], List.Pairwise (fun (x1 x2 : α) => x1 > x2) l := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- Nat.modEq_iff_dvd', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.modEq_iff_dvd'.h3 : ¬∀ {n a b : ℕ}, a ≡ b [MOD n] ↔ n ∣ b - a := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- List.IsRotated.perm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsRotated.perm.h3 : ¬∀ {α : Type} {l l' : List α}, l.Perm l' := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  decide +kernel)

-- PNat.Coprime.gcd_mul_right_cancel, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.gcd_mul_right_cancel.h3 : ¬∀ (m : ℕ+) {n k : ℕ+}, (m * k).gcd n = m.gcd n := fun hc_h => absurd (@hc_h (1) (2) (2)) (by
  decide +kernel)

-- PNat.Coprime.gcd_mul_left_cancel_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.gcd_mul_left_cancel_right.h3 : ¬∀ (m : ℕ+) {n k : ℕ+}, m.gcd (k * n) = m.gcd n := fun hc_h => absurd (@hc_h (2) (1) (2)) (by
  decide +kernel)

-- Nat.add_mod_add_of_le_add_mod, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_mod_add_of_le_add_mod.h3 : ¬∀ {a b c : ℕ}, (a + b) % c + c = a % c + b % c := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- List.IsChain.sortedGE, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.sortedGE.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedGE := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- PNat.Coprime.gcd_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.gcd_mul.h3 : ¬∀ (k : ℕ+) {m n : ℕ+}, k.gcd (m * n) = k.gcd m * k.gcd n := fun hc_h => absurd (@hc_h (2) (2) (2)) (by
  decide +kernel)

-- PNat.Coprime.gcd_mul_left_cancel, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.Coprime.gcd_mul_left_cancel.h3 : ¬∀ (m : ℕ+) {n k : ℕ+}, (k * m).gcd n = m.gcd n := fun hc_h => absurd (@hc_h (1) (2) (2)) (by
  decide +kernel)

-- Int.modEq_of_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.modEq_of_dvd.h3 : ¬∀ {n a b : ℤ}, a ≡ b [ZMOD n] := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- List.IsRotated.reverse, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsRotated.reverse.h3 : ¬∀ {α : Type} {l l' : List α}, l.reverse ~r l'.reverse := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  decide +kernel)

-- Nat.ordCompl_pow_mul_eq_self_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordCompl_pow_mul_eq_self_iff.h3 : ¬∀ (k m : ℕ) {p : ℕ}, p ^ k * m / p ^ (p ^ k * m).factorization p = m ↔ m = 0 ∨ ¬p ∣ m := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- List.sortedLE_of_getElem_le_getElem_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sortedLE_of_getElem_le_getElem_of_le.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedLE := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.SortedGE.pairwise, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGE.pairwise.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], List.Pairwise (fun (x1 x2 : α) => x1 ≥ x2) l := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.SortedLE.isChain, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLE.isChain.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], List.IsChain (fun (x1 x2 : α) => x1 ≤ x2) l := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.SortedLE.monotone_get, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLE.monotone_get.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], Monotone l.get := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.SortedLE.reverse, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLE.reverse.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.reverse.SortedGE := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- Nat.mod_sub_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mod_sub_of_le.h3 : ¬∀ {a b n : ℕ}, a % n - b = (a - b) % n := fun hc_h => absurd (@hc_h (2) (1) (2)) (by
  decide +kernel)

-- List.getElem_cyclicPermutations, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_cyclicPermutations.h3 : ¬∀ {α : Type} (l : List α) (n : ℕ), n < l.cyclicPermutations.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (1)) (by
  decide +kernel)

-- List.Pairwise.sortedGT, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.sortedGT.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedGT := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- Nat.coprime_of_mul_modEq_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_of_mul_modEq_one.h3 : ¬∀ (b : ℕ) {a n : ℕ}, a.Coprime n := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- List.IsRotated.nodup_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsRotated.nodup_iff.h3 : ¬∀ {α : Type} {l l' : List α}, l.Nodup ↔ l'.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0, 0])) (by
  decide +kernel)

-- Nat.count_succ_eq_count, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_succ_eq_count.h3 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {n : ℕ}, Nat.count p (n + 1) = Nat.count p n := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (0)) (by
  decide +kernel)

-- Nat.count_of_forall, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_of_forall.h3 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {n : ℕ}, Nat.count p n = n := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (2)) (by
  decide +kernel)

-- List.coe_maximum_of_length_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.coe_maximum_of_length_pos.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α}, 0 < l.length := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([])) (by
  decide +kernel)

-- Nat.count_of_forall_not, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.count_of_forall_not.h3 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {n : ℕ}, Nat.count p n = 0 := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0) (1)) (by
  decide +kernel)

-- List.take_concat_get', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.take_concat_get'.h3 : ¬∀ {α : Type} (l : List α) (i : ℕ), i < l.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- List.IsChain.sortedGT, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.sortedGT.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedGT := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.head?_rotate, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.head?_rotate.h3 : ¬∀ {α : Type} {l : List α} {n : ℕ}, (l.rotate n).head? = l[n]? := fun hc_h => absurd (@hc_h (ℕ) ([0]) (1)) (by
  decide +kernel)

-- List.sortedLT_range', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sortedLT_range'.h3 : ¬∀ (a b : ℕ) {s : ℕ}, (List.range' a b s).SortedLT := fun hc_h => absurd (@hc_h (0) (2) (0)) (by
  decide +kernel)

-- List.SortedLT.strictMono_get, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.strictMono_get.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], StrictMono l.get := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- Nat.ModEq.dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ModEq.dvd.h3 : Not
      (∀ {n a b : Nat},
        @Dvd.dvd Int Int.instDvd (@Nat.cast Int instNatCastInt n)
          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt b)
            (@Nat.cast Int instNatCastInt a))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- List.Pairwise.sortedLT, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.sortedLT.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedLT := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- Nat.Ico_filter_coprime_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Ico_filter_coprime_le.h3 : ¬∀ {a : ℕ} (k n : ℕ), {x ∈ Finset.Ico k (k + n) | a.Coprime x}.card ≤ a.totient * (n / a + 1) := fun hc_h => absurd (@hc_h (0) (0) (2)) (by
  decide +kernel)

-- Nat.dvd_two_of_totient_le_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_two_of_totient_le_one.h1 : ¬∀ {a : ℕ}, a.totient ≤ 1 → a ∣ 2 := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  decide +kernel)

-- Nat.dvd_two_of_totient_le_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_two_of_totient_le_one.h2 : ¬∀ {a : ℕ}, 0 < a → a ∣ 2 := fun hc_h => absurd (@hc_h (3) (by
  decide)) (by
  decide +kernel)

-- List.Pairwise.sortedGE, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Pairwise.sortedGE.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedGE := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- Nat.add_div_of_dvd_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_div_of_dvd_right.h3 : ¬∀ {a b c : ℕ}, (a + b) / c = a / c + b / c := fun hc_h => absurd (@hc_h (1) (1) (2)) (by
  decide +kernel)

-- Nat.add_mod_of_add_mod_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_mod_of_add_mod_lt.h3 : ¬∀ {a b c : ℕ}, (a + b) % c = a % c + b % c := fun hc_h => absurd (@hc_h (1) (1) (2)) (by
  decide +kernel)

-- List.minimum_of_length_pos_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minimum_of_length_pos_mem.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α}, 0 < l.length := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([])) (by
  decide +kernel)

-- List.SortedLE.of_reverse, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLE.of_reverse.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedGE := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.SortedLT.isChain, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.isChain.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], List.IsChain (fun (x1 x2 : α) => x1 < x2) l := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.SortedLE.of_map_toDual, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLE.of_map_toDual.h3 : ¬∀ {α : Type} [inst : Preorder α] {l : List α}, (List.map (⇑OrderDual.toDual) l).SortedGE := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) ([1, 0])) (by
  decide +kernel)

-- List.SortedLT.reverse, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLT.reverse.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.reverse.SortedGT := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- Set.subset_of_mem_powerset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subset_of_mem_powerset.h3 : ¬∀ {α : Type} {x s : Set α}, x ⊆ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Set.Nontrivial.exists_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.exists_lt.h3 : ¬∀ {α : Type} {s : Set α} [inst : LinearOrder α], ∃ x ∈ s, ∃ y ∈ s, x < y := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (Nat.instLinearOrder)) (by
  simp)

-- List.sortedGT_of_getElem_gt_getElem_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sortedGT_of_getElem_gt_getElem_of_lt.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedGT := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- Set.Sized.empty_mem_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Sized.empty_mem_iff.h3 : ¬∀ {α : Type} {A : Set (Finset α)} {r : ℕ}, ∅ ∈ A ↔ A = {∅} := fun hc_h => absurd (@hc_h (ℕ) (⊤) (0)) (by
  simp)

-- List.SortedGE.antitone_get, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGE.antitone_get.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], Antitone l.get := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.SortedGE.of_map_toDual, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGE.of_map_toDual.h3 : ¬∀ {α : Type} [inst : Preorder α] {l : List α}, (List.map (⇑OrderDual.toDual) l).SortedLE := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) ([0, 1])) (by
  decide +kernel)

-- List.insertIdx_eraseIdx_getElem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.insertIdx_eraseIdx_getElem.h3 : ¬∀ {α : Type} {l : List α} {n : ℕ}, n < l.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- List.SortedGT.of_reverse, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.of_reverse.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.SortedLT := fun hc_h => absurd (@hc_h (ℕ) ([1, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- List.minimum_ne_top_of_length_pos, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.minimum_ne_top_of_length_pos.h3 : ¬∀ {α : Type} [inst : LinearOrder α] {l : List α}, l.minimum ≠ ⊤ := fun hc_h => absurd (@hc_h (ℕ) (Nat.instLinearOrder) ([])) (by
  decide +kernel)

-- LE.le.subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.LE.le.subset.h3 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Set.encard_sdiff_singleton_add_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_sdiff_singleton_add_one.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, (s \ {a}).encard + 1 = s.encard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1)) (by
  norm_num)

-- Set.le_ncard_diff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.le_ncard_diff.h3 : ¬∀ {α : Type} (s t : Set α), t.ncard - s.ncard ≤ (t \ s).ncard := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True}) ({n : ℕ | n = 0})) (by
  simp)

-- Set.encard_diff_singleton_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_diff_singleton_of_mem.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, (s \ {a}).encard = s.encard - 1 := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- Set.eq_of_forall_subset_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_of_forall_subset_iff.h3 : ¬∀ {α : Type} {s t : Set α}, s = t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Set.ncard_le_ncard_sdiff_add_ncard, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_le_ncard_sdiff_add_ncard.h3 : ¬∀ {α : Type} (s t : Set α), s.ncard ≤ (s \ t).ncard + t.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | True})) (by
  simp)

-- Set.Infinite.exists_subset_ncard_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.exists_subset_ncard_eq.h2 : ¬∀ {α : Type} {s : Set α} (k : ℕ), ∃ t ⊆ s, t.Finite ∧ t.ncard = k := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) (1)) (by
  simp)

-- Set.ncard_inter_le_ncard_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_inter_le_ncard_left.h3 : ¬∀ {α : Type} (s t : Set α), (s ∩ t).ncard ≤ s.ncard := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True}) ({n : ℕ | n = 0})) (by
  simp)

-- Function.Injective.encard_range, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.encard_range.h3 : ¬∀ {α β : Type} {f : α → β}, (Set.range f).encard = ENat.card α := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Set.union_ne_univ_of_ncard_add_ncard_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.union_ne_univ_of_ncard_add_ncard_lt.h3 : ¬∀ {α : Type} {s t : Set α}, s ∪ t ≠ Set.univ := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true}) ({b : Bool | b = Bool.false})) (by
  simp)

-- Nat.ascFactorial_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ascFactorial_le.h3 : ¬∀ (k : ℕ) {n m : ℕ}, n.ascFactorial k ≤ m.ascFactorial k := fun hc_h => absurd (@hc_h (1) (1) (0)) (by
  decide +kernel)

-- List.SortedGT.of_map_toDual, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.of_map_toDual.h3 : ¬∀ {α : Type} [inst : Preorder α] {l : List α}, (List.map (⇑OrderDual.toDual) l).SortedLT := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) ([0, 1])) (by
  decide +kernel)

-- List.mem_sublistsLen_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_sublistsLen_self.h3 : ¬∀ {α : Type} {l l' : List α}, l' ∈ List.sublistsLen l'.length l := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  decide +kernel)

-- List.subperm_of_sublists'_subperm_sublists', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.subperm_of_sublists'_subperm_sublists'.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.Subperm l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([])) (by
  decide +kernel)

-- Set.sep_eq_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sep_eq_of_subset.h3 : ¬∀ {α : Type} {s t : Set α}, {x : α | x ∈ t ∧ x ∈ s} = s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- List.SortedGT.nodup, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedGT.nodup.h3 : ¬∀ {α : Type} {l : List α} [inst : Preorder α], l.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (Nat.instPreorder)) (by
  decide +kernel)

-- Int.gcd_eq_one_of_gcd_mul_right_eq_one_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.gcd_eq_one_of_gcd_mul_right_eq_one_right.h3 : ¬∀ {a : ℤ} {m : ℕ} {n : ℕ}, a.gcd ↑n = 1 := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- List.SortedLE.map_toDual, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.SortedLE.map_toDual.h3 : ¬∀ {α : Type} [inst : Preorder α] {l : List α}, l.SortedGE := fun hc_h => absurd (@hc_h (ℕ) (Nat.instPreorder) ([0, 1])) (by
  decide +kernel)

-- List.nodup_sublistsLen, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nodup_sublistsLen.h3 : ¬∀ {α : Type} (n : ℕ) {l : List α}, (List.sublistsLen n l).Nodup := fun hc_h => absurd (@hc_h (ℕ) (1) ([0, 0])) (by
  decide +kernel)

-- List.sublistsLen_of_length_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sublistsLen_of_length_lt.h3 : ¬∀ {α : Type} {n : ℕ} {l : List α}, List.sublistsLen n l = [] := fun hc_h => absurd (@hc_h (ℕ) (0) ([])) (by
  decide +kernel)

-- Function.Surjective.range_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Surjective.range_eq.h3 : ¬∀ {α ι : Type} {f : ι → α}, Set.range f = Set.univ := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Set.le_ncard_sdiff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.le_ncard_sdiff.h3 : ¬∀ {α : Type} (s t : Set α), t.ncard - s.ncard ≤ (t \ s).ncard := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True}) ({n : ℕ | n = 0})) (by
  simp)

-- Set.ncard_insert_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_insert_of_mem.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, (Insert.insert a s).ncard = s.ncard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- Set.ncard_range_of_injective, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_range_of_injective.h3 : ¬∀ {α β : Type} {f : α → β}, (Set.range f).ncard = Nat.card α := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- Nat.factorization_choose_eq_zero_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_choose_eq_zero_of_lt.h3 : ¬∀ {p n k : ℕ}, (n.choose k).factorization p = 0 := fun hc_h => absurd (@hc_h (2) (2) (1)) (by
  decide +kernel)

-- Set.encard_diff_add_encard_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_diff_add_encard_of_subset.h3 : ¬∀ {α : Type} {s t : Set α}, (t \ s).encard + s.encard = t.encard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Set.one_le_ncard_insert, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.one_le_ncard_insert.h3 : ¬∀ {α : Type} (a : α) (s : Set α), 1 ≤ (Insert.insert a s).ncard := fun hc_h => absurd (@hc_h (ℕ) (0) ({x : ℕ | True})) (by
  simp)

-- List.Disjoint.symm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Disjoint.symm.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₂.Disjoint l₁ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([0])) (by
  simp)

-- List.Nodup.of_append_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.of_append_right.h3 : ¬∀ {α : Type} {l₁ : List α} {l₂ : List α}, l₂.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0, 0])) (by
  decide +kernel)

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

-- Multiset.powersetAux_perm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.powersetAux_perm.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, (Multiset.powersetAux l₁).Perm (Multiset.powersetAux l₂) := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  decide +kernel)

-- FinEnum.card_ofList, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.FinEnum.card_ofList.h3 : ¬∀ {α : Type} [inst : DecidableEq α] (xs : List α) (x : α), x ∈ xs := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([])) (by
  simp)

-- Multiset.revzip_powersetAux_perm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Multiset.revzip_powersetAux_perm.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, (Multiset.powersetAux l₁).revzip.Perm (Multiset.powersetAux l₂).revzip := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  decide +kernel)

-- Nat.Prime.emultiplicity_pow, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.emultiplicity_pow.h3 : ¬∀ {p m n : ℕ}, emultiplicity p (m ^ n) = ↑n * emultiplicity p m := fun hc_h => absurd (@hc_h (1) (0) (0)) (by
  simp)

-- Set.exists_ne_of_one_lt_ncard, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.exists_ne_of_one_lt_ncard.h2 : ¬∀ {α : Type} {s : Set α} (a : α), ∃ b ∈ s, b ≠ a := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- List.lookmap_of_forall_not, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lookmap_of_forall_not.h3 : ¬∀ {α : Type} (f : α → Option α) {l : List α}, List.lookmap f l = l := fun hc_h => absurd (@hc_h (ℕ) (fun n => some (n + 1) : ℕ → Option ℕ) ([0])) (by
  decide +kernel)

-- List.lookmap_id', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lookmap_id'.h2 : ¬∀ {α : Type} (f : α → Option α) (l : List α), List.lookmap f l = l := fun hc_h => absurd (@hc_h (ℕ) (fun n => some (n + 1) : ℕ → Option ℕ) ([0])) (by
  decide +kernel)

-- HasSubset.Subset.le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.HasSubset.Subset.le.h3 : ¬∀ {α : Type} {s t : Set α}, s ⊆ t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- NNRat.cast_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNRat.cast_mk.h3 : ¬∀ {K : Type} [inst : DivisionRing K] (q : ℚ), 0 ≤ q := fun hc_h => absurd (@hc_h (ℚ) (Rat.instDivisionRing) (-1)) (by
  decide +kernel)

-- Even.natCast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Even.natCast.h3 : Not
      (∀ {α : Type} [inst : AddMonoidWithOne α] {n : Nat},
        @Even α (@AddSemigroup.toAdd α (@AddMonoid.toAddSemigroup α (@AddMonoidWithOne.toAddMonoid α inst)))
          (@Nat.cast α (@AddMonoidWithOne.toNatCast α inst) n)) := fun hc_h => absurd (@hc_h (Nat) (Nat.instAddMonoidWithOne) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Set.encard_sdiff_add_encard_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_sdiff_add_encard_of_subset.h3 : ¬∀ {α : Type} {s t : Set α}, (t \ s).encard + s.encard = t.encard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Set.encard_diff_singleton_add_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.encard_diff_singleton_add_one.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, (s \ {a}).encard + 1 = s.encard := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1)) (by
  norm_num)

-- Set.Nonempty.not_disjoint, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.not_disjoint.h3 : ¬∀ {α : Type} {s t : Set α}, ¬Disjoint s t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- List.Nodup.filter, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.filter.h3 : ¬∀ {α : Type} (p : α → Bool) {l : List α}, (List.filter p l).Nodup := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) ([0, 0])) (by
  decide +kernel)

-- Nat.dvd_div_of_mul_dvd_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_div_of_mul_dvd_right.h3 : ¬∀ {a b c : ℕ}, a ∣ c / b := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- List.Nodup.disjoint, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.disjoint.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.Disjoint l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([0])) (by
  simp)

-- Odd.intCast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Odd.intCast.h3 : Not
      (∀ {α : Type} [inst : Ring α] {n : Int},
        @Odd α (@Ring.toSemiring α inst) (@Int.cast α (@AddGroupWithOne.toIntCast α (@Ring.toAddGroupWithOne α inst)) n)) := fun hc_h => absurd (@hc_h (Bool) (@BooleanRing.toRing Bool instBooleanRingBool) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  nofun)

-- Quot.factor_mk_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Quot.factor_mk_eq.h3 : ¬∀ {α : Type} (r s : α → α → Prop) (x y : α), r x y → s x y := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a = b : ℕ → ℕ → Prop) (fun a b => a < b : ℕ → ℕ → Prop)) (by
  simp)

-- Int.ModEq.dvd_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ModEq.dvd_iff.h3 : ¬∀ {n a b : ℤ}, n ∣ a ↔ n ∣ b := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- List.Nodup.ne_singleton_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.ne_singleton_iff.h2 : ¬∀ {α : Type} {l : List α} (x : α), l ≠ [x] ↔ l = [] ∨ ∃ y ∈ l, y ≠ x := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) (0)) (by
  decide +kernel)

-- Nat.log_eq_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_eq_iff.h3 : ¬∀ {b m n : ℕ}, Nat.log b n = m ↔ b ^ m ≤ n ∧ n < b ^ (m + 1) := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- Nat.log_mono_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_mono_right.h3 : ¬∀ {b n m : ℕ}, Nat.log b n ≤ Nat.log b m := fun hc_h => absurd (@hc_h (2) (2) (0)) (by
  decide +kernel)

-- Int.cast_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.cast_ne_zero.h2 : Not
      (∀ {α : Type} [inst : AddGroupWithOne α] {n : Int},
        Iff
          (@Ne α (@Int.cast α (@AddGroupWithOne.toIntCast α inst) n)
            (@OfNat.ofNat α (nat_lit 0)
              (@Zero.toOfNat0 α
                (@NegZeroClass.toZero α
                  (@SubNegZeroMonoid.toNegZeroClass α
                    (@SubtractionMonoid.toSubNegZeroMonoid α
                      (@AddGroup.toSubtractionMonoid α (@AddGroupWithOne.toAddGroup α inst))))))))
          (@Ne Int n (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0))))) := fun hc_h => absurd (@hc_h (Bool) (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool)) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))) (by
  decide +kernel)

-- Nat.clog_le_iff_le_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_le_iff_le_pow.h1 : ¬∀ {b x y : ℕ}, Nat.clog b x ≤ y ↔ x ≤ b ^ y := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- Nat.clog_mono_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_mono_right.h3 : ¬∀ (b : ℕ) {n m : ℕ}, Nat.clog b n ≤ Nat.clog b m := fun hc_h => absurd (@hc_h (2) (2) (0)) (by
  decide +kernel)

-- Int.cast_ne_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.cast_ne_one.h2 : Not
      (∀ {α : Type} [inst : AddGroupWithOne α] {n : Int},
        Iff
          (@Ne α (@Int.cast α (@AddGroupWithOne.toIntCast α inst) n)
            (@OfNat.ofNat α (nat_lit 1)
              (@One.toOfNat1 α (@AddMonoidWithOne.toOne α (@AddGroupWithOne.toAddMonoidWithOne α inst)))))
          (@Ne Int n (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) := fun hc_h => absurd (@hc_h (Bool) (@Ring.toAddGroupWithOne Bool (@BooleanRing.toRing Bool instBooleanRingBool)) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) (by
  decide +kernel)

-- Set.nontrivial_iff_exists_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.nontrivial_iff_exists_ne.h3 : ¬∀ {α : Type} {s : Set α} {x : α}, s.Nontrivial ↔ ∃ y ∈ s, y ≠ x := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1)) (by
  simp)

-- Disjoint.inter_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Disjoint.inter_eq.h3 : ¬∀ {α : Type} {s t : Set α}, s ∩ t = ∅ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({n : ℕ | n = 0})) (by
  simp)

-- List.Nodup.of_append_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.of_append_left.h3 : ¬∀ {α : Type} {l₁ : List α} {l₂ : List α}, l₁.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0]) ([])) (by
  decide +kernel)

-- Set.Nonempty.of_diff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.of_diff.h3 : ¬∀ {α : Type} {s : Set α} {t : Set α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- ZMod.cast_one', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.cast_one'.h3 : Not
      (∀ {n : Nat} {R : Type} [inst : Ring R],
        @Eq R
          (@ZMod.cast R (@Ring.toAddGroupWithOne R inst) n
            (@OfNat.ofNat (ZMod n) (nat_lit 1)
              (@One.toOfNat1 (ZMod n)
                (@AddMonoidWithOne.toOne (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))))))
          (@OfNat.ofNat R (nat_lit 1)
            (@One.toOfNat1 R
              (@AddMonoidWithOne.toOne R (@AddGroupWithOne.toAddMonoidWithOne R (@Ring.toAddGroupWithOne R inst)))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (Bool) (@BooleanRing.toRing Bool instBooleanRingBool)) (by
  decide +kernel)

-- Int.Ico_filter_dvd_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.Ico_filter_dvd_eq.h3 : ¬∀ (a b : ℤ) {r : ℤ}, 0 < r := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- Fin.sub_val_lt_sub, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.sub_val_lt_sub.h3 : ¬∀ {n : ℕ} {i j : Fin n}, ↑(j - i) < n - ↑i := fun hc_h => absurd (@hc_h (2) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- List.nodup_iff_count_eq_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nodup_iff_count_eq_one.h3 : ¬∀ {α : Type} {l : List α} [inst : BEq α], l.Nodup ↔ ∀ a ∈ l, List.count a l = 1 := fun hc_h => absurd (@hc_h (ℕ) ([0]) (⟨fun a b => a != b⟩ : BEq ℕ)) (by
  decide +kernel)

-- Fin.castLT_sub_nezero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castLT_sub_nezero.h3 : ¬∀ {n : ℕ} {i j : Fin n}, i < j := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.add_one_le_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.add_one_le_of_lt.h3 : ¬∀ {n : ℕ} {a b : Fin (n + 1)}, a + 1 ≤ b := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Fin.ne_zero_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.ne_zero_of_lt.h3 : ¬∀ {n : ℕ} {a : Fin (n + 1)} {b : Fin (n + 1)}, b ≠ 0 := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.find?_not_eq_head_dropWhile, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.find?_not_eq_head_dropWhile.h3 : ¬∀ {α : Type} {p : α → Bool} {l : List α}, ∃ x ∈ l, ¬p x = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) ([])) (by
  decide +kernel)

-- List.find?_eq_head_dropWhile_not, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.find?_eq_head_dropWhile_not.h3 : ¬∀ {α : Type} {p : α → Bool} {l : List α}, ∃ x ∈ l, p x = Bool.true := fun hc_h => absurd (@hc_h (ℕ) (fun n => n % 2 == 0 : ℕ → Bool) ([])) (by
  decide +kernel)

-- Nat.Prime.pow_eq_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.pow_eq_iff.h3 : ¬∀ {p a k : ℕ}, a ^ k = p ↔ a = p ∧ k = 1 := fun hc_h => absurd (@hc_h (1) (0) (0)) (by
  decide +kernel)

-- Fin.exists_eq_add_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.exists_eq_add_of_le.h3 : ¬∀ {n : ℕ} {a b : Fin n}, ∃ k ≤ b, b = a + k := fun hc_h => absurd (@hc_h (2) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Subtype.coe_eta, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Subtype.coe_eta.h3.der.{u_1} : ∀ {α : Sort u_1} {p : α → Prop} (a : { a : α // p a }), p ↑a := by
  (intros; lia)
theorem HypCheckProof.Subtype.coe_eta.h3.{u_1} : ∀ {α : Sort u_1} {p : α → Prop} (a : { a : α // p a }),
      (⟨↑a, HypCheckProof.Subtype.coe_eta.h3.der a⟩ : { a : α // p a }) = a := by
  intro hc_x0 hc_x1 hc_x2
  exact @Subtype.coe_eta hc_x0 hc_x1 hc_x2 (@HypCheckProof.Subtype.coe_eta.h3.der hc_x0 hc_x1 hc_x2)

-- Fin.succ_castPred_le_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succ_castPred_le_iff.h3 : ¬∀ {n : ℕ} {a : Fin (n + 1)} {b : Fin (n + 1)}, a ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Nat.Prime.dvd_ascFactorial_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_ascFactorial_iff.h3 : ¬∀ {p k n : ℕ}, p ∣ k.ascFactorial n ↔ ∃ i < n, p ∣ k + i := fun hc_h => absurd (@hc_h (1) (0) (0)) (by
  decide +kernel)

-- Fin.predAbove_succ_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_succ_of_lt.h3 : ¬∀ {n : ℕ} (p i : Fin n), i < p := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.toFinset_toList, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.toFinset_toList.h3 : ¬∀ {α : Type} [inst : DecidableEq α] {s : List α}, s.toFinset.toList.Perm s := fun hc_h => absurd (@hc_h (ℕ) (instDecidableEqNat) ([0, 0])) (by
  simp)

-- List.Ico.filter_lt_of_ge, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.filter_lt_of_ge.h3 : ¬∀ {n m l : ℕ}, List.filter (fun (x : ℕ) => Decidable.decide (x < l)) (List.Ico n m) = List.Ico n l := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  decide +kernel)

-- List.Ico.filter_lt_of_le_bot, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.filter_lt_of_le_bot.h3 : ¬∀ {n m l : ℕ}, List.filter (fun (x : ℕ) => Decidable.decide (x < l)) (List.Ico n m) = [] := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- List.Ico.filter_le_of_top_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.filter_le_of_top_le.h3 : ¬∀ {n m l : ℕ}, List.filter (fun (x : ℕ) => Decidable.decide (l ≤ x)) (List.Ico n m) = [] := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- List.Ico.map_sub, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.map_sub.h3 : ¬∀ (n m k : ℕ), List.map (fun (x : ℕ) => x - k) (List.Ico n m) = List.Ico (n - k) (m - k) := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- List.Perm.offDiag, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.offDiag.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.offDiag.Perm l₂.offDiag := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0, 1])) (by
  decide +kernel)

-- Nat.choose_mul, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_mul.h3 : ¬∀ {n k s : ℕ}, n.choose k * k.choose s = n.choose s * (n - s).choose (k - s) := fun hc_h => absurd (@hc_h (1) (0) (1)) (by
  decide +kernel)

-- Int.dvd_div_of_mul_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.dvd_div_of_mul_dvd.h3 : ¬∀ {a b c : ℤ}, b ∣ c / a := fun hc_h => absurd (@hc_h (1) (0) (1)) (by
  decide +kernel)

-- List.HasPeriod.drop_prefix, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.HasPeriod.drop_prefix.h3 : ¬∀ {α : Type} {w : List α} (p : ℕ), List.drop p w <+: w := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (1)) (by
  decide +kernel)

-- List.getLast?_append_of_ne_nil, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getLast?_append_of_ne_nil.h3 : ¬∀ {α : Type} (l₁ : List α) {l₂ : List α}, (l₁ ++ l₂).getLast? = l₂.getLast? := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([])) (by
  decide +kernel)

-- Fin.castSucc_pred_lt_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castSucc_pred_lt_iff.h3 : ¬∀ {n : ℕ} {a : Fin (n + 1)} {b : Fin (n + 1)}, a ≠ 0 := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.hasPeriod_of_length_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.hasPeriod_of_length_le.h3 : ¬∀ {α : Type} (w : List α) (p : ℕ), w.HasPeriod p := fun hc_h => absurd (@hc_h (ℕ) ([0, 1]) (1)) (by
  nofun)

-- List.mem_sections_length, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_sections_length.h3 : ¬∀ {α : Type} {L : List (List α)} {f : List α}, f.length = L.length := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  decide +kernel)

-- List.Nodup.notMem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.notMem.h3 : ¬∀ {α : Type} {l : List α} {a : α}, a ∉ l := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0)) (by
  decide +kernel)

-- EReal.toReal_neg, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toReal_neg.h1 : ¬∀ {x : EReal}, x ≠ ⊥ → x.toReal < 0 := fun hc_h => absurd (@hc_h (0) (by
  decide)) (by
  simp)

-- EReal.toReal_neg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toReal_neg.h2 : ¬∀ {x : EReal}, x < 0 → x.toReal < 0 := fun hc_h => absurd (@hc_h (⊥) (by
  decide)) (by
  simp)

-- List.head_head_splitBy, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.head_head_splitBy.h3 : ¬∀ {α : Type} (r : α → α → Bool) {l : List α}, l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Bool) ([])) (by
  decide +kernel)

-- List.mem_of_mem_dropLast, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_of_mem_dropLast.h3 : ¬∀ {α : Type} {l : List α} {a : α}, a ∈ l := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- List.map_splitLengths_length, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.map_splitLengths_length.h3 : ¬∀ {α : Type} (l : List α) (sz : List ℕ), List.map List.length (sz.splitLengths l) = sz := fun hc_h => absurd (@hc_h (ℕ) ([]) ([1])) (by
  decide +kernel)

-- Fin.predAbove_pred_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_pred_of_lt.h3 : ¬∀ {n : ℕ} (p i : Fin (n + 1)), i < p := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.cons_head!_tail, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_head!_tail.h3 : ¬∀ {α : Type} [inst : Inhabited α] {l : List α}, l.head! :: l.tail = l := fun hc_h => absurd (@hc_h (ℕ) (instInhabitedNat) ([])) (by
  decide +kernel)

-- List.drop_take_succ_eq_cons_getElem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.drop_take_succ_eq_cons_getElem.h3 : ¬∀ {α : Type} (L : List α) (i : ℕ), i < L.length := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- List.prefix_append_drop, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.prefix_append_drop.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₂ = l₁ ++ List.drop l₁.length l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([])) (by
  decide +kernel)

-- EReal.add_le_of_le_sub, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_le_of_le_sub.h3 : ¬∀ {a b c : EReal}, a + c ≤ b := fun hc_h => absurd (@hc_h (0) (0) (1)) (by
  simp)

-- EReal.add_lt_add_right_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_lt_add_right_coe.h2 : ¬∀ {x y : EReal} (z : ℝ), x + ↑z < y + ↑z := fun hc_h => absurd (@hc_h (0) (0) ({ cauchy := 0 : ℝ })) (by
  simp)

-- Set.mem_powerset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.mem_powerset.h3 : ¬∀ {α : Type} {x s : Set α}, x ∈ 𝒫 s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | False})) (by
  simp)

-- Nat.dvd_pow_iff_ceilRoot_dvd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.dvd_pow_iff_ceilRoot_dvd.h3 : ¬∀ {a b n : ℕ}, a ∣ b ^ n ↔ n.ceilRoot a ∣ b := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- Fin.sub_castSucc_eq_castSucc_sub_of_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.sub_castSucc_eq_castSucc_sub_of_le.h3 : ¬∀ {n : ℕ} {a b : Fin n}, a.castSucc - b.castSucc = (a - b).castSucc := fun hc_h => absurd (@hc_h (2) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Int.modEq_iff_eq_of_div_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.modEq_iff_eq_of_div_eq.h3 : ¬∀ {n a b : ℤ}, a ≡ b [ZMOD n] ↔ a = b := fun hc_h => absurd (@hc_h (1) (0) (1)) (by
  decide +kernel)

-- Nat.Prime.dvd_lcm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_lcm.h3 : ¬∀ {p a b : ℕ}, p ∣ a.lcm b ↔ p ∣ a ∨ p ∣ b := fun hc_h => absurd (@hc_h (6) (2) (3)) (by
  decide +kernel)

-- Fin.succAbove_of_castSucc_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_of_castSucc_lt.h3 : ¬∀ {n : ℕ} (p : Fin (n + 1)) (i : Fin n), p.succAbove i = i.castSucc := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Function.Bijective.list_map, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Bijective.list_map.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Bijective (List.map f) := fun hc_h => absurd (@hc_h (Bool) (Bool) (fun _ => true : Bool → Bool)) (by
  simp)

-- Fin.lt_castPred_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.lt_castPred_iff.h3 : ¬∀ {n : ℕ} {j : Fin n} {i : Fin (n + 1)}, i ≠ Fin.last n := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Set.eq_empty_of_ssubset_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_empty_of_ssubset_singleton.h3 : ¬∀ {α : Type} {s : Set α} {x : α}, s = ∅ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- EReal.sub_lt_of_lt_add', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.sub_lt_of_lt_add'.h3 : ¬∀ {a b c : EReal}, a - b < c := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  simp)

-- NNRat.divNat_mul_right, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNRat.divNat_mul_right.h1 : ¬∀ {a : ℕ} (n d : ℕ), NNRat.divNat (n * a) (d * a) = NNRat.divNat n d := fun hc_h => absurd (@hc_h (0) (1) (1)) (by
  decide +kernel)

-- Fin.succAbove_of_le_castSucc, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_of_le_castSucc.h3 : ¬∀ {n : ℕ} (p : Fin (n + 1)) (i : Fin n), p.succAbove i = i.succ := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Nat.nth_le_nth, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_le_nth.h1 : ¬∀ {p : ℕ → Prop} {k n : ℕ}, Nat.nth p k ≤ Nat.nth p n ↔ k ≤ n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (1) (0)) (by
  simp)

-- EReal.add_le_of_forall_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.add_le_of_forall_lt.h3 : ¬∀ {a b c : EReal}, a + b ≤ c := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  simp)

-- Nat.nth_count, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_count.h3 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] {n : ℕ}, Nat.nth p (Nat.count p n) = n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (1)) (by
  simp)

-- NeZero.natCast_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NeZero.natCast_ne.h3 : Not
      (∀ (n : Nat) (R : Type) [inst : AddMonoidWithOne R],
        @Ne R (@Nat.cast R (@AddMonoidWithOne.toNatCast R inst) n)
          (@OfNat.ofNat R (nat_lit 0)
            (@Zero.toOfNat0 R
              (@AddZero.toZero R
                (@AddZeroClass.toAddZero R (@AddMonoid.toAddZeroClass R (@AddMonoidWithOne.toAddMonoid R inst))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Nat) (Nat.instAddMonoidWithOne)) (by
  decide +kernel)

-- Nat.le_nth_count, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_nth_count.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] (n : ℕ), n ≤ Nat.nth p (Nat.count p n) := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (1)) (by
  simp)

-- Fin.succAbove_of_succ_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_of_succ_le.h3 : ¬∀ {n : ℕ} (p : Fin (n + 1)) (i : Fin n), p.succAbove i = i.castSucc := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.pred_one', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.pred_one'.h1 : ¬∀ {n : ℕ}, NeZero n := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fin.pred_one', hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Fin.pred_one'.h2.der : ∀ {n : Nat} [inst : @NeZero Nat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) n],
      @Ne
        (Fin
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@OfNat.ofNat
          (Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (nat_lit 1)
          (@Fin.instOfNat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
            (nat_lit 1)))
        (@OfNat.ofNat
          (Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (nat_lit 0)
          (@Fin.instOfNat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@instNeZeroNatHAdd_1 n (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
            (nat_lit 0))) := by
  (intros; simp; done)
theorem HypCheckProof.Fin.pred_one'.h2 : ∀ {n : Nat} [inst : @NeZero Nat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) n],
      @Eq (Fin n)
        (@Fin.pred n
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
              (nat_lit 1)))
          (@HypCheckProof.Fin.pred_one'.h2.der n inst))
        (@OfNat.ofNat (Fin n) (nat_lit 0) (@Fin.instOfNat n inst (nat_lit 0))) := by
  intro hc_x0 hc_x1
  exact @Fin.pred_one' hc_x0 hc_x1 (@HypCheckProof.Fin.pred_one'.h2.der hc_x0 hc_x1)

-- Subtype.coe_image_of_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Subtype.coe_image_of_subset.h3 : ¬∀ {α : Type} {s t : Set α}, Subtype.val '' {x : ↑s | ↑x ∈ t} = t := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) ({x : ℕ | True})) (by
  norm_num)

-- finCongr_symm_apply, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.finCongr_symm_apply.h2 : ¬∀ {n m : ℕ} (a : Fin m), n = m := fun hc_h => absurd (@hc_h (0) (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.succAbove_of_lt_succ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_of_lt_succ.h3 : ¬∀ {n : ℕ} (p : Fin (n + 1)) (i : Fin n), p.succAbove i = i.succ := fun hc_h => absurd (@hc_h (1) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Finset.eq_of_mem_singleton, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.eq_of_mem_singleton.h3 : ¬∀ {α : Type} {x y : α}, x = y := fun hc_h => absurd (@hc_h (ℕ) (0) (1)) (by
  decide +kernel)

-- Rat.mkRat_add_mkRat_of_den, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Rat.mkRat_add_mkRat_of_den.h3.gneg : ∀ (n₁ n₂ : ℤ) {d : ℕ}, ¬d ≠ 0 → mkRat n₁ d + mkRat n₂ d = mkRat (n₁ + n₂) d := by
  (intros; simp_all; done)
theorem HypCheckProof.Rat.mkRat_add_mkRat_of_den.h3 : ∀ (n₁ n₂ : ℤ) {d : ℕ}, mkRat n₁ d + mkRat n₂ d = mkRat (n₁ + n₂) d := by
  intro hc_x0 hc_x1 hc_x2
  exact Classical.byCases (fun hc_h => @Rat.mkRat_add_mkRat_of_den hc_x0 hc_x1 hc_x2 hc_h) (fun hc_hn => @HypCheckProof.Rat.mkRat_add_mkRat_of_den.h3.gneg hc_x0 hc_x1 hc_x2 hc_hn)

-- List.exists_of_length_succ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.exists_of_length_succ.h3 : ¬∀ {α : Type} {n : ℕ} (l : List α), ∃ (h : α) (t : List α), l = h :: t := fun hc_h => absurd (@hc_h (ℕ) (0) ([])) (by
  simp)

-- Fin.castpred_succ_le_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castpred_succ_le_iff.h3 : ¬∀ {n : ℕ} {a : Fin (n + 1)} {b : Fin (n + 1)}, a.succ ≠ Fin.last (n + 1) := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Set.inter_singleton_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.inter_singleton_of_mem.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, s ∩ {a} = {a} := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (1)) (by
  (simp <;> omega))

-- List.cons_head?_tail, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.cons_head?_tail.h3 : ¬∀ {α : Type} {l : List α} {a : α}, a :: l.tail = l := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- EReal.inv_inv, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.inv_inv.h1 : ¬∀ {a : EReal}, a ≠ ⊤ → a⁻¹⁻¹ = a := fun hc_h => absurd (@hc_h (⊥) (by
  decide)) (by
  decide +kernel)

-- EReal.inv_inv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.inv_inv.h2 : ¬∀ {a : EReal}, a ≠ ⊥ → a⁻¹⁻¹ = a := fun hc_h => absurd (@hc_h (⊤) (by
  decide)) (by
  decide +kernel)

-- List.dropLast_append_getLast?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dropLast_append_getLast?.h3 : ¬∀ {α : Type} {l : List α} (a : α), l.dropLast ++ [a] = l := fun hc_h => absurd (@hc_h (ℕ) ([]) (0)) (by
  decide +kernel)

-- Fin.predAbove_castPred_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_castPred_of_lt.h3 : ¬∀ {n : ℕ} (p i : Fin (n + 1)), p < i := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.lt_castPred_succ_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.lt_castPred_succ_iff.h3 : ¬∀ {n : ℕ} {a : Fin (n + 1)} {b : Fin (n + 1)}, a.succ ≠ Fin.last (n + 1) := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Vector.mk_toList, hypothesis 3: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.List.Vector.mk_toList.h3.der.{u_1} : ∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n), v.toList.length = n := by
  (intros; simp; done)
theorem HypCheckProof.List.Vector.mk_toList.h3.{u_1} : ∀ {α : Type u_1} {n : ℕ} (v : List.Vector α n),
      (⟨v.toList, HypCheckProof.List.Vector.mk_toList.h3.der v⟩ : { l : List α // l.length = n }) = v := by
  intro hc_x0 hc_x1 hc_x2
  exact @List.Vector.mk_toList hc_x0 hc_x1 hc_x2 (@HypCheckProof.List.Vector.mk_toList.h3.der hc_x0 hc_x1 hc_x2)

-- Ordnode.Valid'.node4L_lemma₂, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.node4L_lemma₂.h3 : ¬∀ {b : ℕ} {c d : ℕ}, c ≤ 3 * d := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- List.Perm.permutations', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.permutations'.h3 : ¬∀ {α : Type} {s t : List α}, s.permutations'.Perm t.permutations' := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  decide +kernel)

-- List.forall₂_refl, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.forall₂_refl.h2 : ¬∀ {α : Type} {Rₐ : α → α → Prop} (l : List α), List.Forall₂ Rₐ l l := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop) ([0])) (by
  decide +kernel)

-- List.nodup_permutations'Aux_of_notMem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nodup_permutations'Aux_of_notMem.h3 : ¬∀ {α : Type} (s : List α) (x : α), (List.permutations'Aux x s).Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0]) (0)) (by
  decide +kernel)

-- List.perm_of_mem_permutations, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.perm_of_mem_permutations.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.Perm l₂ := fun hc_h => absurd (@hc_h (ℕ) ([]) ([0])) (by
  decide +kernel)

-- Set.offDiag_insert, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.offDiag_insert.h3 : ¬∀ {α : Type} {s : Set α} {a : α}, (Insert.insert a s).offDiag = s.offDiag ∪ {a} ×ˢ s ∪ s ×ˢ {a} := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (0)) (by
  simp)

-- Fin.cast_rev, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.cast_rev.h3 : ¬∀ {n m : ℕ} (i : Fin n), n = m := fun hc_h => absurd (@hc_h (1) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Lex.ne_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Lex.ne_iff.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, List.Lex (fun (x1 x2 : α) => x1 ≠ x2) l₁ l₂ ↔ l₁ ≠ l₂ := fun hc_h => absurd (@hc_h (ℕ) ([0]) ([])) (by
  decide +kernel)

-- Set.sInter_subset_of_mem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.sInter_subset_of_mem.h3 : ¬∀ {α : Type} {S : Set (Set α)} {t : Set α}, ⋂₀ S ⊆ t := fun hc_h => absurd (@hc_h (Bool) (∅) ({b : Bool | b = Bool.true})) (by
  simp)

-- Fin.find_nat_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.find_nat_lt.h3 : ¬∀ {n : ℕ} {p : ℕ → Prop} [inst : DecidablePred p], ∃ k < n, p k := fun hc_h => absurd (@hc_h (0) (fun n => n = 0 : ℕ → Prop) (fun (a : ℕ) => instDecidableEqNat a 0)) (by
  decide +kernel)

-- List.getD_reverse, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getD_reverse.h3 : ¬∀ {α : Type} {l : List α} (i : ℕ), l.reverse.getD i = l.getD (l.length - 1 - i) := fun hc_h => absurd (@hc_h (Bool) ([Bool.false]) (1)) (by
  decide +kernel)

-- Set.ofPred_subset_ofPred_of_imp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ofPred_subset_ofPred_of_imp.h3 : ¬∀ {α : Type} {p q : α → Prop}, {a : α | p a} ⊆ {a : α | q a} := fun hc_h => absurd (@hc_h (ℕ) (fun n => n = 0 : ℕ → Prop) (fun _ => False : ℕ → Prop)) (by
  simp)

-- Set.symmDiff_sUnion_subset, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.symmDiff_sUnion_subset.h3 : ¬∀ {α : Type} {s : Set α} {S : Set (Set α)}, symmDiff s (⋃₀ S) ⊆ ⋃₀ ((fun (x : Set α) => symmDiff s x) '' S) := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0}) (∅)) (by
  simp)

-- nodup_permsOfList, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.nodup_permsOfList.h3 : ¬∀ {α : Type} [inst : DecidableEq α] {l : List α}, (permsOfList l).Nodup := fun hc_h => absurd (@hc_h (Bool) (instDecidableEqBool) ([Bool.false, Bool.false])) (by
  decide +kernel)

-- Set.Nonempty.left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.left.h3 : ¬∀ {α : Type} {s : Set α} {t : Set α}, s.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False}) ({n : ℕ | n = 0})) (by
  simp)

-- Finset.monotone_preimage, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.monotone_preimage.h3 : ¬∀ {α β : Type} {f : α → β}, Function.Injective f := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun _ => 0 : ℕ → ℕ)) (by
  simp)

-- exists_ne_mem_inter_of_not_pairwise_disjoint, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.exists_ne_mem_inter_of_not_pairwise_disjoint.h3 : ¬∀ {α ι : Type} {f : ι → Set α}, ∃ (i : ι) (j : ι), i ≠ j ∧ ∃ (x : α), x ∈ f i ∩ f j := fun hc_h => absurd (@hc_h (ℕ) (ℕ) (fun (a : ℕ) => {x : ℕ | False})) (by
  simp)

-- Nat.shiftLeft_sub, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.shiftLeft_sub.h3 : ¬∀ (m : ℕ) {n k : ℕ}, m <<< (n - k) = m <<< n >>> k := fun hc_h => absurd (@hc_h (1) (0) (1)) (by
  decide +kernel)

-- Nat.find_lt_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.find_lt_iff.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p] (n : ℕ), ∃ (n : ℕ), p n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse) (0)) (by
  simp)

-- Set.subsingleton_of_forall_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subsingleton_of_forall_eq.h3 : ¬∀ {α : Type} {s : Set α} (a : α), s.Subsingleton := fun hc_h => absurd (@hc_h (Bool) ({x : Bool | True}) (Bool.false)) (by
  decide +kernel)

-- Nat.pair_lt_pair_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pair_lt_pair_right.h3 : ¬∀ (a : ℕ) {b₁ b₂ : ℕ}, Nat.pair a b₁ < Nat.pair a b₂ := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  decide +kernel)

-- Nat.getD_digits, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.getD_digits.h3 : ¬∀ (n i : ℕ) {b : ℕ}, (b.digits n).getD i 0 = n / b ^ i % b := fun hc_h => absurd (@hc_h (1) (0) (1)) (by
  decide +kernel)

-- Nat.lt_digits_length_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_digits_length_iff.h2 : ¬∀ {b k : ℕ} (n : ℕ), k < (b.digits n).length ↔ b ^ k ≤ n := fun hc_h => absurd (@hc_h (0) (1) (0)) (by
  decide +kernel)

-- Part.get_some, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Part.get_some.h2.der.{u_1} : ∀ {α : Type u_1} {a : α}, (Part.some a).Dom := by
  (intros; trivial)
theorem HypCheckProof.Part.get_some.h2.{u_1} : ∀ {α : Type u_1} {a : α}, (Part.some a).get HypCheckProof.Part.get_some.h2.der = a := by
  intro hc_x0 hc_x1
  exact @Part.get_some hc_x0 hc_x1 (@HypCheckProof.Part.get_some.h2.der hc_x0 hc_x1)

-- Subtype.map_id, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Subtype.map_id.h2.der.{u_1} : ∀ {α : Sort u_1} {p : α → Prop} (a : α), p a → p (@id α a) := by
  (intros; assumption)
theorem HypCheckProof.Subtype.map_id.h2.{u_1} : ∀ {α : Sort u_1} {p : α → Prop},
      @Eq (@Subtype α p → @Subtype α p) (@Subtype.map α α p p (@id α) (@HypCheckProof.Subtype.map_id.h2.der α p))
        (@id (@Subtype α p)) := by
  intro hc_x0 hc_x1
  exact @Subtype.map_id hc_x0 hc_x1 (@HypCheckProof.Subtype.map_id.h2.der hc_x0 hc_x1)

-- Nat.Subtype.coe_bot, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Subtype.coe_bot.h2 : ¬∀ {s : Set ℕ} [inst : DecidablePred fun (x : ℕ) => x ∈ s], Nonempty ↑s := fun hc_h => absurd (@hc_h ({x : ℕ | False}) (fun (a : ℕ) => Set.decidableOfPred a fun (x : ℕ) => False)) (by
  simp)

-- Fin.find?_eq_some_find_of_isSome, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.find?_eq_some_find_of_isSome.h2 : ¬∀ {n : ℕ} {p : Fin n → Bool}, (Fin.find? p).isSome = Bool.true := fun hc_h => absurd (@hc_h (0) (fun (a : Fin 0) => Bool.false)) (by
  decide +kernel)

-- List.Nodup.sublists, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.sublists.h2 : ¬∀ {α : Type} {l : List α}, l.sublists.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0])) (by
  decide +kernel)

-- Int.exists_lt_and_lt_iff_not_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.exists_lt_and_lt_iff_not_dvd.h2 : ¬∀ {n : ℤ} (m : ℤ), (∃ (k : ℤ), n * k < m ∧ m < n * (k + 1)) ↔ ¬n ∣ m := fun hc_h => absurd (@hc_h (0) (1)) (by
  omega)

-- Nat.Icc_factorization_eq_pow_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Icc_factorization_eq_pow_dvd.h2 : ¬∀ (n : ℕ) {p : ℕ}, Finset.Icc 1 (n.factorization p) = {i ∈ Finset.Ico 1 n | p ^ i ∣ n} := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- Set.Nontrivial.offDiag_nonempty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.offDiag_nonempty.h2 : ¬∀ {α : Type} {s : Set α}, s.offDiag.Nonempty := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- WithZeroMulInt.toNNReal_le_one_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithZeroMulInt.toNNReal_le_one_iff.h2 : ¬∀ {e : NNReal} {m : WithZero (Multiplicative ℤ)}, 1 < e := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Fintype.card_eq_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_eq_zero.h2 : ¬∀ {α : Type} [inst : Fintype α], Fintype.card α = 0 := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype)) (by
  decide +kernel)

-- Nat.factorization_le_factorization_mul_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_le_factorization_mul_right.h2 : ¬∀ {a b : ℕ}, b.factorization ≤ (a * b).factorization := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- Set.Nontrivial.pair_subset, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nontrivial.pair_subset.h2 : ¬∀ {α : Type} {s : Set α}, ∃ (x : α) (y : α), x ≠ y ∧ {x, y} ⊆ s := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- ZMod.intCast_mul_inv_eq_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.intCast_mul_inv_eq_one.h2 : Not
      (∀ {n : Nat} {x : Int},
        @Eq (ZMod n)
          (@HMul.hMul (ZMod n) (ZMod n) (ZMod n)
            (@instHMul (ZMod n)
              (@Distrib.toMul (ZMod n)
                (@instDistribOfSemiring (ZMod n)
                  (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))))
            (@Int.cast (ZMod n)
              (@AddGroupWithOne.toIntCast (ZMod n)
                (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
              x)
            (@Inv.inv (ZMod n) (ZMod.instInv n)
              (@Int.cast (ZMod n)
                (@AddGroupWithOne.toIntCast (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
                x)))
          (@OfNat.ofNat (ZMod n) (nat_lit 1)
            (@One.toOfNat1 (ZMod n)
              (@AddMonoidWithOne.toOne (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- ZMod.coe_int_inv_mul_eq_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.coe_int_inv_mul_eq_one.h2 : Not
      (∀ {n : Nat} {x : Int},
        @Eq (ZMod n)
          (@HMul.hMul (ZMod n) (ZMod n) (ZMod n)
            (@instHMul (ZMod n)
              (@Distrib.toMul (ZMod n)
                (@instDistribOfSemiring (ZMod n)
                  (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))))
            (@Inv.inv (ZMod n) (ZMod.instInv n)
              (@Int.cast (ZMod n)
                (@AddGroupWithOne.toIntCast (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
                x))
            (@Int.cast (ZMod n)
              (@AddGroupWithOne.toIntCast (ZMod n)
                (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
              x))
          (@OfNat.ofNat (ZMod n) (nat_lit 1)
            (@One.toOfNat1 (ZMod n)
              (@AddMonoidWithOne.toOne (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- ZMod.coe_int_mul_inv_eq_one, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.coe_int_mul_inv_eq_one.h2 : Not
      (∀ {n : Nat} {x : Int},
        @Eq (ZMod n)
          (@HMul.hMul (ZMod n) (ZMod n) (ZMod n)
            (@instHMul (ZMod n)
              (@Distrib.toMul (ZMod n)
                (@instDistribOfSemiring (ZMod n)
                  (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))))
            (@Int.cast (ZMod n)
              (@AddGroupWithOne.toIntCast (ZMod n)
                (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
              x)
            (@Inv.inv (ZMod n) (ZMod.instInv n)
              (@Int.cast (ZMod n)
                (@AddGroupWithOne.toIntCast (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
                x)))
          (@OfNat.ofNat (ZMod n) (nat_lit 1)
            (@One.toOfNat1 (ZMod n)
              (@AddMonoidWithOne.toOne (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- ZMod.isUnit_inv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.isUnit_inv.h2 : Not
      (∀ {m : Nat} {n : Int},
        @IsUnit (ZMod m)
          (@Semiring.toMonoid (ZMod m)
            (@CommSemiring.toSemiring (ZMod m) (@CommRing.toCommSemiring (ZMod m) (ZMod.commRing m))))
          (@Inv.inv (ZMod m) (ZMod.instInv m)
            (@Int.cast (ZMod m)
              (@AddGroupWithOne.toIntCast (ZMod m)
                (@Ring.toAddGroupWithOne (ZMod m) (@CommRing.toRing (ZMod m) (ZMod.commRing m))))
              n))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- Nat.factorization_pow_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_pow_self.h2 : ¬∀ {p n : ℕ}, (p ^ n).factorization p = n := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.factorization_eq_card_pow_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_eq_card_pow_dvd.h2 : ¬∀ (n : ℕ) {p : ℕ}, n.factorization p = {i ∈ Finset.Ico 1 n | p ^ i ∣ n}.card := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- Nat.ordProj_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordProj_le.h2 : ¬∀ {n : ℕ} (p : ℕ), p ^ n.factorization p ≤ n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.factorization_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_lt.h2 : ¬∀ {n : ℕ} (p : ℕ), n.factorization p < n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Set.eq_univ_of_univ_subset, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_univ_of_univ_subset.h2 : ¬∀ {α : Type} {s : Set α}, s = Set.univ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Nat.ordCompl_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordCompl_pos.h2 : ¬∀ {n : ℕ} (p : ℕ), 0 < n / p ^ n.factorization p := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Bool.of_decide_false, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.of_decide_false.h2 : ¬∀ {p : Prop} [inst : Decidable p], ¬p := fun hc_h => absurd (@hc_h (True) (instDecidableTrue)) (by
  decide +kernel)

-- Fintype.card_ofSubsingleton, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_ofSubsingleton.h2 : ¬∀ {α : Type} (a : α), Subsingleton α := fun hc_h => absurd (@hc_h (ℕ) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (0 : ℕ) (1 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.ordCompl_of_not_prime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ordCompl_of_not_prime.h2 : ¬∀ (n p : ℕ), n / p ^ n.factorization p = n := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- Nat.prod_pow_factorization_choose, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prod_pow_factorization_choose.h2 : ¬∀ (n k : ℕ), ∏ p ∈ Finset.range (n + 1), p ^ (n.choose k).factorization p = n.choose k := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- List.head_eq_getElem_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.head_eq_getElem_zero.h2 : ¬∀ {α : Type} {l : List α}, l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- Nat.factorization_factorial_eq_zero_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_factorial_eq_zero_of_lt.h2 : ¬∀ {p n : ℕ}, n.factorial.factorization p = 0 := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- Set.Nonempty.ssubset_univ, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.ssubset_univ.h2 : ¬∀ {α : Type} {s : Set α}, s ⊂ Set.univ := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True})) (by
  simp)

-- Nat.factorization_centralBinom_eq_zero_of_two_mul_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorization_centralBinom_eq_zero_of_two_mul_lt.h2 : ¬∀ {p n : ℕ}, n.centralBinom.factorization p = 0 := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- Part.some_get, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Part.some_get.h2 : ¬∀ {α : Type} {a : Part α}, a.Dom := fun hc_h => absurd (@hc_h (ℕ) (⊥)) (by
  nofun)

-- Nat.Prime.emultiplicity_pow_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.emultiplicity_pow_self.h2 : ¬∀ {p n : ℕ}, emultiplicity p (p ^ n) = ↑n := fun hc_h => absurd (@hc_h (1) (0)) (by
  simp)

-- ENat.toNat_le_of_le_coe, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.toNat_le_of_le_coe.h2 : ¬∀ {m : ℕ∞} {n : ℕ}, m.toNat ≤ n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.factorial_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorial_le.h2 : ¬∀ {m n : ℕ}, m.factorial ≤ n.factorial := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

-- Int.card_fintype_Ioo_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.card_fintype_Ioo_of_lt.h2 : ¬∀ (a b : ℤ), ↑(Fintype.card ↑(Set.Ioo a b)) = b - a - 1 := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Int.card_Icc_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.card_Icc_of_le.h2 : ¬∀ (a b : ℤ), ↑(Finset.Icc a b).card = b + 1 - a := fun hc_h => absurd (@hc_h (1) (-1)) (by
  decide +kernel)

-- List.IsRotated.cons_getLast_dropLast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsRotated.cons_getLast_dropLast.h2 : ¬∀ {α : Type} (L : List α), L ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- Sym2.toRel_fromRel, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.toRel_fromRel.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
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

-- ENat.toNat_sub, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.toNat_sub.h1 : ¬∀ {n : ℕ∞} (m : ℕ∞), (m - n).toNat = m.toNat - n.toNat := fun hc_h => absurd (@hc_h (⊤) (1)) (by
  decide +kernel)

-- ENat.toNat_le_of_le_natCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.toNat_le_of_le_natCast.h2 : ¬∀ {m : ℕ∞} {n : ℕ}, m.toNat ≤ n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.ascFactorial_eq_div', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ascFactorial_eq_div'.h2 : ¬∀ (n k : ℕ), n.ascFactorial k = (n + k - 1).factorial / (n - 1).factorial := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.pow_lt_ascFactorial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_lt_ascFactorial.h2 : ¬∀ (n : ℕ) {k : ℕ}, (n + 1) ^ k < (n + 1).ascFactorial k := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Sym2.fromRel_subset_compl_diagSet, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym2.fromRel_subset_compl_diagSet.h2 : ¬∀ {α : Type} {r : α → α → Prop}, Std.Symm r := fun hc_h => absurd (@hc_h (ℕ) (fun a b => a < b : ℕ → ℕ → Prop)) (by
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

-- Nat.factorial_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorial_lt.h2 : ¬∀ {m n : ℕ}, n.factorial < m.factorial ↔ n < m := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.descFactorial_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.descFactorial_of_lt.h2 : ¬∀ {n k : ℕ}, n.descFactorial k = 0 := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Sigma.fst_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sigma.fst_injective.h2 : Not (∀ {α : Type} {β : α → Type}, @Function.Injective (@Sigma α fun (a : α) => β a) α (@Sigma.fst α fun (a : α) => β a)) := fun hc_h => absurd (@hc_h (Bool) (fun (a : Bool) => Bool)) (by
  decide +kernel)

-- ENat.natCast_lt_of_coe_top_le_withTop, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.natCast_lt_of_coe_top_le_withTop.h1 : ¬∀ {N : WithTop ℕ∞} (n : ℕ), ↑n < N := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- ENat.add_one_natCast_le_withTop_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.add_one_natCast_le_withTop_of_lt.h2 : ¬∀ {m : ℕ} {n : WithTop ℕ∞}, ↑(m + 1) ≤ n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.factorial_inj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.factorial_inj.h2 : ¬∀ {m n : ℕ}, n.factorial = m.factorial ↔ n = m := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- List.Nodup.attach, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Nodup.attach.h2 : ¬∀ {α : Type} {l : List α}, l.attach.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0])) (by
  decide +kernel)

-- ENat.epow_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.epow_pos.h2 : ¬∀ {x y : ℕ∞}, 0 < x ^ y := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.size_bit, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.size_bit.h2 : ¬∀ {b : Bool} {n : ℕ}, (Nat.bit b n).size = n.size.succ := fun hc_h => absurd (@hc_h (Bool.false) (0)) (by
  decide +kernel)

-- Function.Injective.nodup, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Function.Injective.nodup.h2 : ¬∀ {α : Type} {l : List α}, l.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0])) (by
  decide +kernel)

-- Nat.coprime_self_sub_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_self_sub_left.h2 : ¬∀ {m n : ℕ}, (n - m).Coprime n ↔ m.Coprime n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.testBit_eq_false_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.testBit_eq_false_of_lt.h2 : ¬∀ {n i : ℕ}, n.testBit i = Bool.false := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Int.ne_zero_of_gcd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.ne_zero_of_gcd.h2 : ¬∀ {x y : ℤ}, x ≠ 0 ∨ y ≠ 0 := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Fin2.IsLT.succ, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin2.IsLT.succ.h2 : ¬∀ (m n : ℕ), Fin2.IsLT m.succ n.succ := fun hc_h => absurd (@hc_h (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.h)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Finset.Nonempty.not_empty_toList, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.Nonempty.not_empty_toList.h2.{u_1} : ¬∀ {α : Type u_1} {s : Finset α}, ¬s.toList.isEmpty = Bool.true := by
  (simp_all; done)

-- Nat.Coprime.lcm_eq_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.lcm_eq_mul.h2 : ¬∀ {m n : ℕ}, m.lcm n = m * n := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- Nat.coprime_sub_self_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_sub_self_right.h2 : ¬∀ {m n : ℕ}, m.Coprime (n - m) ↔ m.Coprime n := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- List.IsChain.length_div_two_le_count_bool, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.length_div_two_le_count_bool.h1 : ¬∀ {l : List Bool} (b : Bool), l.length / 2 ≤ List.count b l := fun hc_h => absurd (@hc_h ([Bool.false, Bool.false]) (Bool.true)) (by
  decide +kernel)

-- List.IsChain.two_mul_count_bool_le_length_add_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.two_mul_count_bool_le_length_add_one.h1 : ¬∀ {l : List Bool} (b : Bool), 2 * List.count b l ≤ l.length + 1 := fun hc_h => absurd (@hc_h ([Bool.false, Bool.false]) (Bool.false)) (by
  decide +kernel)

-- List.IsChain.count_not_cons, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.count_not_cons.h2 : ¬∀ {b : Bool} {l : List Bool}, List.count (!b) l = List.count b l + l.length % 2 := fun hc_h => absurd (@hc_h (Bool.false) ([Bool.false])) (by
  decide +kernel)

-- Finset.Nonempty.empty_ssubset, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.Nonempty.empty_ssubset.h2.{u_1} : ¬∀ {α : Type u_1} {s : Finset α}, ∅ ⊂ s := by
  (simp_all; done)

-- Multiset.noncommSum_empty, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Multiset.noncommSum_empty.h2.der.{u_3} : ∀ {α : Type u_3} [inst : AddMonoid α],
      @Set.Pairwise α
        (@Set.ofPred α fun (x : α) =>
          @Membership.mem α (Multiset α) (@Multiset.instMembership α)
            (@OfNat.ofNat (Multiset α) (nat_lit 0) (@Zero.toOfNat0 (Multiset α) (@Multiset.instZero α))) x)
        (@AddCommute α (@AddZero.toAdd α (@AddZeroClass.toAddZero α (@AddMonoid.toAddZeroClass α inst)))) := by
  (intros; simp; done)
theorem HypCheckProof.Multiset.noncommSum_empty.h2.{u_3} : ∀ {α : Type u_3} [inst : AddMonoid α],
      @Eq α
        (@Multiset.noncommSum α inst
          (@OfNat.ofNat (Multiset α) (nat_lit 0) (@Zero.toOfNat0 (Multiset α) (@Multiset.instZero α)))
          (@HypCheckProof.Multiset.noncommSum_empty.h2.der α inst))
        (@OfNat.ofNat α (nat_lit 0)
          (@Zero.toOfNat0 α (@AddZero.toZero α (@AddZeroClass.toAddZero α (@AddMonoid.toAddZeroClass α inst))))) := by
  intro hc_x0 hc_x1
  exact @Multiset.noncommSum_empty hc_x0 hc_x1 (@HypCheckProof.Multiset.noncommSum_empty.h2.der hc_x0 hc_x1)

-- List.nodup_permutations, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.nodup_permutations.h2 : ¬∀ {α : Type} (s : List α), s.permutations.Nodup := fun hc_h => absurd (@hc_h (ℕ) ([0, 0])) (by
  simp)

-- Fin.coe_natCast_eq_mod, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.coe_natCast_eq_mod.h2 : ¬∀ (m n : ℕ), NeZero m := fun hc_h => absurd (@hc_h (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fin.val_add_one_of_lt', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.val_add_one_of_lt'.h2 : Not
      (∀ {n : Nat} {i : Fin n},
        @Eq Nat
          (@Fin.val n
            (@HAdd.hAdd (Fin n) (Fin n) (Fin n) (@instHAdd (Fin n) (@Fin.instAdd n)) i
              (@OfNat.ofNat (Fin n) (nat_lit 1) (@Fin.instOfNat n (@Fin.neZero n i) (nat_lit 1)))))
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Fin.val n i)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@of_decide_eq_true
        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Set.Nonempty.ne_empty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.ne_empty.h2 : ¬∀ {α : Type} {s : Set α}, s ≠ ∅ := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Bool.and_elim_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.and_elim_left.h2 : ¬∀ {a : Bool} {b : Bool}, a = Bool.true := fun hc_h => absurd (@hc_h (Bool.false) (Bool.false)) (by
  decide +kernel)

-- Fin.ofNat_eq_cast, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.ofNat_eq_cast.h1 : ¬∀ (n a : ℕ), NeZero n := fun hc_h => absurd (@hc_h (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Set.Infinite.exists_subset_countable_infinite, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.exists_subset_countable_infinite.h2 : ¬∀ {α : Type} {s : Set α}, ∃ t ⊆ s, t.Countable ∧ t.Infinite := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Fintype.exists_pair_of_one_lt_card, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.exists_pair_of_one_lt_card.h2 : ¬∀ {α : Type} [inst : Fintype α], ∃ (a : α) (b : α), a ≠ b := fun hc_h => absurd (@hc_h (Unit) (PUnit.fintype)) (by
  decide +kernel)

-- Infinite.exists_subset_card_eq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Infinite.exists_subset_card_eq.h1 : ¬∀ (α : Type) (n : ℕ), ∃ (s : Finset α), s.card = n := fun hc_h => absurd (@hc_h (Bool) (3)) (by
  decide +kernel)

-- Prod.snd_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Prod.snd_injective.h2 : Not (∀ {α β : Type}, @Function.Injective (Prod α β) β (@Prod.snd α β)) := fun hc_h => absurd (@hc_h (Bool) (Bool)) (by
  decide +kernel)

-- Stream'.cycle_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Stream'.cycle_eq.h2 : ¬∀ {α : Type} (l : List α), l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- Set.Finite.encard_lt_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Finite.encard_lt_top.h2 : ¬∀ {α : Type} {s : Set α}, s.encard < ⊤ := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True})) (by
  simp)

-- Fintype.false, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.false.h1 : ¬∀ {α : Type} (_h : Fintype α), False := fun hc_h => absurd (@hc_h (Bool) (Bool.fintype)) (by
  decide +kernel)

-- Fin.pred_castSucc_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.pred_castSucc_lt.h2 : ¬∀ {n : ℕ} {a : Fin (n + 1)}, a.castSucc ≠ 0 := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Int.abs_le_sqrt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.abs_le_sqrt.h2 : ¬∀ {a b : ℤ}, |a| ≤ Int.sqrt b ↔ a * a ≤ b := fun hc_h => absurd (@hc_h (0) (-1)) (by
  decide +kernel)

-- Int.abs_le_sqrt_iff_sq_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.abs_le_sqrt_iff_sq_le.h2 : ¬∀ {a b : ℤ}, |a| ≤ Int.sqrt b ↔ a ^ 2 ≤ b := fun hc_h => absurd (@hc_h (0) (-1)) (by
  decide +kernel)

-- Finset.Nonempty.card_pos, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Finset.Nonempty.card_pos.h2.{u_1} : ¬∀ {α : Type u_1} {s : Finset α}, 0 < s.card := by
  (simp_all; done)

-- Set.even_ncard_compl_iff', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.even_ncard_compl_iff'.h1 : ¬∀ {α : Type} (s : Set α), Even sᶜ.ncard ↔ Odd s.ncard := fun hc_h => absurd (@hc_h (Bool) ({b : Bool | b = Bool.true})) (by
  simp)

-- Int.le_of_ofNat_le_ofNat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.le_of_ofNat_le_ofNat.h2 : ¬∀ {m n : ℕ}, m ≤ n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Fin.succAbove_pred_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.succAbove_pred_self.h2 : ¬∀ {n : ℕ} (p : Fin (n + 1)), p ≠ 0 := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Nat.Prime.coprime_iff_not_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.coprime_iff_not_dvd.h2 : ¬∀ {p n : ℕ}, p.Coprime n ↔ ¬p ∣ n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Rat.le_toNNRat_iff_coe_le', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.le_toNNRat_iff_coe_le'.h2 : ¬∀ {p : ℚ} {q : ℚ≥0}, q ≤ p.toNNRat ↔ ↑q ≤ p := fun hc_h => absurd (@hc_h (-1) (0)) (by
  decide +kernel)

-- Fin.exists_succ_eq_of_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.exists_succ_eq_of_ne_zero.h2 : ¬∀ {n : ℕ} {x : Fin (n + 1)}, ∃ (y : Fin n), y.succ = x := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Ico.filter_le_of_bot, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.filter_le_of_bot.h2 : ¬∀ {n m : ℕ}, List.filter (fun (x : ℕ) => Decidable.decide (x ≤ n)) (List.Ico n m) = [n] := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- List.Ico.succ_top, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Ico.succ_top.h2 : ¬∀ {n m : ℕ}, List.Ico n (m + 1) = List.Ico n m ++ [m] := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Dvd.dvd.zero_modEq_int, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dvd.dvd.zero_modEq_int.h2 : ¬∀ {n a : ℤ}, 0 ≡ a [ZMOD n] := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Int.existsUnique_equiv_nat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.existsUnique_equiv_nat.h2 : ¬∀ (a : ℤ) {b : ℤ}, ∃ (z : ℕ), ↑z < b ∧ ↑z ≡ a [ZMOD b] := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Set.Nonempty.encard_pos, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.encard_pos.h2 : ¬∀ {α : Type} {s : Set α}, 0 < s.encard := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Rat.toNNRat_lt_toNNRat_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.toNNRat_lt_toNNRat_iff.h2 : ¬∀ {p q : ℚ}, q.toNNRat < p.toNNRat ↔ q < p := fun hc_h => absurd (@hc_h (0) (-1)) (by
  decide +kernel)

-- List.Palindrome.of_reverse_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Palindrome.of_reverse_eq.h2 : ¬∀ {α : Type} {l : List α}, l.Palindrome := fun hc_h => absurd (@hc_h (ℕ) ([0, 1])) (by
  decide +kernel)

-- List.Palindrome.reverse_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Palindrome.reverse_eq.h2 : ¬∀ {α : Type} {l : List α}, l.reverse = l := fun hc_h => absurd (@hc_h (ℕ) ([0, 1])) (by
  decide +kernel)

-- Fin.castSucc_castPred, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castSucc_castPred.h2 : ¬∀ {n : ℕ} (i : Fin (n + 1)), i ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Rat.le_toNNRat_iff_coe_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.le_toNNRat_iff_coe_le.h2 : ¬∀ {p : ℚ} {q : ℚ≥0}, q ≤ p.toNNRat ↔ ↑q ≤ p := fun hc_h => absurd (@hc_h (-1) (0)) (by
  decide +kernel)

-- Dvd.dvd.modEq_zero_int, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Dvd.dvd.modEq_zero_int.h2 : ¬∀ {n a : ℤ}, a ≡ 0 [ZMOD n] := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Int.existsUnique_equiv, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.existsUnique_equiv.h2 : ¬∀ (a : ℤ) {b : ℤ}, ∃ (z : ℤ), 0 ≤ z ∧ z < b ∧ z ≡ a [ZMOD b] := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Set.coe_ncard_eq_encard, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.coe_ncard_eq_encard.h2 : ¬∀ {α : Type} (s : Set α), ↑s.ncard = s.encard := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | True})) (by
  simp)

-- Nat.fib_lt_fib, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.fib_lt_fib.h1 : ¬∀ {m n : ℕ}, Nat.fib m < Nat.fib n ↔ m < n := fun hc_h => absurd (@hc_h (1) (2)) (by
  decide +kernel)

-- Nat.Prime.dvd_factorial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_factorial.h2 : ¬∀ {n p : ℕ}, p ∣ n.factorial ↔ p ≤ n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- EReal.toENNReal_le_toENNReal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.toENNReal_le_toENNReal.h2 : ¬∀ {x y : EReal}, x.toENNReal ≤ y.toENNReal := fun hc_h => absurd (@hc_h (⊤) (0)) (by
  decide +kernel)

-- Nat.coprime_of_dvd', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_of_dvd'.h2 : ¬∀ {m n : ℕ}, m.Coprime n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.Prime.dvd_iff_not_coprime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.dvd_iff_not_coprime.h2 : ¬∀ {p n : ℕ}, p ∣ n ↔ ¬p.Coprime n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- EReal.le_neg_of_le_neg, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.le_neg_of_le_neg.h2 : ¬∀ {a b : EReal}, b ≤ -a := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- Nat.nth_apply_eq_orderIsoOfNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_apply_eq_orderIsoOfNat.h1 : ¬∀ {p : ℕ → Prop} (n : ℕ), (Set.ofPred p).Infinite := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (0)) (by
  simp)

-- Nat.Prime.not_prime_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.not_prime_pow.h2 : ¬∀ {x n : ℕ}, ¬Nat.Prime (x ^ n) := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- Nat.nth_mem_of_infinite, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_mem_of_infinite.h1 : ¬∀ {p : ℕ → Prop} (n : ℕ), p (Nat.nth p n) := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (0)) (by
  decide +kernel)

-- Nat.nth_of_forall_not, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_of_forall_not.h2 : ¬∀ {p : ℕ → Prop} {n : ℕ}, Nat.nth p n = 0 := fun hc_h => absurd (@hc_h (fun _ => True : ℕ → Prop) (1)) (by
  simp)

-- Nat.exists_lt_card_nth_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_lt_card_nth_eq.h2 : ¬∀ {p : ℕ → Prop} {x : ℕ}, ∃ (n : ℕ), (∀ (hf : (Set.ofPred p).Finite), n < hf.toFinset.card) ∧ Nat.nth p n = x := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop) (1)) (by
  simp)

-- Nat.pow_minFac, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_minFac.h2 : ¬∀ {n k : ℕ}, (n ^ k).minFac = n.minFac := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.coprime_primeFactorsList_disjoint, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.coprime_primeFactorsList_disjoint.h2 : ¬∀ {a b : ℕ}, a.primeFactorsList.Disjoint b.primeFactorsList := fun hc_h => absurd (@hc_h (2) (2)) (by
  simp)

-- Nat.isLeast_nth, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.isLeast_nth.h2 : ¬∀ {p : ℕ → Prop} {n : ℕ}, IsLeast {i : ℕ | p i ∧ ∀ k < n, Nat.nth p k < i} (Nat.nth p n) := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (0)) (by
  decide +kernel)

-- Nat.nth_zero_of_exists, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_zero_of_exists.h2 : ¬∀ {p : ℕ → Prop} [inst : DecidablePred p], ∃ (n : ℕ), p n := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (fun (a : ℕ) => instDecidableFalse)) (by
  simp)

-- List.length_pos_of_ne_nil, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.length_pos_of_ne_nil.h2 : ¬∀ {α : Type} {l : List α}, 0 < l.length := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- EReal.neg_lt_of_neg_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.neg_lt_of_neg_lt.h2 : ¬∀ {a b : EReal}, -b < a := fun hc_h => absurd (@hc_h (0) (0)) (by
  simp)

-- Nat.nth_mem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_mem.h2 : ¬∀ {p : ℕ → Prop} (n : ℕ), p (Nat.nth p n) := fun hc_h => absurd (@hc_h (fun _ => False : ℕ → Prop) (0)) (by
  decide +kernel)

-- Nat.Prime.primeFactorsList_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.primeFactorsList_pow.h1 : ¬∀ {p : ℕ} (n : ℕ), (p ^ n).primeFactorsList = List.replicate n p := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Ordnode.Raised.dist_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Raised.dist_le.h2 : ¬∀ {n m : ℕ}, n.dist m ≤ 1 := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- Ordnode.Sized.size_eq_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Sized.size_eq_zero.h2 : ¬∀ {α : Type} {t : Ordnode α}, t.size = 0 ↔ t = Ordnode.nil := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil)) (by
  simp)

-- Ordnode.Raised.dist_le', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Raised.dist_le'.h2 : ¬∀ {n m : ℕ}, m.dist n ≤ 1 := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- Nat.le_of_mem_primeFactorsList, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_of_mem_primeFactorsList.h2 : ¬∀ {n p : ℕ}, p ≤ n := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Ordnode.size_eq_realSize, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.size_eq_realSize.h2 : ¬∀ {α : Type} {t : Ordnode α}, t.size = t.realSize := fun hc_h => absurd (@hc_h (ℕ) (Ordnode.node 0 Ordnode.nil 0 Ordnode.nil)) (by
  decide +kernel)

-- Nat.primeFactors_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.primeFactors_pow.h2 : ¬∀ {k : ℕ} (n : ℕ), (n ^ k).primeFactors = n.primeFactors := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- Nat.Coprime.disjoint_primeFactors, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Coprime.disjoint_primeFactors.h2 : ¬∀ {a b : ℕ}, Disjoint a.primeFactors b.primeFactors := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- Set.ncard_le_card, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.ncard_le_card.h1 : ¬∀ {α : Type} (s : Set α), s.ncard ≤ Nat.card α := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Set.Nonempty.compl_ssubset_univ, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Nonempty.compl_ssubset_univ.h2 : ¬∀ {α : Type} {s : Set α}, sᶜ ⊂ Set.univ := fun hc_h => absurd (@hc_h (ℕ) ({x : ℕ | False})) (by
  simp)

-- Finset.empty_disjUnion, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finset.empty_disjUnion.h2.der.{u_2} : ∀ {α : Type u_2} (t : Finset α),
      @Disjoint (Finset α) (@Finset.instPartialOrder α) (@Finset.instOrderBot α)
        (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α)) t := by
  (intros; solve_by_elim)
theorem HypCheckProof.Finset.empty_disjUnion.h2.{u_2} : ∀ {α : Type u_2} (t : Finset α),
      @Eq (Finset α)
        (@Finset.disjUnion α (@EmptyCollection.emptyCollection (Finset α) (@Finset.instEmptyCollection α)) t
          (@HypCheckProof.Finset.empty_disjUnion.h2.der α t))
        t := by
  intro hc_x0 hc_x1
  exact @Finset.empty_disjUnion hc_x0 hc_x1 (@HypCheckProof.Finset.empty_disjUnion.h2.der hc_x0 hc_x1)

-- ZMod.val_intCast, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.val_intCast.h2 : Not
      (∀ {n : Nat} (a : Int),
        @Eq Int
          (@Nat.cast Int instNatCastInt
            (@ZMod.val n
              (@Int.cast (ZMod n)
                (@AddGroupWithOne.toIntCast (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))
                a)))
          (@HMod.hMod Int Int Int (@instHMod Int Int.instMod) a (@Nat.cast Int instNatCastInt n))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) (by
  decide +kernel)

-- Set.Infinite.nontrivial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.Infinite.nontrivial.h2 : ¬∀ {α : Type} {s : Set α}, s.Nontrivial := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Finset.disjUnion_empty, hypothesis 2: removable
set_option maxHeartbeats 1000 in
theorem HypCheckProof.Finset.disjUnion_empty.h2.der.{u_2} : ∀ {α : Type u_2} (s : Finset α), Disjoint s ∅ := by
  (intros; solve_by_elim)
theorem HypCheckProof.Finset.disjUnion_empty.h2.{u_2} : ∀ {α : Type u_2} (s : Finset α), s.disjUnion ∅ (HypCheckProof.Finset.disjUnion_empty.h2.der s) = s := by
  intro hc_x0 hc_x1
  exact @Finset.disjUnion_empty hc_x0 hc_x1 (@HypCheckProof.Finset.disjUnion_empty.h2.der hc_x0 hc_x1)

-- Ordnode.Valid'.rotateL_lemma₄, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Ordnode.Valid'.rotateL_lemma₄.h2 : ¬∀ {a b : ℕ}, 3 * b ≤ 16 * a + 9 := fun hc_h => absurd (@hc_h (0) (9)) (by
  decide +kernel)

-- Rat.intCast_div, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.intCast_div.h2 : Not
      (∀ (a b : Int),
        @Eq Rat (@Int.cast Rat Rat.instIntCast (@HDiv.hDiv Int Int Int (@instHDiv Int Int.instDiv) a b))
          (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Int.cast Rat Rat.instIntCast a)
            (@Int.cast Rat Rat.instIntCast b))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))) (@OfNat.ofNat Int (nat_lit 2) (@instOfNat (nat_lit 2)))) (by
  decide +kernel)

-- Fin.predAbove_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_zero.h1 : ¬∀ {n : ℕ} {i : Fin (n + 1)}, NeZero n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fin.range_castLE, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.range_castLE.h2 : ¬∀ {n k : ℕ}, n ≤ k := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Rat.natCast_div, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.natCast_div.h2 : Not
      (∀ (a b : Nat),
        @Eq Rat (@Nat.cast Rat Rat.instNatCast (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a b))
          (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Nat.cast Rat Rat.instNatCast a)
            (@Nat.cast Rat Rat.instNatCast b))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (by
  decide +kernel)

-- ZMod.natCast_toNat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.natCast_toNat.h2 : Not
      (∀ (p : Nat) {z : Int},
        @Eq (ZMod p)
          (@Nat.cast (ZMod p)
            (@AddMonoidWithOne.toNatCast (ZMod p)
              (@AddGroupWithOne.toAddMonoidWithOne (ZMod p)
                (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p)))))
            z.toNat)
          (@Int.cast (ZMod p)
            (@AddGroupWithOne.toIntCast (ZMod p)
              (@Ring.toAddGroupWithOne (ZMod p) (@CommRing.toRing (ZMod p) (ZMod.commRing p))))
            z)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1))))) (by
  decide +kernel)

-- ZMod.isUnit_prime_iff_not_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.isUnit_prime_iff_not_dvd.h2 : Not
      (∀ {n p : Nat},
        Iff
          (@IsUnit (ZMod n)
            (@Semiring.toMonoid (ZMod n)
              (@CommSemiring.toSemiring (ZMod n) (@CommRing.toCommSemiring (ZMod n) (ZMod.commRing n))))
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              p))
          (Not (@Dvd.dvd Nat Nat.instDvd p n))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  simp)

-- ZMod.addOrderOf_coe', hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.addOrderOf_coe'.h2 : Not
      (∀ {a : Nat} (n : Nat),
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

-- Int.natAbs_natCast_sub_natCast_of_ge, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.natAbs_natCast_sub_natCast_of_ge.h2 : Not
      (∀ {a b : Nat},
        @Eq Nat
          (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@Nat.cast Int instNatCastInt a)
              (@Nat.cast Int instNatCastInt b)).natAbs
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) a b)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Fin.coe_castPred, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.coe_castPred.h2 : ¬∀ {n : ℕ} (i : Fin (n + 1)), i ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- PNat.le_sub_one_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.le_sub_one_of_lt.h2 : ¬∀ {a b : ℕ+}, a ≤ b - 1 := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- ZMod.val_inv_mul, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.val_inv_mul.h2 : Not
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
              (@ZMod.val n
                (@Inv.inv (ZMod n) (ZMod.instInv n)
                  (@Nat.cast (ZMod n)
                    (@AddMonoidWithOne.toNatCast (ZMod n)
                      (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                        (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
                    m))))
            (@Nat.cast (ZMod n)
              (@AddMonoidWithOne.toNatCast (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))
              m))
          (@OfNat.ofNat (ZMod n) (nat_lit 1)
            (@One.toOfNat1 (ZMod n)
              (@AddMonoidWithOne.toOne (ZMod n)
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                  (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n)))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Fin.castLE_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castLE_injective.h2 : ¬∀ {n m : ℕ}, m ≤ n := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- PNat.mul_div_exact, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.mul_div_exact.h2 : ¬∀ {m k : ℕ+}, k * m.divExact k = m := fun hc_h => absurd (@hc_h (1) (2)) (by
  decide +kernel)

-- Fin.predAbove_castPred_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.predAbove_castPred_self.h2 : ¬∀ {n : ℕ} (p : Fin (n + 1)), p ≠ Fin.last n := fun hc_h => absurd (@hc_h (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- PNat.sub_add_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.sub_add_of_lt.h2 : ¬∀ {a b : ℕ+}, a - b + b = a := fun hc_h => absurd (@hc_h (1) (1)) (by
  decide +kernel)

-- Rat.num_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.num_dvd.h2 : ¬∀ (a : ℤ) {b : ℤ}, (Rat.divInt a b).num ∣ a := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Finset.Nat.antidiagonal_filter_le_snd_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nat.antidiagonal_filter_le_snd_of_le.h2 : ¬∀ {n k : ℕ},
        {a ∈ Finset.HasAntidiagonal.antidiagonal n | k ≤ a.2} =
          Finset.map
            ((Function.Embedding.refl ℕ).prodMap { toFun := fun (x : ℕ) => x + k, inj' := add_left_injective k : ℕ ↪ ℕ })
            (Finset.HasAntidiagonal.antidiagonal (n - k)) := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Finset.Nat.antidiagonal_filter_fst_le_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nat.antidiagonal_filter_fst_le_of_le.h2 : ¬∀ {n k : ℕ},
        {a ∈ Finset.HasAntidiagonal.antidiagonal n | a.1 ≤ k} =
          Finset.map
            ((Function.Embedding.refl ℕ).prodMap
              { toFun := fun (x : ℕ) => x + (n - k), inj' := add_left_injective (n - k) : ℕ ↪ ℕ })
            (Finset.HasAntidiagonal.antidiagonal k) := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Finset.Nat.antidiagonal_filter_le_fst_of_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.Nat.antidiagonal_filter_le_fst_of_le.h2 : ¬∀ {n k : ℕ},
        {a ∈ Finset.HasAntidiagonal.antidiagonal n | k ≤ a.1} =
          Finset.map
            ({ toFun := fun (x : ℕ) => x + k, inj' := add_left_injective k : ℕ ↪ ℕ }.prodMap (Function.Embedding.refl ℕ))
            (Finset.HasAntidiagonal.antidiagonal (n - k)) := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- PrimeMultiset.coePNat_prime, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PrimeMultiset.coePNat_prime.h2 : ¬∀ (v : PrimeMultiset) (p : ℕ+), p.Prime := fun hc_h => absurd (@hc_h (0) (1)) (by
  simp)

-- Nat.bits_append_bit, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bits_append_bit.h2 : ¬∀ (n : ℕ) (b : Bool), (Nat.bit b n).bits = b :: n.bits := fun hc_h => absurd (@hc_h (0) (Bool.false)) (by
  decide +kernel)

-- Nat.choose_lt_two_pow, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_lt_two_pow.h2 : ¬∀ (n k : ℕ), n.choose k < 2 ^ n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.clog_of_left_le_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.clog_of_left_le_one.h1 : ¬∀ {b : ℕ} (n : ℕ), Nat.clog b n = 0 := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- Nat.choose_eq_factorial_div_factorial, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_eq_factorial_div_factorial.h2 : ¬∀ {n k : ℕ}, n.choose k = n.factorial / (k.factorial * (n - k).factorial) := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Sym.instIsEmptySucc, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym.instIsEmptySucc.h2 : ¬∀ {α : Type} (n : ℕ), IsEmpty (Sym α n.succ) := fun hc_h => absurd (@hc_h (ℕ) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.false (Inhabited.default : Sym ℕ (Nat.succ 0)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.le_pow_clog, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_pow_clog.h1 : ¬∀ {b : ℕ} (x : ℕ), x ≤ b ^ Nat.clog b x := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- Nat.choose_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.choose_ne_zero.h2 : ¬∀ {n k : ℕ}, n.choose k ≠ 0 := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Sym.instSubsingleton, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Sym.instSubsingleton.h1 : ¬∀ {α : Type} (n : ℕ), Subsingleton (Sym α n) := fun hc_h => absurd (@hc_h (Bool) (1)) (by
  nofun)

-- Nat.log_lt_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.log_lt_self.h2 : ¬∀ (b : ℕ) {x : ℕ}, Nat.log b x < x := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- instLawfulOfScientificOfCharZero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.instLawfulOfScientificOfCharZero.h2 : ¬∀ {K : Type} [inst : Field K], Lean.Grind.LawfulOfScientific K := fun hc_h => absurd (@hc_h (ZMod 2) (ZMod.instField 2)) (by
  exact fun hc_c =>
    absurd (hc_c.ofScientific_def (m := (2 : ℕ)) (s := (Bool.true : Bool)) (e := (1 : ℕ)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.lt_base_pow_length_digits, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.lt_base_pow_length_digits.h2 : ¬∀ {b m : ℕ}, m < b ^ (b.digits m).length := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- List.getLast?_eq_getLast_of_ne_nil, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getLast?_eq_getLast_of_ne_nil.h2 : ¬∀ {α : Type} {l : List α}, l ≠ [] := fun hc_h => absurd (@hc_h (ℕ) ([])) (by
  decide +kernel)

-- Set.eq_empty_of_subset_empty, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.eq_empty_of_subset_empty.h2 : ¬∀ {α : Type} {s : Set α}, s = ∅ := fun hc_h => absurd (@hc_h (ℕ) ({n : ℕ | n = 0})) (by
  simp)

-- Nat.minSqFac_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.minSqFac_dvd.h2 : ¬∀ {n d : ℕ}, d * d ∣ n := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Nat.head!_digits, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.head!_digits.h2 : ¬∀ {b n : ℕ}, (b.digits n).head! = n % b := fun hc_h => absurd (@hc_h (1) (1)) (by
  decide +kernel)

-- List.pairwiseDisjoint_consFixedLengthDigits, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.pairwiseDisjoint_consFixedLengthDigits.h1 : ¬∀ {b : ℕ} (l : ℕ), 1 < b := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.padicValNat_lt_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.padicValNat_lt_self.h2 : ¬∀ {p n : ℕ}, multiplicity p n < n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.maxPowDvdDiv.go_spec, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.maxPowDvdDiv.go_spec.h2 : ¬∀ {n p : ℕ}, 1 < p ∧ n ≠ 0 := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.maxPowDvdDiv_of_base_le_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.maxPowDvdDiv_of_base_le_one.h1 : ¬∀ {p : ℕ} (n : ℕ), p.maxPowDvdDiv n = (0, n) := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- Nat.maxPowDvdDiv_base_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.maxPowDvdDiv_base_pow.h1 : ¬∀ {p : ℕ} (k : ℕ), p.maxPowDvdDiv (p ^ k) = (k, 1) := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.multiplicity_lt_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.multiplicity_lt_self.h2 : ¬∀ {p n : ℕ}, multiplicity p n < n := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Nat.maxPowDvdDiv_of_not_dvd, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.maxPowDvdDiv_of_not_dvd.h2 : ¬∀ {p n : ℕ}, p.maxPowDvdDiv n = (0, n) := fun hc_h => absurd (@hc_h (2) (2)) (by
  decide +kernel)

-- padicValNat_base_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.padicValNat_base_pow.h1 : ¬∀ {p : ℕ} (k : ℕ), multiplicity p (p ^ k) = k := fun hc_h => absurd (@hc_h (1) (1)) (by
  simp)

-- Finset.mem_range_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.mem_range_le.h2 : ¬∀ {n x : ℕ}, x ≤ n := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- multiplicity_base_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.multiplicity_base_pow.h1 : ¬∀ {p : ℕ} (k : ℕ), multiplicity p (p ^ k) = k := fun hc_h => absurd (@hc_h (1) (1)) (by
  simp)

-- LT.lt.nat_succ_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.LT.lt.nat_succ_le.h2 : ¬∀ {n m : ℕ}, n.succ ≤ m := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- NNRat.num_mk, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNRat.num_mk.h1 : ¬∀ (q : ℚ), 0 ≤ q := fun hc_h => absurd (@hc_h (-1)) (by
  decide +kernel)

-- EReal.mul_top_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.mul_top_of_pos.h1 : ¬∀ {x : EReal}, x * ⊤ = ⊤ := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Nat.pow_left_injective, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_left_injective.h1 : ¬∀ {n : ℕ}, Function.Injective fun (a : ℕ) => a ^ n := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Bool.bool_eq_false, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.bool_eq_false.h1 : ¬∀ {b : Bool}, b = Bool.false := fun hc_h => absurd (@hc_h (Bool.true)) (by
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

-- Rat.den_inv_of_ne_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.den_inv_of_ne_zero.h1 : ¬∀ {q : ℚ}, q⁻¹.den = q.num.natAbs := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.nth_eq_orderIsoOfNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.nth_eq_orderIsoOfNat.h1 : ¬∀ {p : ℕ → Prop}, (Set.ofPred p).Infinite := fun hc_h => absurd (@hc_h (fun n => n = 0 : ℕ → Prop)) (by
  simp)

-- EReal.mul_bot_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.mul_bot_of_pos.h1 : ¬∀ {x : EReal}, x * ⊥ = ⊥ := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Fin.one_eq_mk_of_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.one_eq_mk_of_lt.h1 : ¬∀ {n : ℕ}, 1 < n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.gcdB_zero_right, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.gcdB_zero_right.h1 : ¬∀ {s : ℕ}, s.gcdB 0 = 0 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.prod_primeFactors_coe_pow_factorization, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prod_primeFactors_coe_pow_factorization.h1 : Not
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

-- Nat.minFac_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.minFac_le.h1 : ¬∀ {n : ℕ}, n.minFac ≤ n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Rat.toNNRat_of_nonpos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.toNNRat_of_nonpos.h1 : ¬∀ {q : ℚ}, q.toNNRat = 0 := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- Nat.le_three_of_sqrt_eq_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_three_of_sqrt_eq_one.h1 : ¬∀ {n : ℕ}, n ≤ 3 := fun hc_h => absurd (@hc_h (4)) (by
  decide +kernel)

-- EReal.mul_top_of_neg, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.mul_top_of_neg.h1 : ¬∀ {x : EReal}, x * ⊤ = ⊥ := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- EReal.top_sub, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.top_sub.h1 : ¬∀ {x : EReal}, ⊤ - x = ⊤ := fun hc_h => absurd (@hc_h (⊤)) (by
  decide +kernel)

-- Nat.Prime.one_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.one_le.h1 : ¬∀ {p : ℕ}, 1 ≤ p := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- WithZeroMulInt.toNNReal_strictMono, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.WithZeroMulInt.toNNReal_strictMono.h1 : ¬∀ {e : NNReal}, 1 < e := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Nat.Prime.ne_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.ne_one.h1 : ¬∀ {p : ℕ}, p ≠ 1 := fun hc_h => absurd (@hc_h (1)) (by
  decide +kernel)

-- PLift.instIsEmpty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PLift.instIsEmpty.h1 : ¬∀ {α : Type}, IsEmpty (PLift α) := fun hc_h => absurd (@hc_h (ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.false ({ down := 0 : PLift ℕ } : PLift ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.Prime.one_lt', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.one_lt'.h1 : ¬∀ (p : ℕ), Fact (1 < p) := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.Prime.primeFactors, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.primeFactors.h1 : ¬∀ {p : ℕ}, p.primeFactors = {p} := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Fin.eq_one_of_ne_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.eq_one_of_ne_zero.h1 : ¬∀ (i : Fin 2), i = 1 := fun hc_h => absurd (@hc_h ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- Fintype.card_ofIsEmpty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fintype.card_ofIsEmpty.h1 : ¬∀ {α : Type}, IsEmpty α := fun hc_h => absurd (@hc_h (ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.false (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fin.last_pos', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.last_pos'.h1 : ¬∀ {n : ℕ}, 0 < Fin.last n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Odd.intCast_zmod_two, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Odd.intCast_zmod_two.h1 : Not
      (∀ {n : Int},
        @Eq (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Int.cast (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@AddGroupWithOne.toIntCast (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Ring.toAddGroupWithOne (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@CommRing.toRing (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (ZMod.commRing (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            n)
          (@OfNat.ofNat (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 1)
            (@One.toOfNat1 (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddMonoidWithOne.toOne (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Ring.toAddGroupWithOne (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@CommRing.toRing (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (ZMod.commRing (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- Rat.inv_intCast_den_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.inv_intCast_den_of_pos.h1 : Not
      (∀ {a : Int},
        @Eq Int (@Nat.cast Int instNatCastInt (@Inv.inv Rat Rat.instInv (@Int.cast Rat Rat.instIntCast a)).den) a) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (by
  decide +kernel)

-- Nat.totient_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_lt.h1 : ¬∀ (n : ℕ), n.totient < n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.exists_eq_two_pow_mul_odd, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.exists_eq_two_pow_mul_odd.h1 : ¬∀ {n : ℕ}, ∃ (k : ℕ) (m : ℕ), Odd m ∧ n = 2 ^ k * m := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- NNRat.den_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.NNRat.den_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
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

-- BinaryTree.left_node_right_eq_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.BinaryTree.left_node_right_eq_self.h1 : ¬∀ {x : BinaryTree Unit}, BinaryTree.node () x.left x.right = x := fun hc_h => absurd (@hc_h (BinaryTree.nil)) (by
  decide +kernel)

-- List.IsChain.count_false_le_count_true_add_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.count_false_le_count_true_add_one.h1 : ¬∀ {l : List Bool}, List.count Bool.false l ≤ List.count Bool.true l + 1 := fun hc_h => absurd (@hc_h ([Bool.false, Bool.false])) (by
  decide +kernel)

-- Even.natCast_zmod_two, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Even.natCast_zmod_two.h1 : Not
      (∀ {n : Nat},
        @Eq (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Nat.cast (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@AddMonoidWithOne.toNatCast (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@AddGroupWithOne.toAddMonoidWithOne (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Ring.toAddGroupWithOne (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@CommRing.toRing (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (ZMod.commRing (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            n)
          (@OfNat.ofNat (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
            (@Zero.toOfNat0 (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@MulZeroClass.toZero (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@instMulZeroClassOfSemiring (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@CommSemiring.toSemiring (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@CommRing.toCommSemiring (ZMod (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (ZMod.commRing (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Nat.totient_eq_prod_factorization, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.totient_eq_prod_factorization.h1 : ¬∀ {n : ℕ}, n.totient = n.factorization.prod fun (p k : ℕ) => p ^ (k - 1) * (p - 1) := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Set.not_countable_univ, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.not_countable_univ.h1 : Not (∀ {α : Type}, Not (@Set.Countable α (@Set.univ α))) := fun hc_h => absurd (@hc_h (Bool)) (by
  simp)

-- ENat.mul_top, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.mul_top.h1 : ¬∀ {m : ℕ∞}, m * ⊤ = ⊤ := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- ZMod.val_one'', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ZMod.val_one''.h1 : Not
      (∀ {n : Nat},
        @Eq Nat
          (@ZMod.val n
            (@OfNat.ofNat (ZMod n) (nat_lit 1)
              (@One.toOfNat1 (ZMod n)
                (@AddMonoidWithOne.toOne (ZMod n)
                  (@AddGroupWithOne.toAddMonoidWithOne (ZMod n)
                    (@Ring.toAddGroupWithOne (ZMod n) (@CommRing.toRing (ZMod n) (ZMod.commRing n))))))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (by
  decide +kernel)

-- Rat.inv_natCast_den_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.inv_natCast_den_of_pos.h1 : Not (∀ {a : Nat}, @Eq Nat (@Inv.inv Rat Rat.instInv (@Nat.cast Rat Rat.instNatCast a)).den a) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- ENat.top_mul, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.top_mul.h1 : ¬∀ {m : ℕ∞}, ⊤ * m = ⊤ := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Set.subsingleton_univ, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Set.subsingleton_univ.h1 : Not (∀ {α : Type}, @Set.Subsingleton α (@Set.univ α)) := fun hc_h => absurd (@hc_h (Bool)) (by
  decide +kernel)

-- Fin.castSucc_zero', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.castSucc_zero'.h1 : ¬∀ {n : ℕ}, NeZero n := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENat.exists_nat_gt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.exists_nat_gt.h1 : ¬∀ {n : ℕ∞}, ∃ (m : ℕ), n < ↑m := fun hc_h => absurd (@hc_h (⊤)) (by
  simp)

-- PrimeMultiset.prod_ofNatList, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PrimeMultiset.prod_ofNatList.h1 : ¬∀ (l : List ℕ), ∀ p ∈ l, Nat.Prime p := fun hc_h => absurd (@hc_h ([0])) (by
  decide +kernel)

-- Int.alternating_sum_range_choose_of_ne, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.alternating_sum_range_choose_of_ne.h1 : Not
      (∀ {n : Nat},
        @Eq Int
          (∑
            m ∈
              Finset.range
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
            @HMul.hMul Int Int Int (@instHMul Int Int.instMul)
              (@HPow.hPow Int Nat Int (@instHPow Int Nat (@NPow.toPow Int (@Monoid.toNPow Int Int.instMonoid)))
                (@Neg.neg Int Int.instNegInt (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))) m)
              (@Nat.cast Int instNatCastInt (n.choose m)))
          (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) := fun hc_h => absurd (@hc_h (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (by
  decide +kernel)

-- Bool.eq_false_of_not_eq_true', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.eq_false_of_not_eq_true'.h1 : ¬∀ {a : Bool}, a = Bool.false := fun hc_h => absurd (@hc_h (Bool.true)) (by
  decide +kernel)

-- Nat.mul_factorial_pred, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mul_factorial_pred.h1 : ¬∀ {n : ℕ}, n * (n - 1).factorial = n.factorial := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.divisors_eq_image_Iic_factorization_prod_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.divisors_eq_image_Iic_factorization_prod_pow.h1 : ¬∀ {n : ℕ},
        n.divisors = Finset.image (fun (x : ℕ →₀ ℕ) => x.prod fun (x1 x2 : ℕ) => x1 ^ x2) (Finset.Iic n.factorization) := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- PNat.XgcdType.step_isSpecial, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.XgcdType.step_isSpecial.h1 : ¬∀ (u : PNat.XgcdType), u.step.IsSpecial := fun hc_h => absurd (@hc_h ({ wp := 0, x := 0, y := 0, zp := 1, ap := 0, bp := 0 : PNat.XgcdType })) (by
  nofun)

-- PNat.XgcdType.step_wf, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.XgcdType.step_wf.h1 : ¬∀ (u : PNat.XgcdType), SizeOf.sizeOf u.step < SizeOf.sizeOf u := fun hc_h => absurd (@hc_h ({ wp := 0, x := 0, y := 0, zp := 0, ap := 0, bp := 0 : PNat.XgcdType })) (by
  decide +kernel)

-- PNat.XgcdType.finish_v, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.PNat.XgcdType.finish_v.h1 : ¬∀ (u : PNat.XgcdType), u.finish.v = u.v := fun hc_h => absurd (@hc_h ({ wp := 0, x := 0, y := 0, zp := 0, ap := 0, bp := 1 : PNat.XgcdType })) (by
  decide +kernel)

-- Nat.two_le_centralBinom, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.two_le_centralBinom.h1 : ¬∀ (n : ℕ), 2 ≤ n.centralBinom := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.two_dvd_centralBinom_of_one_le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.two_dvd_centralBinom_of_one_le.h1 : ¬∀ {n : ℕ}, 2 ∣ n.centralBinom := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Squarefree.nodup_primeFactorsList, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Squarefree.nodup_primeFactorsList.h1 : ¬∀ {n : ℕ}, n.primeFactorsList.Nodup := fun hc_h => absurd (@hc_h (4)) (by
  decide +kernel)

-- Nat.centralBinom_lt_four_pow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.centralBinom_lt_four_pow.h1 : ¬∀ {n : ℕ}, n.centralBinom < 4 ^ n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.Prime.emultiplicity_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.emultiplicity_self.h1 : ¬∀ {p : ℕ}, emultiplicity p p = 1 := fun hc_h => absurd (@hc_h (1)) (by
  simp)

-- Nat.digits_zero_succ', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digits_zero_succ'.h1 : ¬∀ {n : ℕ}, Nat.digits 0 n = [n] := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Choose.primeFactors_gcd_choose_of_isPrimePow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.primeFactors_gcd_choose_of_isPrimePow.h1 : ¬∀ {n : ℕ}, ((Finset.Icc 1 (n - 1)).gcd n.choose).primeFactors = {n.minFac} := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- ENat.top_epow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.top_epow.h1 : Not
      (∀ {y : ENat},
        @Eq ENat (@HPow.hPow ENat ENat ENat (@instHPow ENat ENat ENat.instPow) (@Top.top ENat instTopENat) y)
          (@Top.top ENat instTopENat)) := fun hc_h => absurd (@hc_h (@OfNat.ofNat ENat (nat_lit 0) (@Zero.toOfNat0 ENat instZeroENat))) (by
  decide +kernel)

-- Nat.Prime.eq_two_or_odd, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.eq_two_or_odd.h1 : ¬∀ {p : ℕ}, p = 2 ∨ p % 2 = 1 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Finset.isEmpty_of_forall_eq_empty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Finset.isEmpty_of_forall_eq_empty.h1 : ¬∀ {α : Type}, IsEmpty α := fun hc_h => absurd (@hc_h (ℕ)) (by
  exact fun hc_c =>
    absurd (hc_c.false (0 : ℕ))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.digitsAux_zero, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.digitsAux_zero.h1 : ¬∀ (b : ℕ), 2 ≤ b := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Choose.minFac_dvd_gcd_choose_of_isPrimePow, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Choose.minFac_dvd_gcd_choose_of_isPrimePow.h1 : ¬∀ {n : ℕ}, n.minFac ∣ (Finset.Icc 1 (n - 1)).gcd n.choose := fun hc_h => absurd (@hc_h (6)) (by
  decide +kernel)

-- Nat.instAtLeastTwoHAddOfNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.instAtLeastTwoHAddOfNat.h1 : ¬∀ (n : ℕ), (n + 1).AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Rat.fract_inv_num_lt_num_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Rat.fract_inv_num_lt_num_of_pos.h1 : ¬∀ {q : ℚ}, (Int.fract q⁻¹).num < q.num := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.not_prime_iff_exists_dvd_lt, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_prime_iff_exists_dvd_lt.h1 : ¬∀ {n : ℕ}, ¬Nat.Prime n ↔ ∃ (m : ℕ), m ∣ n ∧ 2 ≤ m ∧ m < n := fun hc_h => absurd (@hc_h (0)) (by
  (simp <;> decide))

-- Nat.bitIndices_twoPowsum, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.bitIndices_twoPowsum.h1 : ¬∀ {L : List ℕ}, (List.map (fun (i : ℕ) => 2 ^ i) L).sum.bitIndices = L := fun hc_h => absurd (@hc_h ([1, 0])) (by
  decide +kernel)

-- Nat.floorRoot_one_right, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.floorRoot_one_right.h1 : ¬∀ {n : ℕ}, n.floorRoot 1 = 1 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- List.fixedLengthDigits_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.fixedLengthDigits_one.h1 : ¬∀ {b : ℕ}, 1 < b := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- ENat.top_sub_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.top_sub_ofNat.h1 : ¬∀ (a : ℕ), a.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- ENat.toNat_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.toNat_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.zeckendorf_of_pos, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.zeckendorf_of_pos.h1 : ¬∀ {n : ℕ}, n.zeckendorf = n.greatestFib :: (n - Nat.fib n.greatestFib).zeckendorf := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.divisors_filter_squarefree, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.divisors_filter_squarefree.h1 : ¬∀ {n : ℕ},
        {d ∈ n.divisors | Squarefree d}.val =
          Multiset.map (fun (x : Finset ℕ) => x.val.prod)
            (UniqueFactorizationMonoid.normalizedFactors n).toFinset.powerset.val := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Nat.zeckendorf_sum_fib, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.zeckendorf_sum_fib.h1 : ¬∀ {l : List ℕ}, (List.map Nat.fib l).sum.zeckendorf = l := fun hc_h => absurd (@hc_h ([0])) (by
  decide +kernel)

-- ENNReal.toEReal_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENNReal.toEReal_ofNat.h1 : ¬∀ (n : ℕ), n.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.squarefree_iff_nodup_primeFactorsList, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.squarefree_iff_nodup_primeFactorsList.h1 : ¬∀ {n : ℕ}, Squarefree n ↔ n.primeFactorsList.Nodup := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.Prime.even_iff, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.Prime.even_iff.h1 : ¬∀ {p : ℕ}, Even p ↔ p = 2 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.prod_primeFactors_of_squarefree, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prod_primeFactors_of_squarefree.h1 : ¬∀ {n : ℕ}, ∏ p ∈ n.primeFactors, p = n := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.sq_mul_squarefree_of_pos', hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.sq_mul_squarefree_of_pos'.h1 : ¬∀ {n : ℕ}, ∃ (a : ℕ) (b : ℕ), (b + 1) ^ 2 * (a + 1) = n ∧ Squarefree (a + 1) := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Bool.eq_false_of_not_eq_true, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Bool.eq_false_of_not_eq_true.h1 : ¬∀ {b : Bool}, b = Bool.false := fun hc_h => absurd (@hc_h (Bool.true)) (by
  decide +kernel)

-- ENat.top_ne_ofNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.top_ne_ofNat.h1 : ¬∀ (a : ℕ), a.AtLeastTwo := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.prop)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fin.instNontrivial, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.instNontrivial.h1 : ¬∀ {n : ℕ}, Nontrivial (Fin n) := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.exists_pair_ne)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.squarefree_iff_factorization_le_one, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.squarefree_iff_factorization_le_one.h1 : ¬∀ {n : ℕ}, Squarefree n ↔ ∀ (p : ℕ), n.factorization p ≤ 1 := fun hc_h => absurd (@hc_h (0)) (by
  simp)

-- Nat.pow_right_injective, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.pow_right_injective.h1 : ¬∀ {a : ℕ}, Function.Injective fun (x : ℕ) => a ^ x := fun hc_h => absurd (@hc_h (1)) (by
  simp)

-- EReal.top_add_of_ne_bot, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.EReal.top_add_of_ne_bot.h1 : ¬∀ {x : EReal}, ⊤ + x = ⊤ := fun hc_h => absurd (@hc_h (⊥)) (by
  decide +kernel)

-- padicValNat_base, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.padicValNat_base.h1 : ¬∀ {p : ℕ}, multiplicity p p = 1 := fun hc_h => absurd (@hc_h (1)) (by
  simp)

-- Nat.maxPowDvdDiv_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.maxPowDvdDiv_self.h1 : ¬∀ {p : ℕ}, p.maxPowDvdDiv p = (1, 1) := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- Nat.not_prime_iff_exists_mul_eq, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.not_prime_iff_exists_mul_eq.h1 : ¬∀ {n : ℕ}, ¬Nat.Prime n ↔ ∃ (a : ℕ) (b : ℕ), a < n ∧ b < n ∧ a * b = n := fun hc_h => absurd (@hc_h (0)) (by
  (simp <;> decide))

-- Nat.divMaxPow_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.divMaxPow_self.h1 : ¬∀ {p : ℕ}, p.divMaxPow p = 1 := fun hc_h => absurd (@hc_h (0)) (by
  decide +kernel)

-- ENat.sSup_eq_top_of_infinite, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ENat.sSup_eq_top_of_infinite.h1 : ¬∀ {s : Set ℕ∞}, SupSet.sSup s = ⊤ := fun hc_h => absurd (@hc_h (∅)) (by
  simp)

-- Nat.multiplicity_self, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.multiplicity_self.h1 : ¬∀ {p : ℕ}, multiplicity p p = 1 := fun hc_h => absurd (@hc_h (1)) (by
  simp)

-- Nat.instNeZeroNatAbsOfInt_mathlib, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.instNeZeroNatAbsOfInt_mathlib.h1 : ¬∀ (n : ℤ), NeZero n.natAbs := fun hc_h => absurd (@hc_h (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.prime_one_false, hypothesis 0: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.prime_one_false.h0 : ¬False := fun hc_h => absurd (@hc_h ) (by
  decide +kernel)

