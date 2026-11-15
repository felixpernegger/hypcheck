import Batteries
-- batteries port: Decidable instances for Batteries predicates (HypCheck `--dec-src`), so that the
-- counterexample search can evaluate them; elaborated after the imports and copied into proofs files.
noncomputable instance HypCheckDec.ltHeadKey {α β} (cmp : α → α → Ordering) (a : α)
    (t : Batteries.AssocList α β) : Decidable (Batteries.AssocList.LTHeadKey cmp a t) :=
  match t with
  | .nil => isTrue trivial
  | .cons x _ _ => (inferInstance : Decidable (cmp a x = .lt))
noncomputable instance HypCheckDec.keysOrdered {α β} (cmp : α → α → Ordering) (t : Batteries.AssocList α β) :
    Decidable (Batteries.AssocList.KeysOrdered cmp t) :=
  Batteries.AssocList.rec (motive := fun t => Decidable (Batteries.AssocList.KeysOrdered cmp t))
    (isTrue trivial)
    (fun a _ t ih => @instDecidableAnd (Batteries.AssocList.LTHeadKey cmp a t) _ inferInstance ih) t
noncomputable instance HypCheckDec.olLTHeadKey {α β} (cmp : α → α → Ordering) (a : α)
    (l : Batteries.OrderedAssocList cmp β) : Decidable (l.LTHeadKey a) :=
  HypCheckDec.ltHeadKey cmp a l.toAssocList
noncomputable instance HypCheckDec.iterValidFor (l r : List Char) (it : String.Legacy.Iterator) :
    Decidable (String.Legacy.Iterator.ValidFor l r it) :=
  decidable_of_iff (it.s = String.ofList (l.reverseAux r) ∧ it.i = ⟨String.utf8Len l⟩)
    ⟨fun ⟨h1, h2⟩ => by cases it; cases h1; cases h2; exact .mk, fun h => by cases h; exact ⟨rfl, rfl⟩⟩
noncomputable instance HypCheckDec.substrValidFor (l m r : List Char) (s : Substring.Raw) :
    Decidable (Substring.Raw.ValidFor l m r s) :=
  decidable_of_iff (s.str = String.ofList (l ++ m ++ r) ∧ s.startPos = ⟨String.utf8Len l⟩ ∧
      s.stopPos = ⟨String.utf8Len l + String.utf8Len m⟩)
    ⟨fun ⟨h1, h2, h3⟩ => by cases s; cases h1; cases h2; cases h3; exact .mk,
     fun h => by cases h; exact ⟨rfl, rfl, rfl⟩⟩
noncomputable instance HypCheckDec.binHeapWF {α} [Ord α] (h : Batteries.BinaryHeap α) :
    Decidable h.WF :=
  inferInstanceAs (Decidable (∀ i : Fin h.size, (∀ _ : 2 * i.val + 1 < h.size,
    (compare h.vector[i] h.vector[2 * i.val + 1]).isGE) ∧ (∀ _ : 2 * i.val + 1 + 1 < h.size,
    (compare h.vector[i] h.vector[2 * i.val + 1 + 1]).isGE)))
noncomputable instance HypCheckDec.pairingNoSibling {α} (s : Batteries.PairingHeapImp.Heap α) :
    Decidable s.NoSibling :=
  match s with
  | .nil => isTrue .nil
  | .node a c .nil => isTrue (.node a c)
  | .node _ _ (.node _ _ _) => isFalse (fun h => by cases h)


/-! Proofs emitted by HypCheck.lean (Lean 4.36.0-rc2). -/

-- Batteries.OrderedAssocList.merge_assoc, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.merge_assoc.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {β₁ β₂ γ₁ β₃ ε γ₂ : Type}
        (f₁ : α → Option β₁ → Option β₂ → Option γ₁) (f₂ : α → Option γ₁ → Option β₃ → Option ε)
        (g₁ : α → Option β₂ → Option β₃ → Option γ₂) (g₂ : α → Option β₁ → Option γ₂ → Option ε),
        (∀ (a : α), f₁ a Option.none Option.none = Option.none) →
          (∀ (a : α), f₂ a Option.none Option.none = Option.none) →
            (∀ (a : α), g₁ a Option.none Option.none = Option.none) →
              (∀ (a : α), g₂ a Option.none Option.none = Option.none) →
                (∀ (a : α) (x : Option β₁) (y : Option β₂) (z : Option β₃), f₂ a (f₁ a x y) z = g₂ a x (g₁ a y z)) →
                  ∀ (l₁ : Batteries.OrderedAssocList cmp β₁) (l₂ : Batteries.OrderedAssocList cmp β₂)
                    (l₃ : Batteries.OrderedAssocList cmp β₃), Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) (Nat) (Nat) (Nat) (Nat) (Nat) (fun (a : Bool) (a_1 a_2 : Option Nat) => Option.none) (fun (a : Bool) (a_1 a_2 : Option Nat) => Option.none) (fun (a : Bool) (a_1 a_2 : Option Nat) => Option.none) (fun (a : Bool) (a_1 a_2 : Option Nat) => Option.none) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  simp) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (x x_1 : Bool) => Ordering.eq) Nat }) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (x x_1 : Bool) => Ordering.eq) Nat }) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (x x_1 : Bool) => Ordering.eq) Nat })) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_compare (a := (Bool.false : Bool)) (b := (Bool.true : Bool))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.AssocList.KeysOrdered.orderedInsert_aux, hypothesis 10: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Batteries.AssocList.KeysOrdered.orderedInsert_aux.h10.inst : ¬Batteries.AssocList.KeysOrdered (fun (a b : Nat) => Ord.compare a b)
        (Batteries.AssocList.cons 0 0
          (Batteries.AssocList.orderedInsert (fun (a b : Nat) => Ord.compare a b)
            (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) 1 0)) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Batteries.AssocList.KeysOrdered.orderedInsert_aux.h10.prem0 : (fun (a b : Nat) => Ord.compare a b) 1 0 = Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Batteries.AssocList.KeysOrdered.orderedInsert_aux.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {b : β} [inst : Std.LawfulEqCmp cmp]
        [inst : Std.OrientedCmp cmp] {x : α} {y : β} {t : Batteries.AssocList α β},
        cmp a x = Ordering.gt →
          Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y (Batteries.AssocList.orderedInsert cmp t a b)) := fun hc_h => HypCheckProof.Batteries.AssocList.KeysOrdered.orderedInsert_aux.h10.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (1) (Nat) (0) _ _ (0) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) HypCheckProof.Batteries.AssocList.KeysOrdered.orderedInsert_aux.h10.prem0)

-- Batteries.AssocList.KeysOrdered.orderedInsert_aux, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.KeysOrdered.orderedInsert_aux.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {b : β} [inst : Std.LawfulEqCmp cmp]
        [inst : Std.OrientedCmp cmp] {x : α} {y : β} {t : Batteries.AssocList α β},
        Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y t) →
          Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y (Batteries.AssocList.orderedInsert cmp t a b)) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (0) (Nat) (0) _ _ (0) (0) (Batteries.AssocList.nil) (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.orderedFind?_filterMapVal, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.orderedFind?_filterMapVal.h6 : ¬∀ {α β α_1 : Type} {f : α → β → Option α_1} {a : α} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp]
        {l : Batteries.AssocList α β},
        Batteries.AssocList.KeysOrdered cmp l →
          Batteries.AssocList.orderedFind? cmp (Batteries.AssocList.filterMapVal f l) a =
            (Batteries.AssocList.orderedFind? cmp l a).bind fun (b : β) => f a b := fun hc_h => absurd (@hc_h (Bool) (Nat) (Nat) (fun (a : Bool) => if a = Bool.false then fun (x : Nat) => Option.none else Option.some) (Bool.false) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Batteries.AssocList.cons Bool.true 0 Batteries.AssocList.nil) (by
  decide)) (by
  decide +kernel)

-- List.Perm.diff, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.diff.h7 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l₁ l₂ t₁ t₂ : List α}, t₁.Perm t₂ → (l₁.diff t₁).Perm (l₂.diff t₂) := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([0]) ([]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.Perm.diff, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.diff.h8 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l₁ l₂ t₁ t₂ : List α}, l₁.Perm l₂ → (l₁.diff t₁).Perm (l₂.diff t₂) := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([0]) ([0]) ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.Perm.union, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.union.h2 : ¬∀ {α : Type} [inst : BEq α] {l₁ l₂ t₁ t₂ : List α}, l₁.Perm l₂ → t₁.Perm t₂ → (l₁ ∪ t₁).Perm (l₂ ∪ t₂) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0, 1]) ([1, 0]) ([]) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.Perm.union, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.union.h7 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l₁ l₂ t₁ t₂ : List α}, t₁.Perm t₂ → (l₁ ∪ t₁).Perm (l₂ ∪ t₂) := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([0]) ([]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.Perm.union, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.union.h8 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l₁ l₂ t₁ t₂ : List α}, l₁.Perm l₂ → (l₁ ∪ t₁).Perm (l₂ ∪ t₂) := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([]) ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- Std.TransCmp.gt_of_ge_of_gt, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h2.inst : ¬(fun (a b : Nat) => if a % 3 = b % 3 then Ordering.eq else if (a + 1) % 3 = b % 3 then Ordering.lt else Ordering.gt) 0
          1 =
        Ordering.gt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h2.prem0 : (fun (a b : Nat) => if a % 3 = b % 3 then Ordering.eq else if (a + 1) % 3 = b % 3 then Ordering.lt else Ordering.gt) 0
        2 ≠
      Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h2.prem1 : (fun (a b : Nat) => if a % 3 = b % 3 then Ordering.eq else if (a + 1) % 3 = b % 3 then Ordering.lt else Ordering.gt) 2
        1 =
      Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} {x y z : α},
        cmp x y ≠ Ordering.lt → cmp y z = Ordering.gt → cmp x z = Ordering.gt := fun hc_h => HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h2.inst (@hc_h (Nat) (fun (a b : Nat) => if a % 3 = b % 3 then Ordering.eq else if (a + 1) % 3 = b % 3 then Ordering.lt else Ordering.gt) (0) (2) (1) HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h2.prem0 HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h2.prem1)

-- Std.TransCmp.gt_of_ge_of_gt, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h6.inst : ¬(fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.gt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h6.prem0 : (fun (a b : Nat) => Ord.compare a b) 1 0 = Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {x y z : α},
        cmp y z = Ordering.gt → cmp x z = Ordering.gt := fun hc_h => HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h6.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (0) (1) (0) HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h6.prem0)

-- Std.TransCmp.gt_of_ge_of_gt, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h7.inst : ¬(fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.gt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h7.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 ≠ Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {x y z : α},
        cmp x y ≠ Ordering.lt → cmp x z = Ordering.gt := fun hc_h => HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (0) (0) (0) HypCheckProof.Std.TransCmp.gt_of_ge_of_gt.h7.prem0)

-- Std.TransCmp.ge_trans, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.ge_trans.h2.inst : ¬(fun (a b : Nat) => if a % 3 = b % 3 then Ordering.eq else if (a + 1) % 3 = b % 3 then Ordering.lt else Ordering.gt) 0
          1 ≠
        Ordering.lt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.ge_trans.h2.prem0 : (fun (a b : Nat) => if a % 3 = b % 3 then Ordering.eq else if (a + 1) % 3 = b % 3 then Ordering.lt else Ordering.gt) 0
        2 ≠
      Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.ge_trans.h2.prem1 : (fun (a b : Nat) => if a % 3 = b % 3 then Ordering.eq else if (a + 1) % 3 = b % 3 then Ordering.lt else Ordering.gt) 2
        1 ≠
      Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.ge_trans.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} {x y z : α},
        cmp x y ≠ Ordering.lt → cmp y z ≠ Ordering.lt → cmp x z ≠ Ordering.lt := fun hc_h => HypCheckProof.Std.TransCmp.ge_trans.h2.inst (@hc_h (Nat) (fun (a b : Nat) => if a % 3 = b % 3 then Ordering.eq else if (a + 1) % 3 = b % 3 then Ordering.lt else Ordering.gt) (0) (2) (1) HypCheckProof.Std.TransCmp.ge_trans.h2.prem0 HypCheckProof.Std.TransCmp.ge_trans.h2.prem1)

-- Std.TransCmp.ge_trans, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.ge_trans.h6.inst : ¬(fun (a b : Nat) => Ord.compare a b) 0 1 ≠ Ordering.lt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.ge_trans.h6.prem0 : (fun (a b : Nat) => Ord.compare a b) 1 1 ≠ Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.ge_trans.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {x y z : α},
        cmp y z ≠ Ordering.lt → cmp x z ≠ Ordering.lt := fun hc_h => HypCheckProof.Std.TransCmp.ge_trans.h6.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (0) (1) (1) HypCheckProof.Std.TransCmp.ge_trans.h6.prem0)

-- Std.TransCmp.ge_trans, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.ge_trans.h7.inst : ¬(fun (a b : Nat) => Ord.compare a b) 0 1 ≠ Ordering.lt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.ge_trans.h7.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 ≠ Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.ge_trans.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {x y z : α},
        cmp x y ≠ Ordering.lt → cmp x z ≠ Ordering.lt := fun hc_h => HypCheckProof.Std.TransCmp.ge_trans.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (0) (0) (1) HypCheckProof.Std.TransCmp.ge_trans.h7.prem0)

-- List.Subperm.cons_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.cons_left.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α],
        l₁.Subperm l₂ → ∀ (x : α), List.count x l₁ < List.count x l₂ → (x :: l₁).Subperm l₂ := fun hc_h => absurd (@hc_h (Nat) ([]) ([0]) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (by
  decide) (1) (by
  decide)) (by
  decide +kernel)

-- List.Subperm.cons_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.cons_left.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] (x : α),
        List.count x l₁ < List.count x l₂ → (x :: l₁).Subperm l₂ := fun hc_h => absurd (@hc_h (Nat) ([1]) ([0]) (instBEqOfDecidableEq) _ (0) (by
  decide)) (by
  decide +kernel)

-- List.Subperm.cons_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.cons_left.h7 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] [inst : LawfulBEq α], l₁.Subperm l₂ → ∀ (x : α), (x :: l₁).Subperm l₂ := fun hc_h => absurd (@hc_h (Nat) ([]) ([]) (instBEqOfDecidableEq) _ (by
  decide) (0)) (by
  decide +kernel)

-- List.getElem_partialSums, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_partialSums.h7 : ¬∀ {α : Type} {i : Nat} [inst : Add α] [inst_1 : Zero α] [inst_2 : Std.Associative fun (x1 x2 : α) => x1 + x2]
        [inst_3 : Std.LawfulIdentity (fun (x1 x2 : α) => x1 + x2) 0] {l : List α}, i < l.partialSums.length := fun hc_h => absurd (@hc_h (Nat) (1) (instAddNat) (Zero.ofOfNat0) _ _ ([])) (by
  decide +kernel)

-- List.Subperm.diff_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.diff_right.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α], l₁.Subperm l₂ → ∀ (t : List α), (l₁.diff t).Subperm (l₂.diff t) := fun hc_h => absurd (@hc_h (Nat) ([0]) ([0, 1]) (⟨fun a b => a ≤ b⟩ : BEq Nat) (by
  decide) ([1])) (by
  decide +kernel)

-- List.Subperm.diff_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.diff_right.h5 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] (t : List α), (l₁.diff t).Subperm (l₂.diff t) := fun hc_h => absurd (@hc_h (Nat) ([0]) ([]) (instBEqOfDecidableEq) _ ([])) (by
  decide +kernel)

-- List.Subperm.getElem_idxInj_eq_getElem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.getElem_idxInj_eq_getElem.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α}, xs.Subperm ys → ∀ {i : Fin xs.length}, LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) ([0]) (by
  decide) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_beq (a := (0 : Nat)) (b := (1 : Nat))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Subperm.getElem_idxInj_eq_getElem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.getElem_idxInj_eq_getElem.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {xs ys : List α} {i : Fin xs.length}, xs.Subperm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([0]) ([]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Perm.idxBij_symm_idxBij, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_symm_idxBij.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α}, xs.Perm ys → ∀ {i : Fin xs.length}, LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) ([0]) (by
  decide) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_beq (a := (0 : Nat)) (b := (1 : Nat))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Perm.idxBij_symm_idxBij, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_symm_idxBij.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {xs ys : List α} {i : Fin xs.length}, xs.Perm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([0]) ([]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Subperm.erase, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.erase.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] (a : α), l₁.Subperm l₂ → (l₁.erase a).Subperm (l₂.erase a) := fun hc_h => absurd (@hc_h (Nat) ([0, 1]) ([1, 0]) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) (by
  decide)) (by
  decide +kernel)

-- List.Subperm.erase, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.erase.h6 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] (a : α), (l₁.erase a).Subperm (l₂.erase a) := fun hc_h => absurd (@hc_h (Nat) ([0]) ([]) (instBEqOfDecidableEq) _ (1)) (by
  decide +kernel)

-- List.idxOfNth_countBefore_of_lt_length_of_beq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_countBefore_of_lt_length_of_beq.h5 : ¬∀ {α : Type} {i : Nat} {x : α} [inst : BEq α] {xs : List α}, i < xs.length := fun hc_h => absurd (@hc_h (Nat) (0) (0) (instBEqOfDecidableEq) ([])) (by
  decide +kernel)

-- List.idxOfNth_countBefore_of_lt_length_of_beq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_countBefore_of_lt_length_of_beq.h6 : ¬∀ {α : Type} {i : Nat} {x : α} [inst : BEq α] {xs : List α} {h : i < xs.length},
        List.idxOfNth x xs (List.countBefore x xs i) = i := fun hc_h => absurd (@hc_h (Nat) (0) (0) (instBEqOfDecidableEq) ([1]) (by
  decide)) (by
  decide +kernel)

-- List.Perm.union_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.union_right.h4 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] (t₁ : List α), l₁.Perm l₂ → (l₁ ∪ t₁).Perm (l₂ ∪ t₁) := fun hc_h => absurd (@hc_h (Nat) ([0, 1]) ([1, 0]) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) (by
  decide)) (by
  decide +kernel)

-- List.Perm.union_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.union_right.h6 : ¬∀ {α : Type} {l₁ l₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] (t₁ : List α), (l₁ ∪ t₁).Perm (l₂ ∪ t₁) := fun hc_h => absurd (@hc_h (Nat) ([]) ([0]) (instBEqOfDecidableEq) _ ([])) (by
  decide +kernel)

-- List.Perm.getElem_idxBij_symm_eq_getElem, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.getElem_idxBij_symm_eq_getElem.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α}, xs.Perm ys → ∀ (i : Fin ys.length), LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) ([0]) (by
  decide) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_beq (a := (0 : Nat)) (b := (1 : Nat))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Perm.getElem_idxBij_symm_eq_getElem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.getElem_idxBij_symm_eq_getElem.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {xs ys : List α} (i : Fin ys.length), xs.Perm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([0]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Perm.inter_left, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.inter_left.h6 : ¬∀ {α : Type} {t₁ t₂ : List α} [inst : BEq α] [inst_1 : LawfulBEq α] (l : List α), l ∩ t₁ = l ∩ t₂ := fun hc_h => absurd (@hc_h (Nat) ([]) ([0]) (instBEqOfDecidableEq) _ ([0])) (by
  decide +kernel)

-- Batteries.UnionFind.equiv_link, hypothesis 6: necessary
/- FAILED: 2:275: Application type mismatch: The argument
  ⟨1, ⋯⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h 0 0 (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨1, of_decide_eq_true (id (Eq.refl true))⟩ | 5:295: Application type mismatch: The argument
  ⟨1, ⋯⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h 0 0 (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨1, of_decide_eq_true (id (Eq.refl true))⟩ | 2:275: Application type mismatch: The argument
  ⟨1, ?m.23⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h 0 0 (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨1, ?m.23⟩ | 5:295: Application type mismatch: The argument
  ⟨1, ?m.8⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h 0 0 (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨1, ?m.8⟩ | 9:299: Application type mismatch: The argument
  ⟨1, ⋯⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h 0 0 (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨1, of_decide_eq_true (id (Eq.refl true))⟩ | 9:12: Application type mismatch: The argument
  ⟨0, ⋯⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  ↑⟨0, ⋯⟩ | 7:299: Application type mismatch: The argument
  ⟨1, ?m.21⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h 0 0 (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨1, ?m.21⟩ | 9:12: Application type mismatch: The argument
  ⟨0, ?m.1⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  ↑⟨0, ?m.1⟩
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.equiv_link.h6 : ¬∀ {a b : Nat} {self : Batteries.UnionFind} {x y : Fin self.size}, self.parent ↑x = ↑x → self.parent ↑y = ↑y := fun hc_h => absurd (@hc_h (0) (0) (Batteries.UnionFind.empty.push.push.union! 0 1 : Batteries.UnionFind) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide +kernel)) (by
  decide +kernel)
-/

-- Fin.eq_false_of_find?_eq_some_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.eq_false_of_find?_eq_some_of_lt.h3 : ¬∀ {n : Nat} {i : Fin n} {p : Fin n → Bool} (j : Fin n), j < i → p j = Bool.false := fun hc_h => absurd (@hc_h (2) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (fun (a : Fin 2) => Bool.true) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.eq_false_of_find?_eq_some_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.eq_false_of_find?_eq_some_of_lt.h5 : ¬∀ {n : Nat} {i : Fin n} {p : Fin n → Bool}, Fin.find? p = Option.some i → ∀ (j : Fin n), p j = Bool.false := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (fun (a : Fin 1) => Bool.true) (by
  decide) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.Perm.idxBij_leftInverse_idxBij_symm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_leftInverse_idxBij_symm.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α}, xs.Perm ys → LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) ([]) (by
  decide)) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_beq (a := (0 : Nat)) (b := (1 : Nat))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Perm.idxBij_leftInverse_idxBij_symm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_leftInverse_idxBij_symm.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {xs ys : List α}, xs.Perm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([0])) (by
  decide +kernel)

-- List.getElem_swap_left_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_swap_left_of_lt.h4 : ¬∀ {α : Type} {xs : List α} {i j : Nat}, i < (xs.swap i j).length → j < xs.length := fun hc_h => absurd (@hc_h (Nat) ([0]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.getElem_swap_left_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_swap_left_of_lt.h5 : ¬∀ {α : Type} {xs : List α} {i j : Nat}, j < xs.length → i < (xs.swap i j).length := fun hc_h => absurd (@hc_h (Nat) ([0]) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.countPBefore_lt_countP_of_lt_length_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countPBefore_lt_countP_of_lt_length_of_pos.h4 : ¬∀ {α : Type} {i : Nat} {p : α → Bool} {xs : List α}, i < xs.length := fun hc_h => absurd (@hc_h (Nat) (0) (fun n => n % 2 == 0 : Nat → Bool) ([])) (by
  decide +kernel)

-- List.countPBefore_lt_countP_of_lt_length_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countPBefore_lt_countP_of_lt_length_of_pos.h5 : ¬∀ {α : Type} {i : Nat} {p : α → Bool} {xs : List α} {h : i < xs.length}, List.countPBefore p xs i < List.countP p xs := fun hc_h => absurd (@hc_h (Nat) (0) (fun n => n % 2 == 0 : Nat → Bool) ([1]) (by
  decide)) (by
  decide +kernel)

-- Batteries.BinaryHeap.insertExtractMax_wf, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.insertExtractMax_wf.h5 : ¬∀ {α : Type} {x : α} [inst : Ord α] [inst_1 : Std.TransOrd α] {heap : Batteries.BinaryHeap α},
        (heap.insertExtractMax x).snd.WF := fun hc_h => absurd (@hc_h (Nat) (0) (instOrdNat) _ ({ arr := #[0, 1] : Batteries.BinaryHeap Nat })) (by
  decide +kernel)

-- List.getElem_swap_right_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_swap_right_of_lt.h4 : ¬∀ {α : Type} {xs : List α} {i j : Nat}, j < (xs.swap i j).length → i < xs.length := fun hc_h => absurd (@hc_h (Nat) ([0]) (1) (0) (by
  decide)) (by
  decide +kernel)

-- List.getElem_swap_right_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_swap_right_of_lt.h5 : ¬∀ {α : Type} {xs : List α} {i j : Nat}, i < xs.length → j < (xs.swap i j).length := fun hc_h => absurd (@hc_h (Nat) ([0]) (0) (1) (by
  decide)) (by
  decide +kernel)

-- List.mem_idxsOf_getElem, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_idxsOf_getElem.h4 : ¬∀ {α : Type} {i : Nat} {xs : List α} [inst : BEq α] (h : i < xs.length), i ∈ List.idxsOf xs[i] xs := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (0) ([0]) (⟨fun a b => a != b⟩ : BEq Nat) hc_k0) (by
  decide +kernel)

-- List.mem_idxsOf_getElem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_idxsOf_getElem.h5 : ¬∀ {α : Type} {i : Nat} {xs : List α} [inst : BEq α] [inst : EquivBEq α], i < xs.length := fun hc_h => absurd (@hc_h (Nat) (0) ([]) (instBEqOfDecidableEq) _) (by
  decide +kernel)

-- List.Perm.subperm_idxBij, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.subperm_idxBij.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α}, xs.Perm ys → ReflBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a != b⟩ : BEq Nat) ([]) ([]) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.rfl (a := (0 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Perm.subperm_idxBij, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.subperm_idxBij.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : ReflBEq α] {xs ys : List α}, xs.Perm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([0])) (by
  decide +kernel)

-- List.disjoint_of_subset_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.disjoint_of_subset_right.h4 : ¬∀ {α : Type} {l₂ l l₁ : List α}, l₁.Disjoint l → l₁.Disjoint l₂ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([]) ([0]) (by
  simp)) (by
  simp)

-- List.disjoint_of_subset_right, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.disjoint_of_subset_right.h5 : ¬∀ {α : Type} {l₂ l l₁ : List α}, l₂ ⊆ l → l₁.Disjoint l₂ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([0]) ([0]) (by
  decide)) (by
  simp)

-- List.IsChain.imp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.imp.h4 : ¬∀ {α : Type} {R S : α → α → Prop} {l : List α}, List.IsChain R l → List.IsChain S l := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (fun a b => a = b : Nat → Nat → Prop) ([0, 1]) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.imp, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.imp.h5 : ¬∀ {α : Type} {R S : α → α → Prop} {l : List α}, (∀ ⦃a b : α⦄, R a b → S a b) → List.IsChain S l := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (fun a b => a < b : Nat → Nat → Prop) ([1, 0]) (by
  simp)) (by
  decide +kernel)

-- Nat.add_mul_lt_mul_of_lt_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_mul_lt_mul_of_lt_of_lt.h4 : ¬∀ {m n x y : Nat}, y < n → x + m * y < m * n := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.add_mul_lt_mul_of_lt_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.add_mul_lt_mul_of_lt_of_lt.h5 : ¬∀ {m n x y : Nat}, x < m → x + m * y < m * n := fun hc_h => absurd (@hc_h (1) (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- List.idxOfNth_countBefore_getElem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_countBefore_getElem.h3 : ¬∀ {α : Type} {i : Nat} [inst : BEq α] {xs : List α} {h : i < xs.length},
        List.idxOfNth xs[i] xs (List.countBefore xs[i] xs i) = i := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (0) (⟨fun a b => a != b⟩ : BEq Nat) ([0]) hc_k0) (by
  decide +kernel)

-- List.idxOfNth_countBefore_getElem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_countBefore_getElem.h5 : ¬∀ {α : Type} {i : Nat} [inst : BEq α] [inst : ReflBEq α] {xs : List α}, i < xs.length := fun hc_h => absurd (@hc_h (Nat) (0) (instBEqOfDecidableEq) _ ([])) (by
  decide +kernel)

-- List.Perm.idxBij_symm_rightInverse_idxBij, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_symm_rightInverse_idxBij.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α}, xs.Perm ys → LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) ([]) (by
  decide)) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_beq (a := (0 : Nat)) (b := (1 : Nat))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Perm.idxBij_symm_rightInverse_idxBij, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_symm_rightInverse_idxBij.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {xs ys : List α}, xs.Perm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([0])) (by
  decide +kernel)

-- List.Perm.idxBij_surjective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_surjective.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α}, xs.Perm ys → LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) ([]) (by
  decide)) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_beq (a := (0 : Nat)) (b := (1 : Nat))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Perm.idxBij_surjective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_surjective.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {xs ys : List α}, xs.Perm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([0])) (by
  decide +kernel)

-- List.disjoint_of_subset_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.disjoint_of_subset_left.h4 : ¬∀ {α : Type} {l₁ l l₂ : List α}, l.Disjoint l₂ → l₁.Disjoint l₂ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([]) ([0]) (by
  simp)) (by
  simp)

-- List.disjoint_of_subset_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.disjoint_of_subset_left.h5 : ¬∀ {α : Type} {l₁ l l₂ : List α}, l₁ ⊆ l → l₁.Disjoint l₂ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([0]) ([0]) (by
  decide)) (by
  simp)

-- Batteries.AssocList.instLawfulBEq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.instLawfulBEq.h3 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : BEq β] [inst_2 : LawfulBEq β], LawfulBEq (Batteries.AssocList α β) := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => a != b⟩ : BEq Nat) (instBEqOfDecidableEq) _) (by
  exact fun hc_c =>
    absurd
      (hc_c.toReflBEq.rfl (a := (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil : Batteries.AssocList Nat Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.AssocList.instLawfulBEq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.instLawfulBEq.h5 : ¬∀ {α β : Type} [inst : BEq α] [inst_1 : LawfulBEq α] [inst_2 : BEq β], LawfulBEq (Batteries.AssocList α β) := fun hc_h => absurd (@hc_h (Nat) (Nat) (instBEqOfDecidableEq) _ (⟨fun a b => a != b⟩ : BEq Nat)) (by
  exact fun hc_c =>
    absurd
      (hc_c.toReflBEq.rfl (a := (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil : Batteries.AssocList Nat Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Vector.uget_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.uget_mk.h3 : ¬∀ {α : Type} {n : Nat} (a : Array α) (i : USize), i.toNat < n → a.size = n := fun hc_h => absurd (@hc_h (Nat) (1) (#[]) (USize.ofNat 0) (by
  decide)) (by
  decide +kernel)

-- Vector.uget_mk, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.uget_mk.h5 : ¬∀ {α : Type} {n : Nat} (a : Array α), a.size = n → ∀ (i : USize), i.toNat < n := fun hc_h => absurd (@hc_h (Nat) _ (#[]) rfl (USize.ofNat 0)) (by
  decide +kernel)

-- List.Perm.idxBij_symm_leftInverse_idxBij, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_symm_leftInverse_idxBij.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α}, xs.Perm ys → LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) ([]) (by
  decide)) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_beq (a := (0 : Nat)) (b := (1 : Nat))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Perm.idxBij_symm_leftInverse_idxBij, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_symm_leftInverse_idxBij.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {xs ys : List α}, xs.Perm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([0])) (by
  decide +kernel)

-- Nat.mul_add_lt_mul_of_lt_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mul_add_lt_mul_of_lt_of_lt.h4 : ¬∀ {m n x y : Nat}, y < n → n * x + y < m * n := fun hc_h => absurd (@hc_h (0) (1) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Nat.mul_add_lt_mul_of_lt_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.mul_add_lt_mul_of_lt_of_lt.h5 : ¬∀ {m n x y : Nat}, x < m → n * x + y < m * n := fun hc_h => absurd (@hc_h (1) (0) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Batteries.PairingHeapImp.Heap.size_merge, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.PairingHeapImp.Heap.size_merge.h4 : ¬∀ {α : Type} (le : α → α → Bool) {s₁ s₂ : Batteries.PairingHeapImp.Heap α},
        s₂.NoSibling → (Batteries.PairingHeapImp.Heap.merge le s₁ s₂).size = s₁.size + s₂.size := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (Batteries.PairingHeapImp.Heap.node 0 Batteries.PairingHeapImp.Heap.nil
      (Batteries.PairingHeapImp.Heap.node 0 Batteries.PairingHeapImp.Heap.nil Batteries.PairingHeapImp.Heap.nil)) (Batteries.PairingHeapImp.Heap.nil) (by
  decide)) (by
  decide +kernel)

-- Batteries.PairingHeapImp.Heap.size_merge, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.PairingHeapImp.Heap.size_merge.h5 : ¬∀ {α : Type} (le : α → α → Bool) {s₁ s₂ : Batteries.PairingHeapImp.Heap α},
        s₁.NoSibling → (Batteries.PairingHeapImp.Heap.merge le s₁ s₂).size = s₁.size + s₂.size := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (Batteries.PairingHeapImp.Heap.nil) (Batteries.PairingHeapImp.Heap.node 0 Batteries.PairingHeapImp.Heap.nil
      (Batteries.PairingHeapImp.Heap.node 0 Batteries.PairingHeapImp.Heap.nil Batteries.PairingHeapImp.Heap.nil)) (by
  decide)) (by
  decide +kernel)

-- Substring.Raw.Valid.get, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.get.h5 : ¬∀ {m₁ : List Char} {c : Char} {m₂ : List Char} {s : Substring.Raw},
        s.Valid → s.get { byteIdx := String.utf8Len m₁ : String.Pos.Raw } = c := fun hc_h => absurd (@hc_h ([]) ('a') ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) ((@Substring.Raw.Valid.mk ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   decide)))) (by
  decide +kernel)

-- Vector.toArray_scanlM, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.toArray_scanlM.h6 : ¬∀ {m : Type → Type} {β α : Type} {n : Nat} {init : β} [inst : Monad m] {f : β → α → m β} {as : Vector α n},
        Vector.toArray <$> Vector.scanlM f init as = Array.scanlM f init as.toArray := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) (0) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (#v[])) (by
  decide +kernel)

-- Vector.scanlM_pure, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.scanlM_pure.h6 : Not
      (∀ {m : Type → Type} {β α : Type} {n : Nat} {init : β} [inst : Monad m] {f : β → α → β} {as : Vector α n},
        @Eq
          (m
            (Vector β
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@Vector.scanlM m β α n inst
            (fun (x1 : β) (x2 : α) => @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) β (f x1 x2)) init
            as)
          (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
            (Vector β
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Vector.scanl β α n f init as))) := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ({ pure := some, bind := fun _ _ => none } : Monad Option) (fun a b => a - b : Nat → Nat → Nat) (@Vector.mk Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))
      (@of_decide_eq_true
        (@Eq Nat
          (@Array.size Nat
            (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (instDecidableEqNat
          (@Array.size Nat
            (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Eq Nat
                (@Array.size Nat
                  (@List.toArray Nat
                    (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (instDecidableEqNat
                (@Array.size Nat
                  (@List.toArray Nat
                    (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Vector.scanrM_pure, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.scanrM_pure.h6 : Not
      (∀ {m : Type → Type} {α β : Type} {n : Nat} {init : β} [inst : Monad m] {f : α → β → β} {as : Vector α n},
        @Eq
          (m
            (Vector β
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@Vector.scanrM m α β n inst
            (fun (x1 : α) (x2 : β) => @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) β (f x1 x2)) init
            as)
          (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst))
            (Vector β
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Vector.scanr α β n f init as))) := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ({ pure := some, bind := fun _ _ => none } : Monad Option) (fun a b => a - b : Nat → Nat → Nat) (@Vector.mk Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))
      (@of_decide_eq_true
        (@Eq Nat
          (@Array.size Nat
            (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (instDecidableEqNat
          (@Array.size Nat
            (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))))
          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Eq Nat
                (@Array.size Nat
                  (@List.toArray Nat
                    (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (instDecidableEqNat
                (@Array.size Nat
                  (@List.toArray Nat
                    (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))))
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Array.scanlM_pure, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.scanlM_pure.h5 : Not
      (∀ {m : Type → Type} {β α : Type} {init : β} [inst : Monad m] {f : β → α → β} {as : Array α},
        @Eq (m (Array β))
          (@Array.scanlM m β α inst
            (fun (x1 : β) (x2 : α) => @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) β (f x1 x2)) init
            as (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size α as))
          (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (Array β)
            (@Array.scanl β α f init as (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Array.size α as)))) := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ({ pure := some, bind := fun _ _ => none } : Monad Option) (fun a b => a - b : Nat → Nat → Nat) (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))) (by
  decide +kernel)

-- List.toArray_scanrM, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.toArray_scanrM.h5 : ¬∀ {m : Type → Type} {α β : Type} {init : β} [inst : Monad m] {f : α → β → m β} {as : List α},
        List.toArray <$> List.scanrM f init as = Array.scanrM f init as.toArray := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) ([])) (by
  decide +kernel)

-- List.toArray_scanlM, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.toArray_scanlM.h5 : ¬∀ {m : Type → Type} {β α : Type} {init : β} [inst : Monad m] {f : β → α → m β} {as : List α},
        List.toArray <$> List.scanlM f init as = Array.scanlM f init as.toArray := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) ([])) (by
  decide +kernel)

-- ByteArray.get_append_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ByteArray.get_append_left.h3 : ¬∀ {i : Nat} {a : ByteArray} {b : ByteArray}, i < a.size := fun hc_h => absurd (@hc_h (0) ({ data := #[] : ByteArray }) ({ data := #[] : ByteArray })) (by
  decide +kernel)

-- ByteArray.get_append_left, hypothesis 4: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.ByteArray.get_append_left.h4.der : ∀ {i : Nat} {a b : ByteArray},
      @LT.lt Nat instLTNat i a.size →
        @LT.lt Nat instLTNat i
          (@HAppend.hAppend ByteArray ByteArray ByteArray (@instHAppendOfAppend ByteArray ByteArray.instAppend) a b).size := by
  (intros; grind)
theorem HypCheckProof.ByteArray.get_append_left.h4 : ∀ {i : Nat} {a b : ByteArray} (hlt : @LT.lt Nat instLTNat i a.size),
      @Eq UInt8
        (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
          ByteArray.instGetElemNatUInt8LtSize
          (@HAppend.hAppend ByteArray ByteArray ByteArray (@instHAppendOfAppend ByteArray ByteArray.instAppend) a b) i
          (@HypCheckProof.ByteArray.get_append_left.h4.der i a b hlt))
        (@GetElem.getElem ByteArray Nat UInt8 (fun (xs : ByteArray) (i : Nat) => @LT.lt Nat instLTNat i xs.size)
          ByteArray.instGetElemNatUInt8LtSize a i hlt) := by
  intro hc_x0 hc_x1 hc_x2 hc_x3
  exact @ByteArray.get_append_left hc_x0 hc_x1 hc_x2 hc_x3 (@HypCheckProof.ByteArray.get_append_left.h4.der hc_x0 hc_x1 hc_x2 hc_x3)

-- Fin.get_find?_minimal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.get_find?_minimal.h2 : ¬∀ {n : Nat} {p : Fin n → Bool} (j : Fin n), (Fin.find? p).isSome = Bool.true := fun hc_h => absurd (@hc_h (1) (fun (a : Fin 1) => Bool.false) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.get_find?_minimal, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.get_find?_minimal.h4 : ¬∀ {n : Nat} {p : Fin n → Bool}, (Fin.find? p).isSome = Bool.true → ∀ (j : Fin n), p j = Bool.false := fun hc_h => absurd (@hc_h (1) (fun (a : Fin 1) => Bool.true) (by
  decide) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Std.LawfulBCmp.isLE_iff_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulBCmp.isLE_iff_le.h5 : ¬∀ {α : Type} {inst : LE α} {inst_1 : LT α} {inst_2 : BEq α} {cmp : α → α → Ordering} {x y : α},
        (cmp x y).isLE = Bool.true ↔ x ≤ y := fun hc_h => absurd (@hc_h (Nat) (instLENat) (instLTNat) (instBEqOfDecidableEq) (fun a b => compare (a / 2) (b / 2) : Nat → Nat → Ordering) (1) (0)) (by
  decide +kernel)

-- List.interleave_flatten_flatten_of_length_eq_length, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.interleave_flatten_flatten_of_length_eq_length.h3 : ¬∀ {α : Type} {L₁ L₂ : List (List α)}, L₁.length = L₂.length := fun hc_h => absurd (@hc_h (Nat) ([]) ([[]])) (by
  decide +kernel)

-- List.interleave_flatten_flatten_of_length_eq_length, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.interleave_flatten_flatten_of_length_eq_length.h4 : ¬∀ {α : Type} {L₁ L₂ : List (List α)},
        L₁.length = L₂.length → L₁.flatten.interleave L₂.flatten = (List.zipWith List.interleave L₁ L₂).flatten := fun hc_h => absurd (@hc_h (Nat) ([[0], [1]]) ([[], [0]]) (by
  decide)) (by
  decide +kernel)

-- Std.TransOrd.instOrdLex', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TransOrd.instOrdLex'.h3 : Not (∀ {α : Type} (ord₁ ord₂ : Ord α) [inst : @Std.TransOrd α ord₂], @Std.TransOrd α (@Ord.lex' α ord₁ ord₂)) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (instOrdNat) _) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TransOrd.instOrdLex', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TransOrd.instOrdLex'.h4 : Not (∀ {α : Type} (ord₁ ord₂ : Ord α) [inst : @Std.TransOrd α ord₁], @Std.TransOrd α (@Ord.lex' α ord₁ ord₂)) := fun hc_h => absurd (@hc_h (Bool) (instOrdBool) (⟨fun _ _ => .lt⟩ : Ord Bool) _) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (Bool.false : Bool)) (b := (Bool.false : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.idxOfNth_lt_idxOfNth_iff_of_lt_count, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_lt_idxOfNth_iff_of_lt_count.h6 : ¬∀ {α : Type} {n : Nat} {x : α} {m : Nat} [inst : BEq α] {xs : List α},
        List.idxOfNth x xs n < List.idxOfNth x xs m ↔ n < m := fun hc_h => absurd (@hc_h (Nat) (0) (0) (1) (instBEqOfDecidableEq) ([])) (by
  decide +kernel)

-- Array.getElem_scanl, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.getElem_scanl.h6 : ¬∀ {β α : Type} {i : Nat} {init : β} {f : β → α → β} {as : Array α}, i < (Array.scanl f init as).size := fun hc_h => absurd (@hc_h (Nat) (Nat) (1) (0) (fun a b => a - b : Nat → Nat → Nat) (#[])) (by
  decide +kernel)

-- List.getElem_idxsOf_lt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_idxsOf_lt.h6 : ¬∀ {α : Type} {i : Nat} {xs : List α} {x : α} {s : Nat} [inst : BEq α], i < (List.idxsOf x xs s).length := fun hc_h => absurd (@hc_h (Nat) (0) ([]) (0) (0) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- Batteries.BinaryHeap.maxChild_gt, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.maxChild_gt.h6 : ¬∀ {α : Type} {sz : Nat} [inst : Ord α] {a : Vector α sz} {i j : Fin sz}, i < j := fun hc_h => absurd (@hc_h (Nat) (1) (instOrdNat) (#v[0]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Std.LawfulCmp.eq_lt_iff_lt, hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulCmp.eq_lt_iff_lt.h4.inst : ¬((fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.lt ↔ 0 ≤ 0) := by
  decide +kernel
theorem HypCheckProof.Std.LawfulCmp.eq_lt_iff_lt.h4 : ¬∀ {α : Type} {inst : LE α} {inst : LT α} {cmp : α → α → Ordering} {x y : α}, cmp x y = Ordering.lt ↔ x < y := fun hc_h => HypCheckProof.Std.LawfulCmp.eq_lt_iff_lt.h4.inst (@hc_h (Nat) (instLENat) ({ lt := fun (a b : Nat) => a ≤ b : LT Nat }) (fun (a b : Nat) => Ord.compare a b) (0) (0))

-- OptionT.run_monadLift, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.OptionT.run_monadLift.h4 : Not
      (∀ {m n : Type → Type} {α : Type} [inst : Monad m] [inst_1 : MonadLiftT n m] (x : n α),
        @Eq (m (Option α))
          (@OptionT.run m α
            (@MonadLiftT.monadLift n (OptionT m)
              (@instMonadLiftTOfMonadLift n m (OptionT m) (@OptionT.instMonadLift m inst) inst_1) α x))
          (@Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst)) α (Option α) (@Option.some α)
            (@MonadLiftT.monadLift n m inst_1 α x))) := fun hc_h => absurd (@hc_h (Option : Type → Type) (Option : Type → Type) (Nat) ({ pure := fun _ => none, bind := Option.bind } : Monad Option) (instMonadLiftT Option) (@Option.some Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) (by
  decide +kernel)

-- List.idxOfNth_eq_idxOfNth_iff_of_right_lt_count, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_eq_idxOfNth_iff_of_right_lt_count.h6 : ¬∀ {α : Type} {m : Nat} {x : α} {n : Nat} [inst : BEq α] {xs : List α},
        List.idxOfNth x xs n = List.idxOfNth x xs m ↔ n = m := fun hc_h => absurd (@hc_h (Nat) (0) (0) (1) (instBEqOfDecidableEq) ([])) (by
  decide +kernel)

-- List.countBefore_cons_succ_of_not_beq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countBefore_cons_succ_of_not_beq.h6 : ¬∀ {α : Type} {x : α} {xs : List α} {i : Nat} [inst : BEq α] {a : α},
        List.countBefore x (a :: xs) (i + 1) = List.countBefore x xs i := fun hc_h => absurd (@hc_h (Nat) (0) ([]) (0) (instBEqOfDecidableEq) (0)) (by
  decide +kernel)

-- List.idxOfNth_cons_of_beq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_cons_of_beq.h6 : ¬∀ {α : Type} {x : α} {xs : List α} {n : Nat} {a : α} [inst : BEq α],
        List.idxOfNth x (a :: xs) n = if n = 0 then 0 else List.idxOfNth x xs (n - 1) + 1 := fun hc_h => absurd (@hc_h (Nat) (0) ([]) (0) (1) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- Batteries.OrderedAssocList.toAssocList_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.toAssocList_cons.h6 : Not
      (∀ {α : Type} {a : α} {β : Type} {b : β} {cmp : α → α → Ordering} {l : @Batteries.OrderedAssocList α cmp β},
        @Batteries.OrderedAssocList.LTHeadKey α cmp β a l) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (fun a b => compare a b : Nat → Nat → Ordering) (@Batteries.OrderedAssocList.mk Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat
      (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat))
      (@of_decide_eq_true
        (@Batteries.AssocList.KeysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)))
        (@HypCheckDec.keysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Batteries.AssocList.KeysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
                (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)))
              (@HypCheckDec.keysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
                (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Batteries.OrderedAssocList.length_mk_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.length_mk_cons.h6 : ¬∀ {α : Type} {a : α} {β : Type} {b : β} {t : Batteries.AssocList α β} {cmp : α → α → Ordering},
        Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons a b t) := fun hc_h => absurd (@hc_h (Nat) (0) (Nat) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (fun a b => compare a b : Nat → Nat → Ordering)) (by
  decide +kernel)

-- Batteries.AssocList.orderedFind?_cons_self, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.orderedFind?_cons_self.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {b : β} {t : Batteries.AssocList α β},
        Batteries.AssocList.orderedFind? cmp (Batteries.AssocList.cons a b t) a = Option.some b := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Bool.false) (Nat) (0) (Batteries.AssocList.nil)) (by
  decide +kernel)

-- Batteries.OrderedAssocList.ltHeadKey_tail, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.ltHeadKey_tail.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {b : β} {t : Batteries.AssocList α β},
        Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons a b t) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (0) (Nat) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil)) (by
  decide +kernel)

-- Batteries.OrderedAssocList.toAssocList_tail_mk_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.toAssocList_tail_mk_cons.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {a : α} {b : β} {t : Batteries.AssocList α β},
        Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons a b t) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (0) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil)) (by
  decide +kernel)

-- Batteries.AssocList.KeysOrdered.ltHeadKey, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.KeysOrdered.ltHeadKey.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {b : β} {t : Batteries.AssocList α β},
        Batteries.AssocList.LTHeadKey cmp a t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (0) (Nat) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil)) (by
  decide +kernel)

-- Batteries.OrderedAssocList.toAssocList_filterMapVal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.toAssocList_filterMapVal.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β δ : Type} (f : α → β → Option δ) (l : Batteries.OrderedAssocList cmp β),
        Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Nat) (fun (a x : Nat) => Option.none) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat })) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.idxOfNth_eq_idxOfNth_iff_of_left_lt_count, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_eq_idxOfNth_iff_of_left_lt_count.h6 : ¬∀ {α : Type} {n : Nat} {x : α} {m : Nat} [inst : BEq α] {xs : List α},
        List.idxOfNth x xs n = List.idxOfNth x xs m ↔ n = m := fun hc_h => absurd (@hc_h (Nat) (0) (0) (1) (instBEqOfDecidableEq) ([])) (by
  decide +kernel)

-- List.lt_add_of_mem_idxsOf, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lt_add_of_mem_idxsOf.h6 : ¬∀ {α : Type} {xs : List α} {x : α} {s : Nat} [inst : BEq α] (y : Nat), y < xs.length + s := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (0) (instBEqOfDecidableEq) (0)) (by
  decide +kernel)

-- Substring.Raw.ValidFor.prev, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.prev.h6 : ¬∀ {l : List Char} {m₁ : List Char} {c : Char} {m₂ r : List Char} {s : Substring.Raw},
        s.prev { byteIdx := String.utf8Len m₁ + c.utf8Size : String.Pos.Raw } =
          { byteIdx := String.utf8Len m₁ : String.Pos.Raw } := fun hc_h => absurd (@hc_h ([]) ([]) ('é') ([]) ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- List.le_getElem_findIdxs, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_getElem_findIdxs.h5 : ¬∀ {i : Nat} {α : Type} {xs : List α} {p : α → Bool} {s : Nat}, i < (List.findIdxs p xs s).length := fun hc_h => absurd (@hc_h (0) (Nat) ([]) (fun n => n % 2 == 0 : Nat → Bool) (0)) (by
  decide +kernel)

-- Vector.isNone_finIdxOf?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.isNone_finIdxOf?.h3 : ¬∀ {α : Type} {n : Nat} [inst : BEq α] {v : Vector α n} {a : α}, (v.finIdxOf? a).isNone = !v.contains a := fun hc_h => absurd (@hc_h (Nat) (1) (⟨fun a b => a ≤ b⟩ : BEq Nat) (#v[0]) (1)) (by
  decide +kernel)

-- USize.toNat_ofNat_of_le_of_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.USize.toNat_ofNat_of_le_of_lt.h2 : ¬∀ {n i : Nat}, i ≤ n → (USize.ofNat i).toNat = i := fun hc_h => absurd (@hc_h (18446744073709551616) (18446744073709551616) (by
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

-- USize.toNat_ofNat_of_le_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.USize.toNat_ofNat_of_le_of_lt.h3 : ¬∀ {n i : Nat}, n < USize.size → (USize.ofNat i).toNat = i := fun hc_h => absurd (@hc_h (0) (18446744073709551616) (by
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

-- List.subset_cons_diff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.subset_cons_diff.h2 : ¬∀ {α : Type} [inst : BEq α] {a : α} {l₁ l₂ : List α}, (a :: l₁).diff l₂ ⊆ a :: l₁.diff l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) ([1]) ([0])) (by
  decide +kernel)

-- List.erase_cons_subperm_cons_erase, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.erase_cons_subperm_cons_erase.h2 : ¬∀ {α : Type} [inst : BEq α] (a b : α) (l : List α), ((a :: l).erase b).Subperm (a :: l.erase b) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) (0) ([1])) (by
  decide +kernel)

-- List.Subperm.count_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.count_le.h4 : ¬∀ {α : Type} [inst : BEq α] {l₁ l₂ : List α} (a : α), List.count a l₁ ≤ List.count a l₂ := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) ([0]) ([]) (0)) (by
  decide +kernel)

-- List.countPBefore_cons_succ_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countPBefore_cons_succ_of_pos.h5 : ¬∀ {α : Type} {p : α → Bool} {xs : List α} {i : Nat} {a : α},
        List.countPBefore p (a :: xs) (i + 1) = List.countPBefore p xs i + 1 := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) ([]) (0) (1)) (by
  decide +kernel)

-- List.replaceF_cons_of_some, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.replaceF_cons_of_some.h5 : ¬∀ {α : Type} {a' a : α} {l : List α} (p : α → Option α), List.replaceF p (a :: l) = a' :: l := fun hc_h => absurd (@hc_h (Nat) (0) (1) ([]) (fun _ => none : Nat → Option Nat)) (by
  decide +kernel)

-- List.getElem_zero_idxsOf_eq_idxOf_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_zero_idxsOf_eq_idxOf_add.h5 : ¬∀ {α : Type} {xs : List α} {x : α} {s : Nat} [inst : BEq α], 0 < (List.idxsOf x xs s).length := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (0) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- List.findIdxNth_lt_findIdxNth_iff_of_lt_countP, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdxNth_lt_findIdxNth_iff_of_lt_countP.h5 : ¬∀ {α : Type} {n : Nat} {p : α → Bool} {m : Nat} {xs : List α}, List.findIdxNth p xs n < List.findIdxNth p xs m ↔ n < m := fun hc_h => absurd (@hc_h (Nat) (0) (fun n => n % 2 == 0 : Nat → Bool) (1) ([])) (by
  decide +kernel)

-- List.getElem_swap, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_swap.h5 : ¬∀ {α : Type} {xs : List α} {i j k : Nat}, k < (xs.swap i j).length := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (0) (0)) (by
  decide +kernel)

-- List.ge_of_mem_findIdxs, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.ge_of_mem_findIdxs.h5 : ¬∀ {α : Type} {xs : List α} {p : α → Bool} {s : Nat} (y : Nat), s ≤ y := fun hc_h => absurd (@hc_h (Nat) ([]) (fun n => n % 2 == 0 : Nat → Bool) (1) (0)) (by
  decide +kernel)

-- List.mem_inter_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_inter_iff.h2 : ¬∀ {α : Type} [inst : BEq α] {x : α} {l₁ l₂ : List α}, x ∈ l₁ ∩ l₂ ↔ x ∈ l₁ ∧ x ∈ l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) ([0]) ([1])) (by
  decide +kernel)

-- Std.LawfulLTCmp.eq_gt_iff_gt, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.eq_gt_iff_gt.h5.inst : ¬((fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.gt ↔ 0 ≤ 0) := by
  decide +kernel
theorem HypCheckProof.Std.LawfulLTCmp.eq_gt_iff_gt.h5 : ¬∀ {α : Type} {cmp : α → α → Ordering} {x y : α} [inst : LT α], cmp x y = Ordering.gt ↔ y < x := fun hc_h => HypCheckProof.Std.LawfulLTCmp.eq_gt_iff_gt.h5.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (0) (0) ({ lt := fun (a b : Nat) => a ≤ b : LT Nat }))

-- List.idxOfNth_cons_zero_of_beq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_cons_zero_of_beq.h5 : ¬∀ {α : Type} {x : α} {xs : List α} {a : α} [inst : BEq α], List.idxOfNth x (a :: xs) 0 = 0 := fun hc_h => absurd (@hc_h (Nat) (0) ([]) (1) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- Array.extract_append_of_size_left_le_start, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.extract_append_of_size_left_le_start.h5 : ¬∀ {α : Type} {i j : Nat} {a b : Array α}, (a ++ b).extract i j = b.extract (i - a.size) (j - a.size) := fun hc_h => absurd (@hc_h (Nat) (0) (1) (#[0]) (#[])) (by
  decide +kernel)

-- Array.extract_append_of_stop_le_size_left, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.extract_append_of_stop_le_size_left.h5 : ¬∀ {α : Type} {j i : Nat} {a b : Array α}, (a ++ b).extract i j = a.extract i j := fun hc_h => absurd (@hc_h (Nat) (1) (0) (#[]) (#[0])) (by
  decide +kernel)

-- List.IsChain.rel, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.rel.h5 : ¬∀ {α : Type} {R : α → α → Prop} {a b : α} {l : List α}, R a b := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (0) ([])) (by
  decide +kernel)

-- Batteries.OrderedAssocList.ext_toAssocList, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.ext_toAssocList.h5 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {l₁ l₂ : @Batteries.OrderedAssocList α cmp β},
        @Eq (@Batteries.OrderedAssocList α cmp β) l₁ l₂) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (@Batteries.OrderedAssocList.mk Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat
      (@Batteries.AssocList.nil Nat Nat)
      (@of_decide_eq_true
        (@Batteries.AssocList.KeysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Batteries.AssocList.nil Nat Nat))
        (@HypCheckDec.keysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Batteries.AssocList.nil Nat Nat))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Batteries.AssocList.KeysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
                (@Batteries.AssocList.nil Nat Nat))
              (@HypCheckDec.keysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
                (@Batteries.AssocList.nil Nat Nat)))
            Bool.true)
          (@Eq.refl Bool Bool.true)))) (@Batteries.OrderedAssocList.mk Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat
      (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat))
      (@of_decide_eq_true
        (@Batteries.AssocList.KeysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)))
        (@HypCheckDec.keysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Batteries.AssocList.KeysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
                (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)))
              (@HypCheckDec.keysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
                (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  simp)

-- Vector.getD_mk, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.getD_mk.h3 : ¬∀ {α : Type} {n : Nat} (a : Array α) (i : Nat) (x : α), a.size = n := fun hc_h => absurd (@hc_h (Nat) (0) (#[0]) (0) (0)) (by
  decide +kernel)

-- Std.LawfulLECmp.isLE_iff_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulLECmp.isLE_iff_le.h3 : ¬∀ {α : Type} {inst : LE α} {cmp : α → α → Ordering} {x y : α}, (cmp x y).isLE = Bool.true ↔ x ≤ y := fun hc_h => absurd (@hc_h (Nat) (instLENat) (fun a b => compare (a / 2) (b / 2) : Nat → Nat → Ordering) (1) (0)) (by
  decide +kernel)

-- List.findIdxNth_mono, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdxNth_mono.h5 : ¬∀ {α : Type} {n m : Nat} {p : α → Bool} {xs : List α}, List.findIdxNth p xs n ≤ List.findIdxNth p xs m := fun hc_h => absurd (@hc_h (Nat) (1) (0) (fun n => n % 2 == 0 : Nat → Bool) ([0])) (by
  decide +kernel)

-- Batteries.BinomialHeap.Imp.HeapNode.WF.realSize_eq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinomialHeap.Imp.HeapNode.WF.realSize_eq.h5 : ¬∀ {α : Type} {le : α → α → Bool} {a : α} {n : Nat} {s : Batteries.BinomialHeap.Imp.HeapNode α}, s.realSize + 1 = 2 ^ n := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (0) (0) (Batteries.BinomialHeap.Imp.HeapNode.node 0 Batteries.BinomialHeap.Imp.HeapNode.nil
      Batteries.BinomialHeap.Imp.HeapNode.nil)) (by
  decide +kernel)

-- Batteries.OrderedAssocList.getElem?_eq_none_of_ltHeadKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_eq_none_of_ltHeadKey.h5 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {x : α} (l : @Batteries.OrderedAssocList α cmp β),
        @Eq (Option β)
          (@GetElem?.getElem? (@Batteries.OrderedAssocList α cmp β) α β
            (fun (l : @Batteries.OrderedAssocList α cmp β) (a : α) =>
              @Eq Bool (@Batteries.OrderedAssocList.contains α cmp β l a) Bool.true)
            (@Batteries.OrderedAssocList.instGetElem?EqBoolContainsTrue α cmp β) l x)
          (@Option.none β)) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.OrderedAssocList.mk Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat
      (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat))
      (@of_decide_eq_true
        (@Batteries.AssocList.KeysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)))
        (@HypCheckDec.keysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
          (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)))
        (@id
          (@Eq Bool
            (@Decidable.decide
              (@Batteries.AssocList.KeysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
                (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat)))
              (@HypCheckDec.keysOrdered Nat Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b)
                (@Batteries.AssocList.cons Nat Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Batteries.AssocList.nil Nat Nat))))
            Bool.true)
          (@Eq.refl Bool Bool.true))))) (by
  decide +kernel)

-- Vector.get_cast, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.get_cast.h4 : ¬∀ {α : Type} {m n : Nat} (v : Vector α m) (i : Fin n), m = n := fun hc_h => absurd (@hc_h (Nat) (0) (1) (#v[]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Array.pairwise_extract, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.pairwise_extract.h3 : ¬∀ {α : Type} {R : α → α → Prop} {as : Array α} (start stop : Nat), Array.Pairwise R (as.extract start stop) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (#[1, 0]) (0) (2)) (by
  decide +kernel)

-- List.lt_add_of_mem_findIdxs, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.lt_add_of_mem_findIdxs.h5 : ¬∀ {α : Type} {xs : List α} {p : α → Bool} {s : Nat} (y : Nat), y < xs.length + s := fun hc_h => absurd (@hc_h (Nat) ([]) (fun n => n % 2 == 0 : Nat → Bool) (0) (0)) (by
  decide +kernel)

-- List.diff_cons_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.diff_cons_right.h2 : ¬∀ {α : Type} [inst : BEq α] (l₁ l₂ : List α) (a : α), l₁.diff (a :: l₂) = (l₁.diff l₂).erase a := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : BEq Nat) ([0]) ([]) (1)) (by
  decide +kernel)

-- List.findIdxNth_cons_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdxNth_cons_of_pos.h5 : ¬∀ {α : Type} {p : α → Bool} {xs : List α} {n : Nat} {a : α},
        List.findIdxNth p (a :: xs) n = if n = 0 then 0 else List.findIdxNth p xs (n - 1) + 1 := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) ([]) (0) (1)) (by
  decide +kernel)

-- List.getElem_idxOfNth_beq, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_idxOfNth_beq.h5 : ¬∀ {α : Type} {x : α} {n : Nat} {xs : List α} [inst : BEq α], List.idxOfNth x xs n < xs.length := fun hc_h => absurd (@hc_h (Nat) (0) (0) ([]) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- List.sum_pair, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sum_pair.h3 : ¬∀ {α : Type} [inst : Add α] [inst_1 : Zero α] {a b : α}, [a, b].sum = a + b := fun hc_h => absurd (@hc_h (Nat) (instAddNat) (⟨1⟩ : Zero Nat) (0) (0)) (by
  decide +kernel)

-- List.mem_idxsOf_iff_getElem_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.mem_idxsOf_iff_getElem_pos.h5 : ¬∀ {α : Type} {i : Nat} {xs : List α} {x : α} [inst : BEq α], i < xs.length := fun hc_h => absurd (@hc_h (Nat) (0) ([]) (0) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- List.isChain_of_isChain_cons_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isChain_of_isChain_cons_cons.h5 : ¬∀ {α : Type} {R : α → α → Prop} {a b : α} {l : List α}, List.IsChain R l := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (0) ([1, 0])) (by
  decide +kernel)

-- Vector.finIdxOf?_eq_none_iff, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.finIdxOf?_eq_none_iff.h3 : ¬∀ {α : Type} {n : Nat} [inst : BEq α] {v : Vector α n} {a : α}, v.finIdxOf? a = Option.none ↔ ¬a ∈ v := fun hc_h => absurd (@hc_h (Nat) (1) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (#v[0]) (1)) (by
  decide +kernel)

-- List.isPrefixOf?_eq_some_iff_append_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isPrefixOf?_eq_some_iff_append_eq.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys zs : List α}, xs.isPrefixOf? ys = Option.some zs ↔ xs ++ zs = ys := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) ([1]) ([])) (by
  decide +kernel)

-- List.findIdxNth_cons_of_neg, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdxNth_cons_of_neg.h5 : ¬∀ {α : Type} {p : α → Bool} {xs : List α} {n : Nat} {a : α}, List.findIdxNth p (a :: xs) n = List.findIdxNth p xs n + 1 := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) ([]) (0) (0)) (by
  decide +kernel)

-- Batteries.AssocList.orderedFind?_eq_none_of_ltHeadKey, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.orderedFind?_eq_none_of_ltHeadKey.h5 : ¬∀ {α β : Type} {cmp : α → α → Ordering} {x : α} (l : Batteries.AssocList α β),
        Batteries.AssocList.orderedFind? cmp l x = Option.none := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil)) (by
  decide +kernel)

-- List.getElem?_set_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem?_set_of_lt.h5 : ¬∀ {α : Type} (a : α) {m n : Nat} (l : List α), (l.set m a)[n]? = if m = n then Option.some a else l[n]? := fun hc_h => absurd (@hc_h (Nat) (0) (0) (0) ([])) (by
  decide +kernel)

-- List.isChain_cons_of_isChain_cons_cons, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.isChain_cons_of_isChain_cons_cons.h5 : ¬∀ {α : Type} {R : α → α → Prop} {a : α} {b : α} {l : List α}, List.IsChain R (b :: l) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) (0) ([0])) (by
  decide +kernel)

-- Batteries.BinaryHeap.size_pos_of_max, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.size_pos_of_max.h4 : ¬∀ {α : Type} {x : α} [inst : Ord α] {heap : Batteries.BinaryHeap α}, 0 < heap.size := fun hc_h => absurd (@hc_h (Nat) (0) (instOrdNat) ({ arr := #[] : Batteries.BinaryHeap Nat })) (by
  decide +kernel)

-- List.swap_eq_of_ge_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.swap_eq_of_ge_left.h4 : ¬∀ {α : Type} {i j : Nat} {xs : List α}, xs.swap i j = xs := fun hc_h => absurd (@hc_h (Nat) (0) (1) ([0, 1])) (by
  decide +kernel)

-- Batteries.BinomialHeap.Imp.Heap.WF.rankGT, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinomialHeap.Imp.Heap.WF.rankGT.h4 : ¬∀ {α : Type} {lt : α → α → Bool} {n : Nat} {s : Batteries.BinomialHeap.Imp.Heap α}, s.rankGT n := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (0) (Batteries.BinomialHeap.Imp.Heap.cons 0 0 Batteries.BinomialHeap.Imp.HeapNode.nil Batteries.BinomialHeap.Imp.Heap.nil)) (by
  decide +kernel)

-- Vector.swap_same, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.swap_same.h4 : ¬∀ {α : Type} {n : Nat} {v : Vector α n} {i : Nat}, i < n := fun hc_h => absurd (@hc_h (Nat) (0) (#v[]) (0)) (by
  decide +kernel)

-- List.Subperm.cons_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.cons_right.h4 : ¬∀ {α : Type} {l l' : List α} (x : α), l.Subperm (x :: l') := fun hc_h => absurd (@hc_h (Nat) ([0]) ([]) (1)) (by
  decide +kernel)

-- Vector.getElem_tail, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.getElem_tail.h4 : ¬∀ {α : Type} {n : Nat} {v : Vector α n} {i : Nat}, i < n - 1 := fun hc_h => absurd (@hc_h (Nat) (0) (#v[]) (0)) (by
  decide +kernel)

-- Batteries.BinomialHeap.Imp.Heap.WF.size_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinomialHeap.Imp.Heap.WF.size_eq.h4 : ¬∀ {α : Type} {le : α → α → Bool} {n : Nat} {s : Batteries.BinomialHeap.Imp.Heap α}, s.size = s.realSize := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (0) (Batteries.BinomialHeap.Imp.Heap.cons 0 0
      (Batteries.BinomialHeap.Imp.HeapNode.node 0 Batteries.BinomialHeap.Imp.HeapNode.nil
        Batteries.BinomialHeap.Imp.HeapNode.nil)
      Batteries.BinomialHeap.Imp.Heap.nil)) (by
  decide +kernel)

-- List.subperm_ext_iff, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.subperm_ext_iff.h2 : ¬∀ {α : Type} [inst : BEq α] {l₁ l₂ : List α}, l₁.Subperm l₂ ↔ ∀ (x : α), x ∈ l₁ → List.count x l₁ ≤ List.count x l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) ([1])) (by
  decide +kernel)

-- List.IsChain.of_cons, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.of_cons.h4 : ¬∀ {α : Type} {R : α → α → Prop} {b : α} {l : List α}, List.IsChain R l := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (0) ([1, 0])) (by
  decide +kernel)

-- List.getElem_zero_findIdxs_eq_findIdx_add, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_zero_findIdxs_eq_findIdx_add.h4 : ¬∀ {α : Type} {xs : List α} {p : α → Bool} {s : Nat}, 0 < (List.findIdxs p xs s).length := fun hc_h => absurd (@hc_h (Nat) ([]) (fun n => n % 2 == 0 : Nat → Bool) (0)) (by
  decide +kernel)

-- Fin.isNone_of_isNone_findSomeRev?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.isNone_of_isNone_findSomeRev?.h4 : ¬∀ {n : Nat} {α : Type} {i : Fin n} {f : Fin n → Option α}, (f i).isNone = Bool.true := fun hc_h => absurd (@hc_h (1) (Nat) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (fun (a : Fin 1) => Option.some 0)) (by
  decide +kernel)

-- Fin.isSome_findSomeRev?_of_isSome, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.isSome_findSomeRev?_of_isSome.h4 : ¬∀ {n : Nat} {α : Type} {i : Fin n} {f : Fin n → Option α}, (Fin.findSomeRev? f).isSome = Bool.true := fun hc_h => absurd (@hc_h (1) (Nat) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (fun (a : Fin 1) => Option.none)) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.setCurr', hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.setCurr'.h4 : ¬∀ {l r : List Char} {c : Char} {it : String.Legacy.Iterator},
        String.Legacy.Iterator.ValidFor l (List.modifyHead (fun (x : Char) => c) r) (it.setCurr c) := fun hc_h => absurd (@hc_h ([]) ([]) ('a') ({ s := "", i := { byteIdx := 1 : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- List.getElem_filter_eq_getElem_getElem_findIdxs, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_filter_eq_getElem_getElem_findIdxs.h4 : ¬∀ {i : Nat} {α : Type} {xs : List α} {p : α → Bool}, i < (List.filter p xs).length := fun hc_h => absurd (@hc_h (0) (Nat) ([]) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- Fin.isNone_of_isNone_findSome?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.isNone_of_isNone_findSome?.h4 : ¬∀ {n : Nat} {α : Type} {i : Fin n} {f : Fin n → Option α}, (f i).isNone = Bool.true := fun hc_h => absurd (@hc_h (1) (Nat) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (fun (a : Fin 1) => Option.some 0)) (by
  decide +kernel)

-- Substring.Raw.ValidFor.toIterator, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.toIterator.h4 : ¬∀ {l m r : List Char} {s : Substring.Raw}, String.Legacy.Iterator.ValidFor l.reverse (m ++ r) s.toLegacyIterator := fun hc_h => absurd (@hc_h ([]) ([]) ([]) ({ str := "a", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- String.Pos.Raw.extract.go₂_append_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.extract.go₂_append_left.h4 : ¬∀ (s t : List Char) (i e : Nat),
        String.Pos.Raw.extract.go₂ (s ++ t) { byteIdx := i : String.Pos.Raw } { byteIdx := e : String.Pos.Raw } = s := fun hc_h => absurd (@hc_h (['a']) ([]) (0) (0)) (by
  decide +kernel)

-- Batteries.BinaryHeap.size_replaceMax_of_nonempty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.size_replaceMax_of_nonempty.h3 : ¬∀ {α : Type} [inst : Ord α] {heap : Batteries.BinaryHeap α} (x : α), (heap.replaceMax x).snd.size = heap.size := fun hc_h => absurd (@hc_h (Nat) (instOrdNat) ({ arr := #[] : Batteries.BinaryHeap Nat }) (0)) (by
  decide +kernel)

-- List.countPBefore_findIdxNth_of_lt_countP, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countPBefore_findIdxNth_of_lt_countP.h4 : ¬∀ {α : Type} {n : Nat} {p : α → Bool} {xs : List α}, List.countPBefore p xs (List.findIdxNth p xs n) = n := fun hc_h => absurd (@hc_h (Nat) (1) (fun n => n % 2 == 0 : Nat → Bool) ([])) (by
  decide +kernel)

-- List.max!_eq_max_of_ne_nil, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.max!_eq_max_of_ne_nil.h4 : ¬∀ {α : Type} [inst : Inhabited α] [inst : Max α] (l : List α), l ≠ [] := fun hc_h => absurd (@hc_h (Nat) (instInhabitedNat) (Nat.instMax) ([])) (by
  decide +kernel)

-- Std.LawfulCmp.toLawfulEqCmp, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulCmp.toLawfulEqCmp.h4 : ¬∀ {α : Type} {inst : LE α} {inst : LT α} {cmp : α → α → Ordering}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Nat) (instLENat) (instLTNat) (fun a b => compare (a / 2) (b / 2) : Nat → Nat → Ordering)) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_compare (a := (0 : Nat)) (b := (1 : Nat))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- String.Legacy.Iterator.ValidFor.prev, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.prev.h4 : ¬∀ {c : Char} {l r : List Char} {it : String.Legacy.Iterator}, String.Legacy.Iterator.ValidFor l (c :: r) it.prev := fun hc_h => absurd (@hc_h ('a') ([]) ([]) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- List.idxOf_mem_idxsOf, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOf_mem_idxsOf.h4 : ¬∀ {α : Type} {xs : List α} {x : α} [inst : BEq α], List.idxOf x xs ∈ List.idxsOf x xs := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- Substring.Raw.Valid.foldr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.foldr.h4 : ¬∀ {α : Type} (f : Char → α → α) (init : α) {s : Substring.Raw},
        Substring.Raw.Legacy.foldr f init s = List.foldr f init s.toString.toList := fun hc_h => absurd (@hc_h (Nat) (fun (a : Char) (n : Nat) => n + 1) (0) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { byteIdx := 1 : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Substring.Raw.ValidFor.stopPos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.stopPos.h4 : ¬∀ {l m : List Char} {r : List Char} {s : Substring.Raw},
        s.stopPos = { byteIdx := String.utf8Len l + String.utf8Len m : String.Pos.Raw } := fun hc_h => absurd (@hc_h ([]) (['a']) ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- String.length_eq_of_map_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.length_eq_of_map_eq.h4 : ¬∀ {a b : String} {f g : Char → Char}, a.length = b.length := fun hc_h => absurd (@hc_h ("") ("a") (fun (a : Char) => 'a') (fun (a : Char) => 'a')) (by
  decide +kernel)

-- Substring.Raw.ValidFor.bsize, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.bsize.h4 : ¬∀ {l : List Char} {m : List Char} {r : List Char} {s : Substring.Raw}, s.bsize = String.utf8Len m := fun hc_h => absurd (@hc_h ([]) (['a']) ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- List.findIdxNth_cons_zero_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdxNth_cons_zero_of_pos.h4 : ¬∀ {α : Type} {p : α → Bool} {xs : List α} {a : α}, List.findIdxNth p (a :: xs) 0 = 0 := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) ([]) (1)) (by
  decide +kernel)

-- List.interleave_append_right, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.interleave_append_right.h3 : ¬∀ {α : Type} {l₁ l₂ : List α} (l₃ : List α), l₁.interleave (l₂ ++ l₃) = l₁.interleave l₂ ++ l₃ := fun hc_h => absurd (@hc_h (Nat) ([0, 1]) ([]) ([0])) (by
  decide +kernel)

-- List.count_concat, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.count_concat.h2 : ¬∀ {α : Type} [inst : BEq α] (a : α) (l : List α), List.count a (l.concat a) = List.count a l + 1 := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a != b⟩ : BEq Nat) (0) ([])) (by
  decide +kernel)

-- Decidable.exists_not_of_not_forall, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Decidable.exists_not_of_not_forall.h4 : ¬∀ {α : Type} {p : α → Prop} [inst : Decidable (∃ (x : α), ¬p x)] [inst : (x : α) → Decidable (p x)], ∃ (x : α), ¬p x := fun hc_h => absurd (@hc_h (Bool) (fun _ => True : Bool → Prop) (Bool.instDecidableExistsOfDecidablePred fun (x : Bool) => ¬(fun (x : Bool) => True) x) (fun (x : Bool) => instDecidableTrue)) (by
  decide +kernel)

-- List.modify_eq_set_get, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.modify_eq_set_get.h4 : ¬∀ {α : Type} (f : α → α) {n : Nat} {l : List α}, n < l.length := fun hc_h => absurd (@hc_h (Nat) (fun n => n + 1 : Nat → Nat) (0) ([])) (by
  decide +kernel)

-- List.interleave_append_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.interleave_append_left.h3 : ¬∀ {α : Type} {l₁ l₂ : List α} (l₃ : List α), (l₁ ++ l₃).interleave l₂ = l₁.interleave l₂ ++ l₃ := fun hc_h => absurd (@hc_h (Nat) ([]) ([0]) ([1])) (by
  decide +kernel)

-- Eq.congr_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Eq.congr_left.h4 : ¬∀ {α : Type} {x y z : α}, x = z ↔ y = z := fun hc_h => absurd (@hc_h (Nat) (0) (1) (0)) (by
  decide +kernel)

-- Batteries.PairingHeapImp.Heap.size_tail, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.PairingHeapImp.Heap.size_tail.h3 : ¬∀ {α : Type} (le : α → α → Bool) {s : Batteries.PairingHeapImp.Heap α},
        (Batteries.PairingHeapImp.Heap.tail le s).size = s.size - 1 := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (Batteries.PairingHeapImp.Heap.node 0 Batteries.PairingHeapImp.Heap.nil
      (Batteries.PairingHeapImp.Heap.node 0 Batteries.PairingHeapImp.Heap.nil Batteries.PairingHeapImp.Heap.nil))) (by
  decide +kernel)

-- Fin.findSome?_succ_of_isNone, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.findSome?_succ_of_isNone.h3 : ¬∀ {n : Nat} {α : Type} {f : Fin (n + 1) → Option α}, Fin.findSome? f = Fin.findSome? fun (x : Fin n) => f x.succ := fun hc_h => absurd (@hc_h (0) (Nat) (fun (a : Fin (0 + 1)) => Option.some 0)) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.toString, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.toString.h3 : ¬∀ {l r : List Char} {it : String.Legacy.Iterator}, it.s = String.ofList (l.reverseAux r) := fun hc_h => absurd (@hc_h ([]) (['a']) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- List.getElem_flatten_aux₁, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_flatten_aux₁.h3 : ¬∀ {α : Type} (L : List (List α)) (i : Nat),
        List.findIdx (fun (x : Nat) => Decidable.decide (x > i)) (List.map List.length L).partialSums - 1 < L.length := fun hc_h => absurd (@hc_h (Nat) ([]) (0)) (by
  decide +kernel)

-- Fin.eq_false_of_findRev?_eq_none, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.eq_false_of_findRev?_eq_none.h2 : ¬∀ {n : Nat} {p : Fin n → Bool} (i : Fin n), p i = Bool.false := fun hc_h => absurd (@hc_h (1) (fun (a : Fin 1) => Bool.true) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Fin.findSome?_succ_of_none, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.findSome?_succ_of_none.h3 : ¬∀ {n : Nat} {α : Type} {f : Fin (n + 1) → Option α}, Fin.findSome? f = Fin.findSome? fun (x : Fin n) => f x.succ := fun hc_h => absurd (@hc_h (0) (Nat) (fun (a : Fin (0 + 1)) => Option.some 0)) (by
  decide +kernel)

-- Nat.length_toFinDigitsFixed, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.length_toFinDigitsFixed.h3 : ¬∀ {base : Nat} {n prec : Nat}, NeZero base := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.LawfulLECmp.toOrientedCmp, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulLECmp.toOrientedCmp.h3 : ¬∀ {α : Type} {inst : LE α} {cmp : α → α → Ordering}, Std.OrientedCmp cmp := fun hc_h => absurd (@hc_h (Nat) (instLENat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering)) (by
  exact fun hc_c =>
    absurd (hc_c.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.toFinDigitsFixed_succ, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toFinDigitsFixed_succ.h3 : ¬∀ {base : Nat} {n prec : Nat}, NeZero base := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fin.eq_false_of_isNone_find?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.eq_false_of_isNone_find?.h3 : ¬∀ {n : Nat} {i : Fin n} {p : Fin n → Bool}, p i = Bool.false := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (fun (a : Fin 1) => Bool.true)) (by
  decide +kernel)

-- BitVec.getElem_ofFnBE, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.BitVec.getElem_ofFnBE.h3 : ¬∀ {n : Nat} (f : Fin n → Bool) (i : Nat), i < n := fun hc_h => absurd (@hc_h (0) (fun (a : Fin 0) => Bool.false) (0)) (by
  decide +kernel)

-- Nat.toFinDigitsFixedRev_eq_reverse_toFinDigitsFixed, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toFinDigitsFixedRev_eq_reverse_toFinDigitsFixed.h2 : ¬∀ {base : Nat} {prec : Nat} (n : Nat), NeZero base := fun hc_h => absurd (@hc_h (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.disjoint_symm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.disjoint_symm.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₂.Disjoint l₁ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([0])) (by
  simp)

-- List.Perm.flatten_congr, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.flatten_congr.h3 : ¬∀ {α : Type} {l₁ l₂ : List (List α)}, l₁.flatten.Perm l₂.flatten := fun hc_h => absurd (@hc_h (Nat) ([]) ([[0]])) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.atEnd, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.atEnd.h3 : ¬∀ {l : List Char} {r : List Char} {it : String.Legacy.Iterator}, it.atEnd = Bool.true ↔ r = [] := fun hc_h => absurd (@hc_h ([]) (['a']) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- List.replaceF_of_forall_none, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.replaceF_of_forall_none.h3 : ¬∀ {α : Type} {p : α → Option α} {l : List α}, List.replaceF p l = l := fun hc_h => absurd (@hc_h (Nat) (fun n => some (n + 1) : Nat → Option Nat) ([0])) (by
  decide +kernel)

-- List.injective_idxToSigmaCount, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.injective_idxToSigmaCount.h2 : ¬∀ {α : Type} [inst : BEq α] {xs : List α}, ReflBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a != b⟩ : BEq Nat) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.rfl (a := (0 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.UnionFind.lt_rankD_findAux, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.lt_rankD_findAux.h3 : ¬∀ {i : Nat} {self : Batteries.UnionFind} {x : Fin self.size},
        self.rank i < self.rank (Batteries.UnionFind.parentD (self.findAux x).s i) := fun hc_h => absurd (@hc_h (0) (Batteries.UnionFind.empty.push : Batteries.UnionFind) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.surjective_idxToSigmaCount, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.surjective_idxToSigmaCount.h2 : ¬∀ {α : Type} [inst : BEq α] {xs : List α}, LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([])) (by
  exact fun hc_c =>
    absurd
      (hc_c.eq_of_beq (a := (0 : Nat)) (b := (1 : Nat))
        (by
          first
          | decide +kernel
          | (dsimp only <;> decide +kernel)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.UnionFind.arr_link, hypothesis 3: necessary
/- FAILED: 2:249: Application type mismatch: The argument
  ⟨0, ⋯⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨0, of_decide_eq_true (id (Eq.refl true))⟩ | 4:177: Application type mismatch: The argument
  ⟨0, ⋯⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨0, of_decide_eq_true (id (Eq.refl true))⟩ | 2:249: Application type mismatch: The argument
  ⟨0, ?m.16⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨0, ?m.16⟩ | 4:177: Application type mismatch: The argument
  ⟨0, ?m.8⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨0, ?m.8⟩ | 5:271: Application type mismatch: The argument
  ⟨0, ⋯⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨0, of_decide_eq_true (id (Eq.refl true))⟩ | 9:12: Application type mismatch: The argument
  ⟨0, ⋯⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  ↑⟨0, ⋯⟩ | 4:271: Application type mismatch: The argument
  ⟨0, ?m.14⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨0, ?m.14⟩ | 9:12: Application type mismatch: The argument
  ⟨0, ?m.1⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  ↑⟨0, ?m.1⟩
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.arr_link.h3 : ¬∀ {self : Batteries.UnionFind} {x : Fin self.size} {y : Fin self.size}, self.parent ↑y = ↑y := fun hc_h => absurd (@hc_h (Batteries.UnionFind.empty.push.push.union! 0 1 : Batteries.UnionFind) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)
-/

-- List.reverse_interleave_of_length_eq_length, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.reverse_interleave_of_length_eq_length.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, (l₁.interleave l₂).reverse = l₂.reverse.interleave l₁.reverse := fun hc_h => absurd (@hc_h (Nat) ([0, 1]) ([0])) (by
  decide +kernel)

-- Fin.eq_true_of_find?_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.eq_true_of_find?_eq_some.h3 : ¬∀ {n : Nat} {i : Fin n} {p : Fin n → Bool}, p i = Bool.true := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (fun (a : Fin 1) => Bool.false)) (by
  decide +kernel)

-- Fin.get_find?_eq_true, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.get_find?_eq_true.h2 : ¬∀ {n : Nat} {p : Fin n → Bool}, (Fin.find? p).isSome = Bool.true := fun hc_h => absurd (@hc_h (0) (fun (a : Fin 0) => Bool.false)) (by
  decide +kernel)

-- String.utf8Len_le_of_infix, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.utf8Len_le_of_infix.h2 : ¬∀ {cs₁ cs₂ : List Char}, String.utf8Len cs₁ ≤ String.utf8Len cs₂ := fun hc_h => absurd (@hc_h (['a']) ([])) (by
  decide +kernel)

-- Substring.Raw.Valid.any, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.any.h2 : ¬∀ (f : Char → Bool) {s : Substring.Raw}, Substring.Raw.Legacy.any s f = s.toString.toList.any f := fun hc_h => absurd (@hc_h (fun (a : Char) => Bool.true) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { byteIdx := 1 : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Nat.le_add_one_of_avg_eq_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_add_one_of_avg_eq_left.h2 : ¬∀ {a b : Nat}, b ≤ a + 1 := fun hc_h => absurd (@hc_h (0) (2)) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.prev_nil, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.prev_nil.h2 : ¬∀ {r : List Char} {it : String.Legacy.Iterator}, String.Legacy.Iterator.ValidFor [] r it.prev := fun hc_h => absurd (@hc_h (['a']) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- Nat.toString_append_toString, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toString_append_toString.h2 : ¬∀ (a b : Nat),
        ToString.toString a ++ ToString.toString b = ToString.toString (a * 10 ^ (ToString.toString b).length + b) := fun hc_h => absurd (@hc_h (0) (0)) (by
  decide +kernel)

-- Char.eq_true_of_all_eq_true, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.eq_true_of_all_eq_true.h1 : ¬∀ {p : Char → Bool} (c : Char), p c = Bool.true := fun hc_h => absurd (@hc_h (fun (a : Char) => Bool.false) ('a')) (by
  decide +kernel)

-- Nat.toFinDigits_of_lt_two, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toFinDigits_of_lt_two.h2 : ¬∀ {base n : Nat}, n.toFinDigits base = [] := fun hc_h => absurd (@hc_h (2) (1)) (by
  decide +kernel)

-- Substring.Raw.Valid.contains, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.contains.h2 : ¬∀ (c : Char) {s : Substring.Raw}, Substring.Raw.Legacy.contains s c = Bool.true ↔ c ∈ s.toString.toList := fun hc_h => absurd (@hc_h ('A') ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { byteIdx := 1 : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- UInt64.ext, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.UInt64.ext.h2 : ¬∀ {x y : UInt64}, x = y := fun hc_h => absurd (@hc_h (UInt64.ofNat 0) (UInt64.ofNat 1)) (by
  decide +kernel)

-- Std.instOrientedCmpFlipOrdering_batteries, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.instOrientedCmpFlipOrdering_batteries.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering}, Std.OrientedCmp (flip cmp) := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering)) (by
  exact fun hc_c =>
    absurd (hc_c.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Char.exists_eq_true_of_any_eq_true, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.exists_eq_true_of_any_eq_true.h1 : ¬∀ {p : Char → Bool}, ∃ (c : Char), p c = Bool.true := fun hc_h => absurd (@hc_h (fun (a : Char) => Bool.false)) (by
  simp)

-- Char.not_isLower_of_isUpper, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.not_isLower_of_isUpper.h1 : ¬∀ {c : Char}, ¬c.isLower = Bool.true := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- Substring.Raw.Valid.le, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.le.h1 : ¬∀ {s : Substring.Raw}, s.startPos ≤ s.stopPos := fun hc_h => absurd (@hc_h ({ str := "", startPos := { byteIdx := 1 : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

