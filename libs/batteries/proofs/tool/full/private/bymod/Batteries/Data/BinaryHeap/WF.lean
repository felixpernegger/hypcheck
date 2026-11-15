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
-- _private.Batteries.Data.BinaryHeap.WF.0.Batteries.BinaryHeap.WF.TopDown.root_ge_all, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.WF.TopDown.root_ge_all.h3 : ¬∀ {α : Type} {sz : Nat} [inst : Ord α] {a : Vector α sz},
        Batteries.BinaryHeap.WF.TopDown a → ∀ (hne : 0 < sz) (k : Fin sz), (Ord.compare a[0] a[k]).isGE = Bool.true := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Bool) (1) (⟨fun _ _ => .lt⟩ : Ord Bool) (#v[Bool.false]) hc_k0 hc_k1 ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  simp)

-- _private.Batteries.Data.BinaryHeap.WF.0.Batteries.BinaryHeap.WF.TopDown.root_ge_all, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.WF.TopDown.root_ge_all.h5 : ¬∀ {α : Type} {sz : Nat} [inst : Ord α] [inst_1 : Std.TransOrd α] {a : Vector α sz} (hne : 0 < sz) (k : Fin sz),
        (Ord.compare a[0] a[k]).isGE = Bool.true := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (2) (instOrdNat) _ (#v[0, 1]) hc_k0 ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.WF.0.Batteries.BinaryHeap.WF.TopDown.of_root_and_below, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.WF.TopDown.of_root_and_below.h4 : ¬∀ {α : Type} {sz : Nat} [inst : Ord α] {a : Vector α sz}, 0 < sz := fun hc_h => absurd (@hc_h (Nat) (0) (instOrdNat) (#v[])) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.WF.0.Batteries.BinaryHeap.WF.TopDown.below_of_swap_pop, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.WF.TopDown.below_of_swap_pop.h5 : ¬∀ {α : Type} {sz : Nat} [inst : Ord α] {a : Vector α sz}, Batteries.BinaryHeap.WF.TopDown a → 0 < sz := fun hc_h => absurd (@hc_h (Nat) (0) (instOrdNat) (#v[]) (by
  simp)) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.WF.0.Batteries.BinaryHeap.WF.BottomUp.of_exceptAt_root, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.WF.BottomUp.of_exceptAt_root.h4 : ¬∀ {α : Type} {sz : Nat} [inst : Ord α] {a : Vector α sz}, 0 < sz := fun hc_h => absurd (@hc_h (Nat) (0) (instOrdNat) (#v[])) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.WF.0.Batteries.BinaryHeap.InSubtree.ne_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.InSubtree.ne_of_lt.h3 : ¬∀ {i j k : Nat}, Batteries.BinaryHeap.InSubtree j k → k ≠ i := fun hc_h => absurd (@hc_h (0) (0) (0) (by
  grind)) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.WF.0.Batteries.BinaryHeap.InSubtree.ne_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.InSubtree.ne_of_lt.h4 : ¬∀ {i j k : Nat}, i < j → k ≠ i := fun hc_h => absurd (@hc_h (0) (1) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.WF.0.Batteries.BinaryHeap.InSubtree.lt_of_ne, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.InSubtree.lt_of_ne.h2 : ¬∀ {j k : Nat}, j ≠ k → j < k := fun hc_h => absurd (@hc_h (1) (0) (by
  decide)) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.WF.0.Batteries.BinaryHeap.InSubtree.lt_of_ne, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.InSubtree.lt_of_ne.h3 : ¬∀ {j k : Nat}, Batteries.BinaryHeap.InSubtree j k → j < k := fun hc_h => absurd (@hc_h (0) (0) (by
  grind)) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.WF.0.Batteries.BinaryHeap.InSubtree.le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.InSubtree.le.h2 : ¬∀ {j k : Nat}, j ≤ k := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.WF.0.Batteries.BinaryHeap.WF.TopDown.parent_ge_subtree_of_set, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.WF.TopDown.parent_ge_subtree_of_set.h9 : Not
      (∀ {α : Type} {sz : Nat} {x : α} [inst : Ord α] [inst_1 : @Std.TransOrd α inst] {v : Vector α sz} {i : Fin sz},
        @Batteries.BinaryHeap.WF.TopDown α sz inst v →
          @Eq Bool (@Ord.compare α inst (GetElem.getElem v i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)) x).isGE Bool.true →
            ∀ (m : Fin sz),
              Batteries.BinaryHeap.InSubtree (@Fin.val sz i) (@Fin.val sz m) →
                @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Fin.val sz i)) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (instOrdNat) _ (@Vector.mk Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))) (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)) (by
  simp) (by
  decide) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)) (by
  grind)) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.WF.0.Batteries.BinaryHeap.WF.of_topDown, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.WF.of_topDown.h4 : ¬∀ {α : Type} {sz : Nat} {v : Vector α sz} [inst : Ord α], { arr := v.toArray : Batteries.BinaryHeap α }.WF := fun hc_h => absurd (@hc_h (Nat) (2) (#v[0, 1]) (instOrdNat)) (by
  decide +kernel)

