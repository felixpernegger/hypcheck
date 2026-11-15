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
-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.maxChild_ge_right, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.maxChild_ge_right.h7 : ¬∀ {α : Type} {sz : Nat} [inst : Ord α] [inst_1 : Std.OrientedOrd α] (a : Vector α sz) (i j : Fin sz)
        (hright : 2 * ↑i + 2 < sz), (Ord.compare a[j] a[2 * ↑i + 2]).isGE = Bool.true := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (3) (instOrdNat) _ (#v[0, 1, 2]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3)) hc_k0) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.maxChild_ge_right, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.maxChild_ge_right.h8 : ¬∀ {α : Type} {sz : Nat} [inst : Ord α] [inst_1 : Std.OrientedOrd α] (a : Vector α sz) (i j : Fin sz),
        Batteries.BinaryHeap.maxChild a i = Option.some j → 2 * ↑i + 2 < sz := fun hc_h => absurd (@hc_h (Nat) (2) (instOrdNat) _ (#v[0, 1]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.toSortedArray.loop_sorted, hypothesis 5: necessary
/- FAILED: 6:54: expected token | 11:72: expected token | 6:54: expected token | 11:72: expected token | 3:48: expected token | 5:51: expected token | 3:48: expected token | 5:51: expected token
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.toSortedArray.loop_sorted.h5 : ¬∀ {α : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] {heap : Batteries.BinaryHeap α} {out : Array α},
        List.Pairwise (fun (x1 x2 : α) => (Ord.compare x1 x2).isGE = Bool.true) out.toList →
          (∀ (x : α), x ∈ out → ∀ (y : α), y ∈ heap → (Ord.compare x y).isGE = Bool.true) →
            List.Pairwise (fun (x1 x2 : α) => (Ord.compare x1 x2).isGE = Bool.true)
              (Batteries.BinaryHeap.toSortedArray.loop✝ heap out).toList := fun hc_h => absurd (@hc_h (Nat) (instOrdNat) _ ({ arr := #[0, 1] : Batteries.BinaryHeap Nat }) (#[]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)
-/

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.toSortedArray.loop_sorted, hypothesis 6: necessary
/- FAILED: 6:54: expected token | 11:72: expected token | 6:54: expected token | 11:72: expected token | 3:48: expected token | 5:51: expected token | 3:48: expected token | 5:51: expected token
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.toSortedArray.loop_sorted.h6 : ¬∀ {α : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] {heap : Batteries.BinaryHeap α} {out : Array α},
        heap.WF →
          (∀ (x : α), x ∈ out → ∀ (y : α), y ∈ heap → (Ord.compare x y).isGE = Bool.true) →
            List.Pairwise (fun (x1 x2 : α) => (Ord.compare x1 x2).isGE = Bool.true)
              (Batteries.BinaryHeap.toSortedArray.loop✝ heap out).toList := fun hc_h => absurd (@hc_h (Nat) (instOrdNat) _ ({ arr := #[] : Batteries.BinaryHeap Nat }) (#[0, 1]) (by
  decide) (by
  decide)) (by
  decide +kernel)
-/

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.toSortedArray.loop_sorted, hypothesis 7: necessary
/- FAILED: 6:54: expected token | 7:72: expected token | 6:54: expected token | 7:72: expected token | 3:48: expected token | 5:51: expected token | 3:48: expected token | 5:51: expected token
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.toSortedArray.loop_sorted.h7 : ¬∀ {α : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] {heap : Batteries.BinaryHeap α} {out : Array α},
        heap.WF →
          List.Pairwise (fun (x1 x2 : α) => (Ord.compare x1 x2).isGE = Bool.true) out.toList →
            List.Pairwise (fun (x1 x2 : α) => (Ord.compare x1 x2).isGE = Bool.true)
              (Batteries.BinaryHeap.toSortedArray.loop✝ heap out).toList := fun hc_h => absurd (@hc_h (Nat) (instOrdNat) _ ({ arr := #[1] : Batteries.BinaryHeap Nat }) (#[0]) (by
  decide) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)
-/

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.mkHeap.loop_wf, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.mkHeap.loop_wf.h6 : ¬∀ {α : Type} {sz n : Nat} [inst : Ord α] [inst_1 : Std.TransOrd α] {a : Vector α sz},
        (∀ (k : Fin sz), n ≤ ↑k → Batteries.BinaryHeap.WF.Children a k) → n ≤ sz := fun hc_h => absurd (@hc_h (Nat) (0) (1) (instOrdNat) _ (#v[]) (by
  simp)) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.maxChild_isChild, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.maxChild_isChild.h6 : Not
      (∀ {α : Type} {sz : Nat} {i j : Fin sz} [inst : Ord α] {a : Vector α sz},
        Or
          (@Eq Nat (@Fin.val sz j)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Fin.val sz i))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Eq Nat (@Fin.val sz j)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Fin.val sz i))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
          (@Eq.refl Bool Bool.true)))) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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
          (@Eq.refl Bool Bool.true)))) (instOrdNat) (@Vector.mk Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
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

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.heapifyDown_getElem_of_not_inSubtree, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.heapifyDown_getElem_of_not_inSubtree.h6 : ¬∀ {α : Type} {sz : Nat} [inst : Ord α] {a : Vector α sz} {i k : Fin sz},
        (Batteries.BinaryHeap.heapifyDown a i)[k] = a[k] := fun hc_h => absurd (@hc_h (Nat) (2) (instOrdNat) (#v[0, 1]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2))) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.heapifyDown_preserves_ge_root_of_subtree, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.heapifyDown_preserves_ge_root_of_subtree.h6 : ¬∀ {α : Type} {sz : Nat} {v : α} {j : Fin sz} [inst : Ord α] {a : Vector α sz},
        (Ord.compare v (Batteries.BinaryHeap.heapifyDown a j)[j]).isGE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (1) (0) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (instOrdNat) (#v[1])) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.mkHeap.loop_perm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.mkHeap.loop_perm.h5 : ¬∀ {α : Type} {sz n : Nat} [inst : Ord α] {a : Vector α sz}, n ≤ sz := fun hc_h => absurd (@hc_h (Nat) (0) (1) (instOrdNat) (#v[])) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.heapifyDown_eq_of_maxChild_none, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.heapifyDown_eq_of_maxChild_none.h5 : ¬∀ {α : Type} {sz : Nat} {i : Fin sz} [inst : Ord α] {a : Vector α sz}, Batteries.BinaryHeap.heapifyDown a i = a := fun hc_h => absurd (@hc_h (Nat) (2) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (instOrdNat) (#v[0, 1])) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.heapifyDown_set_of_le_preserves_children, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.heapifyDown_set_of_le_preserves_children.h9 : Not
      (∀ {α : Type} {sz : Nat} {x : α} [inst : Ord α] [inst_1 : @Std.TransOrd α inst] {v : Vector α sz} {i : Fin sz},
        @Batteries.BinaryHeap.WF.TopDown α sz inst v →
          @Eq Bool (@Ord.compare α inst (GetElem.getElem v i (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)) x).isGE Bool.true →
            @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@Fin.val sz i)) := fun hc_h => absurd (@hc_h (Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (instOrdNat) _ (@Vector.mk Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))) (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)) (@Fin.mk (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.maxChild_ge_left, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.maxChild_ge_left.h3 : ¬∀ {α : Type} {sz : Nat} [inst : Ord α] (a : Vector α sz) (i j : Fin sz),
        Batteries.BinaryHeap.maxChild a i = Option.some j →
          ∀ (hleft : 2 * ↑i + 1 < sz), (Ord.compare a[j] a[2 * ↑i + 1]).isGE = Bool.true := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Bool) (2) (⟨fun _ _ => .lt⟩ : Ord Bool) (#v[Bool.false, Bool.true]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) hc_k0 hc_k1) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.maxChild_ge_left, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.maxChild_ge_left.h7 : ¬∀ {α : Type} {sz : Nat} [inst : Ord α] [inst_1 : Std.OrientedOrd α] (a : Vector α sz) (i j : Fin sz)
        (hleft : 2 * ↑i + 1 < sz), (Ord.compare a[j] a[2 * ↑i + 1]).isGE = Bool.true := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (2) (instOrdNat) _ (#v[0, 1]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) hc_k0) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.heapifyDown_eq_of_lt_child, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.heapifyDown_eq_of_lt_child.h6 : ¬∀ {α : Type} {sz : Nat} {i j : Fin sz} [inst : Ord α] {a : Vector α sz},
        (Ord.compare a[i] a[j]).isLT = Bool.true →
          Batteries.BinaryHeap.heapifyDown a i = Batteries.BinaryHeap.heapifyDown (a.swap (↑i) (↑j) i.isLt j.isLt) j := fun hc_h => absurd (@hc_h (Nat) (3) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 3)) (instOrdNat) (#v[0, 1, 2]) (by
  decide)) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.heapifyDown_eq_of_lt_child, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.heapifyDown_eq_of_lt_child.h7 : ¬∀ {α : Type} {sz : Nat} {i j : Fin sz} [inst : Ord α] {a : Vector α sz},
        Batteries.BinaryHeap.maxChild a i = Option.some j →
          Batteries.BinaryHeap.heapifyDown a i = Batteries.BinaryHeap.heapifyDown (a.swap (↑i) (↑j) i.isLt j.isLt) j := fun hc_h => absurd (@hc_h (Nat) (2) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (instOrdNat) (#v[1, 0]) (by
  decide)) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.heapifyDown_eq_of_not_lt_child, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.heapifyDown_eq_of_not_lt_child.h6 : ¬∀ {α : Type} {sz : Nat} {i j : Fin sz} [inst : Ord α] {a : Vector α sz},
        ¬(Ord.compare a[i] a[j]).isLT = Bool.true → Batteries.BinaryHeap.heapifyDown a i = a := fun hc_h => absurd (@hc_h (Nat) (2) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (instOrdNat) (#v[0, 1]) (by
  decide)) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.heapifyDown_eq_of_not_lt_child, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.heapifyDown_eq_of_not_lt_child.h7 : ¬∀ {α : Type} {sz : Nat} {i j : Fin sz} [inst : Ord α] {a : Vector α sz},
        Batteries.BinaryHeap.maxChild a i = Option.some j → Batteries.BinaryHeap.heapifyDown a i = a := fun hc_h => absurd (@hc_h (Nat) (2) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (instOrdNat) (#v[0, 1]) (by
  decide)) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.heapifyDown_getElem_of_not_inSubtree', hypothesis 6: necessary
/- FAILED: 3:39: expected token | 4:43: expected token | 3:39: expected token | 4:43: expected token | 5:123: expected token | 8:37: expected token | 5:123: expected token | 8:37: expected token
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.heapifyDown_getElem_of_not_inSubtree'.h6 : ¬∀ {α : Type} {sz k : Nat} [inst : Ord α] {a : Vector α sz} {i : Fin sz},
        ¬Batteries.BinaryHeap.InSubtree✝ (↑i) k → k < sz := fun hc_h => absurd (@hc_h (Nat) (2) (2) (instOrdNat) (#v[0, 1]) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  grind)) (by
  decide +kernel)
-/

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.heapifyDown_getElem_of_not_inSubtree', hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.heapifyDown_getElem_of_not_inSubtree'.h7 : ¬∀ {α : Type} {sz k : Nat} [inst : Ord α] {a : Vector α sz} {i : Fin sz} (hk : k < sz),
        (Batteries.BinaryHeap.heapifyDown a i)[k] = a[k] := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (2) (0) (instOrdNat) (#v[0, 1]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) hc_k0) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.max_eq_arr_zero, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.max_eq_arr_zero.h4 : ¬∀ {α : Type} {x : α} [inst : Ord α] {heap : Batteries.BinaryHeap α}, heap.max = Option.some x := fun hc_h => absurd (@hc_h (Nat) (0) (instOrdNat) ({ arr := #[] : Batteries.BinaryHeap Nat })) (by
  decide +kernel)

