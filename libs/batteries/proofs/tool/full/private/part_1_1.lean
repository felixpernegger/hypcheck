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

-- _private.Batteries.Data.Vector.Lemmas.0.Vector.scanlM.loop_toArray, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.scanlM.loop_toArray.h5 : ¬∀ {m : Type → Type} {β α : Type} {n : Nat} [inst : Monad m] (f : β → α → m β) (as : Vector α n)
        (h_stop : n ≤ as.toArray.size) (i : Nat) (hi : i ≤ n) (cur : β) (acc_v : Vector β i) (acc_a : Array β),
        acc_v.toArray = acc_a →
          Vector.toArray <$> Vector.scanlM.loop f as cur i hi acc_v = Array.scanlM.loop f cur as.toArray i n h_stop acc_a := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (#v[]) hc_k0 (0) hc_k1 (0) (#v[]) _ rfl) (by
  decide +kernel)

-- _private.Batteries.Data.Vector.Lemmas.0.Vector.scanlM.loop_toArray, hypothesis 8: removable
set_option maxHeartbeats 5000 in
theorem HypCheckProof.Vector.scanlM.loop_toArray.h8.der.{u_1, u_2, u_3} : ∀ {m : Type u_1 → Type u_2} {β : Type u_1} {α : Type u_3} {n : Nat} [inst : Monad m] [inst : LawfulMonad m]
      (f : β → α → m β) (as : Vector α n) (i : Nat),
      i ≤ n → ∀ (cur : β) (acc_v : Vector β i) (acc_a : Array β), acc_v.toArray = acc_a → n ≤ as.toArray.size := by
  (intros; simp_all; done)
theorem HypCheckProof.Vector.scanlM.loop_toArray.h8.{u_1, u_2, u_3} : ∀ {m : Type u_1 → Type u_2} {β : Type u_1} {α : Type u_3} {n : Nat} [inst : Monad m] [inst_1 : LawfulMonad m]
      (f : β → α → m β) (as : Vector α n) (i : Nat) (hi : i ≤ n) (cur : β) (acc_v : Vector β i) (acc_a : Array β)
      (h_acc : acc_v.toArray = acc_a),
      Vector.toArray <$> Vector.scanlM.loop f as cur i hi acc_v =
        Array.scanlM.loop f cur as.toArray i n
          (HypCheckProof.Vector.scanlM.loop_toArray.h8.der f as i hi cur acc_v acc_a h_acc) acc_a := by
  intro hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13
  exact @Vector.scanlM.loop_toArray hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 (@HypCheckProof.Vector.scanlM.loop_toArray.h8.der hc_x0 hc_x1 hc_x2 hc_x3 hc_x4 hc_x5 hc_x6 hc_x7 hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13) hc_x8 hc_x9 hc_x10 hc_x11 hc_x12 hc_x13

-- _private.Batteries.Data.Vector.Lemmas.0.Vector.scanlM.loop_toArray, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.scanlM.loop_toArray.h10 : ¬∀ {m : Type → Type} {β α : Type} {n : Nat} [inst : Monad m] [inst : LawfulMonad m] (f : β → α → m β) (as : Vector α n),
        n ≤ as.toArray.size → ∀ (i : Nat) (cur : β) (acc_v : Vector β i) (acc_a : Array β), acc_v.toArray = acc_a → i ≤ n := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (0) (instMonadOption) _ (fun (a x : Nat) => Option.none) (#v[]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (1) (0) (#v[0]) _ rfl) (by
  decide +kernel)

-- _private.Batteries.Data.Vector.Lemmas.0.Vector.scanlM.loop_toArray, hypothesis 14: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.scanlM.loop_toArray.h14 : ¬∀ {m : Type → Type} {β α : Type} {n : Nat} [inst : Monad m] [inst_1 : LawfulMonad m] (f : β → α → m β)
        (as : Vector α n) (h_stop : n ≤ as.toArray.size) (i : Nat) (hi : i ≤ n) (cur : β) (acc_v : Vector β i)
        (acc_a : Array β),
        Vector.toArray <$> Vector.scanlM.loop f as cur i hi acc_v = Array.scanlM.loop f cur as.toArray i n h_stop acc_a := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Option : Type → Type) (Nat) (Nat) (0) (instMonadOption) _ (fun (a x : Nat) => Option.none) (#v[]) hc_k0 (0) hc_k1 (0) (#v[]) (#[0])) (by
  decide +kernel)

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

-- _private.Batteries.Data.List.Basic.0.List.dropSlice_eq_dropSliceTR.go, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.dropSlice_eq_dropSliceTR.go.h6 : ¬∀ (α : Type) (l : List α) (m : Nat) (acc : Array α) (xs : List α) (n : Nat),
        List.dropSliceTR.go l m xs n acc = acc.toList ++ List.dropSlice n (m + 1) xs := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (#[0]) ([]) (0)) (by
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

-- _private.Batteries.Data.String.Legacy.0.String.set_next_add.foo, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.set_next_add.foo.h6 : ¬∀ (i : String.Pos.Raw) (c : Char) (cs : List Char) (a : String.Pos.Raw) (b₁ b₂ : Nat),
        (String.Pos.Raw.utf8GetAux (String.Pos.Raw.utf8SetAux c cs a i) a i).utf8Size + b₁ =
          String.utf8ByteSize'.go (String.Pos.Raw.utf8SetAux c cs a i) + b₂ := fun hc_h => absurd (@hc_h ({ : String.Pos.Raw }) ('a') ([]) ({ : String.Pos.Raw }) (0) (0)) (by
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

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.mkHeap.loop_perm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.mkHeap.loop_perm.h5 : ¬∀ {α : Type} {sz n : Nat} [inst : Ord α] {a : Vector α sz}, n ≤ sz := fun hc_h => absurd (@hc_h (Nat) (0) (1) (instOrdNat) (#v[])) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.Lemmas.0.Batteries.BinaryHeap.heapifyDown_eq_of_maxChild_none, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.heapifyDown_eq_of_maxChild_none.h5 : ¬∀ {α : Type} {sz : Nat} {i : Fin sz} [inst : Ord α] {a : Vector α sz}, Batteries.BinaryHeap.heapifyDown a i = a := fun hc_h => absurd (@hc_h (Nat) (2) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (instOrdNat) (#v[0, 1])) (by
  decide +kernel)

-- _private.Batteries.Data.Char.Basic.0.Char.of_all_eq_true_aux, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.of_all_eq_true_aux.h1 : ¬∀ {p : Char → Bool} (n : Nat) (hn : n.isValidChar), p (Char.ofNatAux n hn) = Bool.true := fun hc_h => absurd (fun hc_k0 => @hc_h (fun (a : Char) => Bool.false) (0) hc_k0) (by
  decide +kernel)

-- _private.Batteries.Data.Char.Basic.0.Char.of_any_eq_false_aux, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.of_any_eq_false_aux.h1 : ¬∀ {p : Char → Bool} (n : Nat) (hn : n.isValidChar), p (Char.ofNatAux n hn) = Bool.false := fun hc_h => absurd (fun hc_k0 => @hc_h (fun (a : Char) => Bool.true) (0) hc_k0) (by
  decide +kernel)

-- _private.Batteries.Data.String.Legacy.0.String.set_next_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.set_next_add.h5 : ¬∀ (s : String) (i : String.Pos.Raw) (c : Char) (b₁ b₂ : Nat),
        (String.Pos.Raw.next (String.Pos.Raw.set s i c) i).byteIdx + b₁ = (String.Pos.Raw.set s i c).rawEndPos.byteIdx + b₂ := fun hc_h => absurd (@hc_h ("") ({ : String.Pos.Raw }) ('a') (0) (0)) (by
  decide +kernel)

-- _private.Batteries.Data.BinaryHeap.WF.0.Batteries.BinaryHeap.InSubtree.le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.InSubtree.le.h2 : ¬∀ {j k : Nat}, j ≤ k := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- _private.Batteries.Data.UnionFind.Basic.0.Batteries.UnionFind.rank'_lt_rankMax.go, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.rank'_lt_rankMax.go.h2 : ¬∀ {l : List Batteries.UFNode} {x : Batteries.UFNode},
        x.rank ≤ List.foldr (fun (x : Batteries.UFNode) => Max.max x.rank) 0 l := fun hc_h => absurd (@hc_h ([]) ({ parent := 0, rank := 1 : Batteries.UFNode })) (by
  decide +kernel)

