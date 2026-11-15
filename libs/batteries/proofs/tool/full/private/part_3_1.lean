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

-- _private.Batteries.Data.OrderedAssocList.0.Batteries.OrderedAssocList.toAssocList_merge_mk_cons_mk_cons, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.toAssocList_merge_mk_cons_mk_cons.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {β γ δ : Type} (f : α → Option β → Option γ → Option δ)
        (x : α) (y : β) (t : Batteries.AssocList α β),
        Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y t) →
          ∀ (x' : α) (y' : γ) (t' : Batteries.AssocList α γ),
            Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x' y' t') → Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) (Nat) (Nat) (fun (a : Bool) (a_1 a_2 : Option Nat) => Option.none) (Bool.false) (0) (Batteries.AssocList.nil) (by
  decide) (Bool.false) (0) (Batteries.AssocList.nil) (by
  decide)) (by
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

-- _private.Batteries.Data.OrderedAssocList.0.Batteries.OrderedAssocList.toAssocList_merge_mk_cons_mk_cons, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.toAssocList_merge_mk_cons_mk_cons.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] [inst : Std.TransCmp cmp] {β γ δ : Type}
        (f : α → Option β → Option γ → Option δ) (x : α) (y : β) (t : Batteries.AssocList α β) (x' : α) (y' : γ)
        (t' : Batteries.AssocList α γ),
        Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x' y' t') →
          Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y t) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ (Nat) (Nat) (Nat) (fun (a : Nat) (a_1 a_2 : Option Nat) => Option.none) (0) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (0) (0) (Batteries.AssocList.nil) (by
  decide)) (by
  decide +kernel)

-- _private.Batteries.Data.OrderedAssocList.0.Batteries.OrderedAssocList.toAssocList_merge_mk_cons_mk_cons, hypothesis 15: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.toAssocList_merge_mk_cons_mk_cons.h15 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] [inst : Std.TransCmp cmp] {β γ δ : Type}
        (f : α → Option β → Option γ → Option δ) (x : α) (y : β) (t : Batteries.AssocList α β),
        Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y t) →
          ∀ (x' : α) (y' : γ) (t' : Batteries.AssocList α γ),
            Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x' y' t') := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ (Nat) (Nat) (Nat) (fun (a : Nat) (a_1 a_2 : Option Nat) => Option.none) (0) (0) (Batteries.AssocList.nil) (by
  decide) (0) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil)) (by
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

-- _private.Batteries.Data.Vector.Lemmas.0.Vector.scanrM.loop_toArray, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.scanrM.loop_toArray.h6 : ¬∀ {m : Type → Type} {α β : Type} {n : Nat} {cur : β} [inst : Monad m] {f : α → β → m β} {as : Vector α n} {i : Nat}
        {hi : i ≤ n} {acc_v : Vector β (n - i)} {acc_a : Array β} {h_acc : acc_v.toArray = acc_a},
        Vector.toArray <$> Vector.scanrM.loop f as cur i hi acc_v =
          Array.scanrM.loop f cur as.toArray i 0 (Eq.mpr (id (congrArg (LE.le i) as.size_toArray)) hi) acc_a := fun hc_h => absurd (fun hc_k0 => @hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) (0) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (#v[]) (0) hc_k0 (#v[]) _ rfl) (by
  decide +kernel)

-- _private.Batteries.Data.Vector.Lemmas.0.Vector.scanrM.loop_toArray, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.scanrM.loop_toArray.h10 : ¬∀ {m : Type → Type} {α β : Type} {n : Nat} {cur : β} [inst : Monad m] [inst : LawfulMonad m] {f : α → β → m β}
        {as : Vector α n} {i : Nat} {acc_v : Vector β (n - i)} {acc_a : Array β} {h_acc : acc_v.toArray = acc_a}, i ≤ n := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (0) (0) (instMonadOption) _ (fun (a x : Nat) => Option.none) (#v[]) (1) (#v[]) _ rfl) (by
  decide +kernel)

-- _private.Batteries.Data.Vector.Lemmas.0.Vector.scanrM.loop_toArray, hypothesis 13: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.scanrM.loop_toArray.h13 : ¬∀ {m : Type → Type} {α β : Type} {n : Nat} {cur : β} [inst : Monad m] [inst_1 : LawfulMonad m] {f : α → β → m β}
        {as : Vector α n} {i : Nat} {hi : i ≤ n} {acc_v : Vector β (n - i)} {acc_a : Array β},
        Vector.toArray <$> Vector.scanrM.loop f as cur i hi acc_v =
          Array.scanrM.loop f cur as.toArray i 0 (Eq.mpr (id (congrArg (LE.le i) as.size_toArray)) hi) acc_a := fun hc_h => absurd (fun hc_k0 => @hc_h (Option : Type → Type) (Nat) (Nat) (0) (0) (instMonadOption) _ (fun (a x : Nat) => Option.none) (#v[]) (0) hc_k0 (#v[]) (#[0])) (by
  decide +kernel)

-- _private.Batteries.Data.Array.Basic.0.Array.scanlM_loop_eq_scanlMFast_loop, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.scanlM_loop_eq_scanlMFast_loop.h11 : ¬∀ {m : Type → Type} {β α : Type} [inst : Monad m] {f : β → α → m β} {init : β} {as : Array α}
        {h_size : Array.SizeFitsUSize as} {start stop : Nat} {h_start : start ≤ as.size} {acc : Array β}, stop ≤ as.size := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (instMonadOption) (fun (a x : Nat) => Option.none) (0) (#[]) (by
  grind) (0) (1) (by
  decide) (#[])) (by
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

-- _private.Batteries.Data.UnionFind.Lemmas.0.Batteries.UnionFind.root_link.go, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.root_link.go.h6 : ¬∀ {self : Batteries.UnionFind} {x y : Fin self.size},
        self.parent ↑x = ↑x →
          self.parent ↑y = ↑y →
            ∀ {m : Batteries.UnionFind} (i : Nat),
              m.rootD i = if self.rootD i = ↑x ∨ self.rootD i = ↑y then ↑x else self.rootD i := fun hc_h => absurd (@hc_h (Batteries.UnionFind.empty.push.push : Batteries.UnionFind) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (Batteries.UnionFind.empty : Batteries.UnionFind) (0)) (by
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

