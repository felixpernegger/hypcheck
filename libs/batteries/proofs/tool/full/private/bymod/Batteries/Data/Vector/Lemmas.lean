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

