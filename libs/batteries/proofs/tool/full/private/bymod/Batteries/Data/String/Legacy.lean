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
-- _private.Batteries.Data.String.Legacy.0.String.set_next_add.foo, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.set_next_add.foo.h6 : ¬∀ (i : String.Pos.Raw) (c : Char) (cs : List Char) (a : String.Pos.Raw) (b₁ b₂ : Nat),
        (String.Pos.Raw.utf8GetAux (String.Pos.Raw.utf8SetAux c cs a i) a i).utf8Size + b₁ =
          String.utf8ByteSize'.go (String.Pos.Raw.utf8SetAux c cs a i) + b₂ := fun hc_h => absurd (@hc_h ({ : String.Pos.Raw }) ('a') ([]) ({ : String.Pos.Raw }) (0) (0)) (by
  decide +kernel)

-- _private.Batteries.Data.String.Legacy.0.String.set_next_add, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.set_next_add.h5 : ¬∀ (s : String) (i : String.Pos.Raw) (c : Char) (b₁ b₂ : Nat),
        (String.Pos.Raw.next (String.Pos.Raw.set s i c) i).byteIdx + b₁ = (String.Pos.Raw.set s i c).rawEndPos.byteIdx + b₂ := fun hc_h => absurd (@hc_h ("") ({ : String.Pos.Raw }) ('a') (0) (0)) (by
  decide +kernel)

-- _private.Batteries.Data.String.Legacy.0.String.mapAux_lemma, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.mapAux_lemma.h3 : ¬∀ (s : String) (i : String.Pos.Raw) (c : Char),
        (String.Pos.Raw.set s i c).rawEndPos.byteIdx - (String.Pos.Raw.next (String.Pos.Raw.set s i c) i).byteIdx <
          s.rawEndPos.byteIdx - i.byteIdx := fun hc_h => absurd (@hc_h ("") ({ : String.Pos.Raw }) ('a')) (by
  decide +kernel)

