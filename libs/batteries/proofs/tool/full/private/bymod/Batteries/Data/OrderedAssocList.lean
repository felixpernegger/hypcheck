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

-- _private.Batteries.Data.OrderedAssocList.0.Batteries.OrderedAssocList.merge_mk_cons_mk_cons, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.merge_mk_cons_mk_cons.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {β γ δ : Type} {x : α} {y : β}
        {t : Batteries.AssocList α β} {h : Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y t)} {x' : α}
        {y' : γ} {t' : Batteries.AssocList α γ}
        {h' : Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x' y' t')}
        {f : α → Option β → Option γ → Option δ}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) (Nat) (Nat) (Bool.false) (0) (Batteries.AssocList.nil) (by
  decide) (Bool.false) (0) (Batteries.AssocList.nil) (by
  decide) (fun (a : Bool) (a_1 a_2 : Option Nat) => Option.none)) (by
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

-- _private.Batteries.Data.OrderedAssocList.0.Batteries.OrderedAssocList.merge_mk_cons_mk_cons, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.merge_mk_cons_mk_cons.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] [inst : Std.TransCmp cmp] {β γ δ : Type} {x : α}
        {y : β} {t : Batteries.AssocList α β} {x' : α} {y' : γ} {t' : Batteries.AssocList α γ}
        {h' : Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x' y' t')}
        {f : α → Option β → Option γ → Option δ}, Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y t) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ (Nat) (Nat) (Nat) (0) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (0) (0) (Batteries.AssocList.nil) (by
  decide) (fun (a : Nat) (a_1 a_2 : Option Nat) => Option.none)) (by
  decide +kernel)

-- _private.Batteries.Data.OrderedAssocList.0.Batteries.OrderedAssocList.merge_mk_cons_mk_cons, hypothesis 14: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.merge_mk_cons_mk_cons.h14 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] [inst : Std.TransCmp cmp] {β γ δ : Type} {x : α}
        {y : β} {t : Batteries.AssocList α β} {h : Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y t)}
        {x' : α} {y' : γ} {t' : Batteries.AssocList α γ} {f : α → Option β → Option γ → Option δ},
        Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x' y' t') := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ (Nat) (Nat) (Nat) (0) (0) (Batteries.AssocList.nil) (by
  decide) (0) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (fun (a : Nat) (a_1 a_2 : Option Nat) => Option.none)) (by
  decide +kernel)

