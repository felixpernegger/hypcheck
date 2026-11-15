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

-- Batteries.AssocList.ltHeadKey_orderedMerge, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_orderedMerge.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {l₁ : Batteries.AssocList α β} {β_1 : Type}
        {l₂ : Batteries.AssocList α β_1} {α_1 : Type} {f : α → Option β → Option β_1 → Option α_1}
        [inst : Std.TransCmp cmp],
        Batteries.AssocList.LTHeadKey cmp a l₂ →
          Batteries.AssocList.KeysOrdered cmp l₁ →
            Batteries.AssocList.KeysOrdered cmp l₂ →
              Batteries.AssocList.LTHeadKey cmp a (Batteries.AssocList.orderedMerge cmp f l₁ l₂) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (0) (Nat) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (Nat) (Batteries.AssocList.nil) (Nat) (fun (a : Nat) (a_1 a_2 : Option Nat) => Option.some 0) _ (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.ltHeadKey_orderedMerge, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_orderedMerge.h11 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {l₁ : Batteries.AssocList α β} {β_1 : Type}
        {l₂ : Batteries.AssocList α β_1} {α_1 : Type} {f : α → Option β → Option β_1 → Option α_1}
        [inst : Std.TransCmp cmp],
        Batteries.AssocList.LTHeadKey cmp a l₁ →
          Batteries.AssocList.KeysOrdered cmp l₁ →
            Batteries.AssocList.KeysOrdered cmp l₂ →
              Batteries.AssocList.LTHeadKey cmp a (Batteries.AssocList.orderedMerge cmp f l₁ l₂) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (0) (Nat) (Batteries.AssocList.nil) (Nat) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (Nat) (fun (a : Nat) (a_1 a_2 : Option Nat) => Option.some 0) _ (by
  decide) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Batteries.OrderedAssocList.getElem?_merge, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_merge.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {β γ δ : Type} {a : α}
        {f : α → Option β → Option γ → Option δ},
        f a Option.none Option.none = Option.none →
          ∀ {l₁ : Batteries.OrderedAssocList cmp β} {l₂ : Batteries.OrderedAssocList cmp γ}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) (Nat) (Nat) (Bool.false) (fun (a : Bool) (a_1 a_2 : Option Nat) => Option.none) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
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

-- Batteries.OrderedAssocList.getElem?_merge, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_merge.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {β γ δ : Type} {a : α}
        {f : α → Option β → Option γ → Option δ},
        f a Option.none Option.none = Option.none →
          ∀ {l₁ : Batteries.OrderedAssocList cmp β} {l₂ : Batteries.OrderedAssocList cmp γ}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) (Nat) (Nat) (0) (fun (a : Nat) (a_1 a_2 : Option Nat) => Option.none) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat }) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat })) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.OrderedAssocList.getElem?_merge, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_merge.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] [inst_1 : Std.TransCmp cmp] {β γ δ : Type} {a : α}
        {f : α → Option β → Option γ → Option δ} {l₁ : Batteries.OrderedAssocList cmp β}
        {l₂ : Batteries.OrderedAssocList cmp γ}, (Batteries.OrderedAssocList.merge f l₁ l₂)[a]? = f a l₁[a]? l₂[a]? := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ (Nat) (Nat) (Nat) (0) (fun (a : Nat) (a_1 a_2 : Option Nat) => Option.some 0) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => Ord.compare a b) Nat }) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => Ord.compare a b) Nat })) (by
  decide +kernel)

-- Batteries.AssocList.ext_orderedFind?, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.ext_orderedFind?.h9 : ¬∀ {α β : Type} (cmp : α → α → Ordering) [inst : Std.LawfulEqCmp cmp] [inst : Std.TransCmp cmp]
        {l₁ l₂ : Batteries.AssocList α β},
        Batteries.AssocList.KeysOrdered cmp l₁ → Batteries.AssocList.KeysOrdered cmp l₂ → l₁ = l₂ := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ (Batteries.AssocList.nil) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (by
  decide) (by
  decide)) (by
  simp)

-- Batteries.AssocList.orderedFind?_eq, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.orderedFind?_eq.h3 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] [inst : BEq α] [inst_1 : LawfulBEq α]
        (l : Batteries.AssocList α β),
        Batteries.AssocList.KeysOrdered cmp l →
          ∀ (x : α),
            Batteries.AssocList.orderedFind? cmp l x =
              Option.map (fun (x : α × β) => x.snd) (List.find? (fun (x_1 : α × β) => x_1.fst == x) l.toList) := fun hc_h => absurd (@hc_h (Bool) (Nat) (fun _ _ => .eq : Bool → Bool → Ordering) _ (instBEqOfDecidableEq) _ (Batteries.AssocList.cons Bool.false 0 Batteries.AssocList.nil) (by
  decide) (Bool.true)) (by
  decide +kernel)

-- Batteries.AssocList.orderedFind?_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.orderedFind?_eq.h4 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] [inst : BEq α] [inst_1 : LawfulBEq α]
        (l : Batteries.AssocList α β),
        Batteries.AssocList.KeysOrdered cmp l →
          ∀ (x : α),
            Batteries.AssocList.orderedFind? cmp l x =
              Option.map (fun (x : α × β) => x.snd) (List.find? (fun (x_1 : α × β) => x_1.fst == x) l.toList) := fun hc_h => absurd (@hc_h (Nat) (Bool) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (instBEqOfDecidableEq) _ (Batteries.AssocList.cons 1 Bool.false (Batteries.AssocList.cons 0 Bool.false Batteries.AssocList.nil)) (by
  decide) (0)) (by
  decide +kernel)

-- Batteries.AssocList.orderedFind?_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.orderedFind?_eq.h6 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] [inst : Std.TransCmp cmp] [inst : BEq α]
        (l : Batteries.AssocList α β),
        Batteries.AssocList.KeysOrdered cmp l →
          ∀ (x : α),
            Batteries.AssocList.orderedFind? cmp l x =
              Option.map (fun (x : α × β) => x.snd) (List.find? (fun (x_1 : α × β) => x_1.fst == x) l.toList) := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (by
  decide) (1)) (by
  decide +kernel)

-- Batteries.AssocList.orderedFind?_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.orderedFind?_eq.h8 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] [inst : Std.TransCmp cmp] [inst : BEq α]
        [inst_1 : LawfulBEq α] (l : Batteries.AssocList α β) (x : α),
        Batteries.AssocList.orderedFind? cmp l x =
          Option.map (fun (x : α × β) => x.snd) (List.find? (fun (x_1 : α × β) => x_1.fst == x) l.toList) := fun hc_h => absurd (@hc_h (Nat) (Bool) (fun a b => compare a b : Nat → Nat → Ordering) _ _ (instBEqOfDecidableEq) _ (Batteries.AssocList.cons 1 Bool.false (Batteries.AssocList.cons 0 Bool.false Batteries.AssocList.nil)) (0)) (by
  decide +kernel)

-- Batteries.AssocList.leHeadKey_cons, hypothesis 10: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.leHeadKey_cons.h10 : ¬∀ {α : Type} {cmp : α → α → Ordering} {x : α} {β : Type} {y : β} {t : Batteries.AssocList α β} {β_1 : Type}
        {s : Batteries.AssocList α β_1} [inst : Std.TransCmp cmp],
        Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y t) →
          Batteries.AssocList.LEHeadKey cmp (Batteries.AssocList.cons x y t) s := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (1) (Nat) (0) (Batteries.AssocList.nil) (Nat) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) _ (by
  decide)) (by
  (simp <;> decide))

-- Batteries.OrderedAssocList.insert_mk_cons, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.insert_mk_cons.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.OrientedCmp cmp] {β : Type} {x : α} {y : β}
        {t : Batteries.AssocList α β} {h : Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y t)} {a : α}
        {b : β}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) (Bool.false) (0) (Batteries.AssocList.nil) (by
  decide) (Bool.false) (0)) (by
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

-- Batteries.OrderedAssocList.insert_mk_cons, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.insert_mk_cons.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {β : Type} {x : α} {y : β}
        {t : Batteries.AssocList α β} {h : Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y t)} {a : α}
        {b : β}, Std.OrientedCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) (0) (0) (Batteries.AssocList.nil) (by
  decide) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.OrderedAssocList.insert_mk_cons, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.insert_mk_cons.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] [inst : Std.OrientedCmp cmp] {β : Type} {x : α}
        {y : β} {t : Batteries.AssocList α β} {a : α} {b : β},
        Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y t) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ _ (Nat) (0) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (0) (0)) (by
  decide +kernel)

-- Batteries.AssocList.KeysOrdered.lt_of_mem, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.KeysOrdered.lt_of_mem.h7 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {x : α} {y : β} {t : Batteries.AssocList α β}
        {p : α × β}, p ∈ t.toList → cmp x p.fst = Ordering.lt := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (0) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) ((0, 0)) (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.KeysOrdered.lt_of_mem, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.KeysOrdered.lt_of_mem.h9 : ¬∀ {α β : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {x : α} {y : β} {t : Batteries.AssocList α β},
        Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y t) → ∀ {p : α × β}, cmp x p.fst = Ordering.lt := fun hc_h => absurd (@hc_h (Nat) (Nat) (fun a b => compare a b : Nat → Nat → Ordering) _ (0) (0) (Batteries.AssocList.nil) (by
  decide) ((0, 0))) (by
  decide +kernel)

-- Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.inst : Not
      (@Std.LawfulLTCmp Nat (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) fun (x1 x2 : Nat) =>
        @compareOfLessAndEq Nat x1 x2 (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)
          ((fun (a b : Nat) => a.decLe b) x1 x2) instDecidableEqNat) := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (0 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.prem0 : ∀ {x y z : Nat}, @LE.le Nat instLENat x y → @LE.le Nat instLENat y z → @LE.le Nat instLENat x z := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.prem1 : ∀ {x y : Nat}, Not (@LE.le Nat instLENat x y) → @LE.le Nat instLENat y x := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.prem2 : ∀ {x y : Nat}, @LE.le Nat instLENat x y → @LE.le Nat instLENat y x → @Eq Nat x y := by
  omega
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : @DecidableLT α inst] [inst_2 : DecidableEq α] [inst_3 : LE α],
        (∀ {x y z : α}, @LT.lt α inst x y → @LT.lt α inst y z → @LT.lt α inst x z) →
          (∀ {x y : α}, Not (@LT.lt α inst x y) → @LE.le α inst_3 y x) →
            (∀ {x y : α}, @LE.le α inst_3 x y → @LE.le α inst_3 y x → @Eq α x y) →
              @Std.LawfulLTCmp α inst fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_1 x1 x2) inst_2) := fun hc_h => HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.inst (@hc_h (Nat) (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) (fun (a b : Nat) => a.decLe b) (instDecidableEqNat) (instLENat) HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.prem0 HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.prem1 HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.prem2)

-- Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6 : ¬∀ {α : Type} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : DecidableEq α] [inst_3 : LE α],
        (∀ (x : α), ¬x < x) →
          (∀ {x y : α}, ¬x < y → y ≤ x) →
            (∀ {x y : α}, x ≤ y → y ≤ x → x = y) → Std.LawfulLTCmp fun (x1 x2 : α) => compareOfLessAndEq x1 x2 := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≠ b⟩ : LT Nat) (fun (a b : Nat) => instDecidableNot) (instDecidableEqNat) (instLENat) (by
  simp) (by
  simp) (by
  omega)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.inst : Not
      (@Std.LawfulLTCmp Nat
        (@LT.mk Nat fun (a b : Nat) =>
          @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        fun (x1 x2 : Nat) =>
        @compareOfLessAndEq Nat x1 x2
          (@LT.mk Nat fun (a b : Nat) =>
            @LT.lt Nat instLTNat
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          ((fun (a b : Nat) =>
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
                (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            x1 x2)
          instDecidableEqNat) := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (2 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem0 : ∀ (x : Nat),
      Not
        (@LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem1 : ∀ {x y z : Nat},
      @LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem2 : ∀ {x y : Nat}, @LE.le Nat instLENat x y → @LE.le Nat instLENat y x → @Eq Nat x y := by
  omega
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : @DecidableLT α inst] [inst_2 : DecidableEq α] [inst_3 : LE α],
        (∀ (x : α), Not (@LT.lt α inst x x)) →
          (∀ {x y z : α}, @LT.lt α inst x y → @LT.lt α inst y z → @LT.lt α inst x z) →
            (∀ {x y : α}, @LE.le α inst_3 x y → @LE.le α inst_3 y x → @Eq α x y) →
              @Std.LawfulLTCmp α inst fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_1 x1 x2) inst_2) := fun hc_h => HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.inst (@hc_h (Nat) (@LT.mk Nat fun (a b : Nat) =>
      @LT.lt Nat instLTNat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (fun (a b : Nat) =>
      (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (instDecidableEqNat) (instLENat) HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem0 HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem1 HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem2)

-- Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.inst : Not
      (@Std.LawfulLTCmp Nat
        (@LT.mk Nat fun (a b : Nat) =>
          @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        fun (x1 x2 : Nat) =>
        @compareOfLessAndEq Nat x1 x2
          (@LT.mk Nat fun (a b : Nat) =>
            @LT.lt Nat instLTNat
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          ((fun (a b : Nat) =>
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
                (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            x1 x2)
          instDecidableEqNat) := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (2 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem0 : ∀ (x : Nat),
      Not
        (@LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem1 : ∀ {x y z : Nat},
      @LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem2 : ∀ {x y : Nat},
      Not
          (@LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
        @LE.le Nat instLENat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  simp
theorem HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : @DecidableLT α inst] [inst_2 : DecidableEq α] [inst_3 : LE α],
        (∀ (x : α), Not (@LT.lt α inst x x)) →
          (∀ {x y z : α}, @LT.lt α inst x y → @LT.lt α inst y z → @LT.lt α inst x z) →
            (∀ {x y : α}, Not (@LT.lt α inst x y) → @LE.le α inst_3 y x) →
              @Std.LawfulLTCmp α inst fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_1 x1 x2) inst_2) := fun hc_h => HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.inst (@hc_h (Nat) (@LT.mk Nat fun (a b : Nat) =>
      @LT.lt Nat instLTNat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (fun (a b : Nat) =>
      (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (instDecidableEqNat) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem0 HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem1 HypCheckProof.Std.LawfulLTCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem2)

-- Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 5: necessary
/- FAILED: 6:2: failed to synthesize
  Decidable (∀ {x y z : Bool}, x < y → y < z → x < z)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 8:2: failed to synthesize
  Decidable (∀ {x y z : Bool}, x < y → y < z → x < z)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 6:2: failed to synthesize
  Decidable (∀ {x y z : Bool}, x < y → y < z → x < z)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 8:2: failed to synthesize
  Decidable (∀ {x y z : Bool}, x < y → y < z → x < z)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. | 8:11: `dsimp` made no progress | 27:485: don't know how to synthesize implicit argument `y`
  @h5.prem1 (?m.17 hc_h) (?m.18 hc_h)
context:
hc_h :
  ∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : DecidableLT α] [inst_3 : DecidableEq α],
    (∀ {x y z : α}, x < y → y < z → x < z) →
      (∀ {x y : α}, ¬x < y ↔ y ≤ x) →
        (∀ {x y : α}, x ≤ y → y ≤ x → x = y) → Std.LawfulCmp fun x1 x2 => compareOfLessAndEq x1 x2
x✝ y✝ : Bool
⊢ Bool | 8:11: `dsimp` made no progress | 27:485: don't know how to synthesize implicit argument `y`
  @h5.prem1 (?m.17 hc_h) (?m.18 hc_h)
context:
hc_h :
  ∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : DecidableLT α] [inst_3 : DecidableEq α],
    (∀ {x y z : α}, x < y → y < z → x < z) →
      (∀ {x y : α}, ¬x < y ↔ y ≤ x) →
        (∀ {x y : α}, x ≤ y → y ≤ x → x = y) → Std.LawfulCmp fun x1 x2 => compareOfLessAndEq x1 x2
x✝ y✝ : Bool
⊢ Bool
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5 : ¬∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : DecidableLT α] [inst_3 : DecidableEq α],
        (∀ {x y z : α}, x < y → y < z → x < z) →
          (∀ {x y : α}, ¬x < y ↔ y ≤ x) →
            (∀ {x y : α}, x ≤ y → y ≤ x → x = y) → Std.LawfulCmp fun (x1 x2 : α) => compareOfLessAndEq x1 x2 := fun hc_h => absurd (@hc_h (Bool) (⟨fun _ _ => True⟩ : LT Bool) (⟨fun _ _ => False⟩ : LE Bool) (fun (a b : Bool) => instDecidableTrue) (instDecidableEqBool) (by
  decide) (by
  decide) (by
  decide)) (by
  exact fun hc_c =>
    absurd (hc_c.toTransCmp.toOrientedCmp.eq_swap (a := (Bool.false : Bool)) (b := (Bool.false : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))
-/

-- Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.inst : Not
      (@Std.LawfulCmp Bool (@LE.mk Bool fun (a b : Bool) => @Eq Bool a b) (@LT.mk Bool fun (a b : Bool) => @Ne Bool a b)
        fun (x1 x2 : Bool) =>
        @compareOfLessAndEq Bool x1 x2 (@LT.mk Bool fun (a b : Bool) => @Ne Bool a b)
          ((fun (a b : Bool) => @instDecidableNot (@Eq Bool a b) (instDecidableEqBool a b)) x1 x2) instDecidableEqBool) := by
  exact fun hc_c =>
    absurd (hc_c.toTransCmp.toOrientedCmp.eq_swap (a := (Bool.false : Bool)) (b := (Bool.true : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.prem0 : ∀ (x : Bool), Not (@Ne Bool x x) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.prem1 : ∀ {x y : Bool}, Iff (Not (@Ne Bool x y)) (@Eq Bool y x) := by
  decide
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.prem2 : ∀ {x y : Bool}, @Eq Bool x y → @Eq Bool y x → @Eq Bool x y := by
  decide
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : @DecidableLT α inst] [inst_3 : DecidableEq α],
        (∀ (x : α), Not (@LT.lt α inst x x)) →
          (∀ {x y : α}, Iff (Not (@LT.lt α inst x y)) (@LE.le α inst_1 y x)) →
            (∀ {x y : α}, @LE.le α inst_1 x y → @LE.le α inst_1 y x → @Eq α x y) →
              @Std.LawfulCmp α inst_1 inst fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_2 x1 x2) inst_3) := fun hc_h => HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.inst (@hc_h (Bool) (@LT.mk Bool fun (a b : Bool) => @Ne Bool a b) (@LE.mk Bool fun (a b : Bool) => @Eq Bool a b) (fun (a b : Bool) => @instDecidableNot (@Eq Bool a b) (instDecidableEqBool a b)) (instDecidableEqBool) HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.prem0 HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.prem1 HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6.prem2)

-- Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.inst : Not
      (@Std.LawfulCmp Nat instLENat
        (@LT.mk Nat fun (a b : Nat) =>
          @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        fun (x1 x2 : Nat) =>
        @compareOfLessAndEq Nat x1 x2
          (@LT.mk Nat fun (a b : Nat) =>
            @LT.lt Nat instLTNat
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          ((fun (a b : Nat) =>
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
                (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            x1 x2)
          instDecidableEqNat) := by
  exact fun hc_c =>
    absurd (hc_c.toTransCmp.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (2 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem0 : ∀ (x : Nat),
      Not
        (@LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem1 : ∀ {x y z : Nat},
      @LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem2 : ∀ {x y : Nat}, @LE.le Nat instLENat x y → @LE.le Nat instLENat y x → @Eq Nat x y := by
  omega
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : @DecidableLT α inst] [inst_3 : DecidableEq α],
        (∀ (x : α), Not (@LT.lt α inst x x)) →
          (∀ {x y z : α}, @LT.lt α inst x y → @LT.lt α inst y z → @LT.lt α inst x z) →
            (∀ {x y : α}, @LE.le α inst_1 x y → @LE.le α inst_1 y x → @Eq α x y) →
              @Std.LawfulCmp α inst_1 inst fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_2 x1 x2) inst_3) := fun hc_h => HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.inst (@hc_h (Nat) (@LT.mk Nat fun (a b : Nat) =>
      @LT.lt Nat instLTNat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (instLENat) (fun (a b : Nat) =>
      (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (instDecidableEqNat) HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem0 HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem1 HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem2)

-- Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.inst : Not
      (@Std.LawfulCmp Nat
        (@LE.mk Nat fun (a b : Nat) =>
          @LE.le Nat instLENat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@LT.mk Nat fun (a b : Nat) =>
          @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        fun (x1 x2 : Nat) =>
        @compareOfLessAndEq Nat x1 x2
          (@LT.mk Nat fun (a b : Nat) =>
            @LT.lt Nat instLTNat
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          ((fun (a b : Nat) =>
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
                (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            x1 x2)
          instDecidableEqNat) := by
  exact fun hc_c =>
    absurd (hc_c.toTransCmp.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (2 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem0 : ∀ (x : Nat),
      Not
        (@LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem1 : ∀ {x y z : Nat},
      @LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem2 : ∀ {x y : Nat},
      Iff
        (Not
          (@LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (@LE.le Nat instLENat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  simp
theorem HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : @DecidableLT α inst] [inst_3 : DecidableEq α],
        (∀ (x : α), Not (@LT.lt α inst x x)) →
          (∀ {x y z : α}, @LT.lt α inst x y → @LT.lt α inst y z → @LT.lt α inst x z) →
            (∀ {x y : α}, Iff (Not (@LT.lt α inst x y)) (@LE.le α inst_1 y x)) →
              @Std.LawfulCmp α inst_1 inst fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_2 x1 x2) inst_3) := fun hc_h => HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.inst (@hc_h (Nat) (@LT.mk Nat fun (a b : Nat) =>
      @LT.lt Nat instLTNat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (fun (a b : Nat) =>
      (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (instDecidableEqNat) HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem0 HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem1 HypCheckProof.Std.LawfulCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem2)

-- Batteries.AssocList.ltHeadKey_of_cons, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_of_cons.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a x : α} {β : Type} {y : β} {t : Batteries.AssocList α β},
        Batteries.AssocList.LTHeadKey cmp a (Batteries.AssocList.cons x y t) →
          Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y t) → Batteries.AssocList.LTHeadKey cmp a t := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (0) (1) (Nat) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.ltHeadKey_of_cons, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_of_cons.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a x : α} {β : Type} {y : β} {t : Batteries.AssocList α β}
        [inst : Std.TransCmp cmp],
        Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons x y t) → Batteries.AssocList.LTHeadKey cmp a t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (1) (0) (Nat) (0) (Batteries.AssocList.cons 1 0 Batteries.AssocList.nil) _ (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.ltHeadKey_of_cons, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_of_cons.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a x : α} {β : Type} {y : β} {t : Batteries.AssocList α β}
        [inst : Std.TransCmp cmp],
        Batteries.AssocList.LTHeadKey cmp a (Batteries.AssocList.cons x y t) → Batteries.AssocList.LTHeadKey cmp a t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (0) (1) (Nat) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) _ (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.ltHeadKey_of_leHeadKey, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_of_leHeadKey.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {s : Batteries.AssocList α β} {β_1 : Type}
        {t : Batteries.AssocList α β_1},
        Batteries.AssocList.LTHeadKey cmp a s →
          Batteries.AssocList.LEHeadKey cmp s t → Batteries.AssocList.LTHeadKey cmp a t := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (0) (Nat) (Batteries.AssocList.cons 1 0 Batteries.AssocList.nil) (Nat) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (by
  decide) (by
  simp)) (by
  decide +kernel)

-- Batteries.AssocList.ltHeadKey_of_leHeadKey, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_of_leHeadKey.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {s : Batteries.AssocList α β} {β_1 : Type}
        {t : Batteries.AssocList α β_1} [inst : Std.TransCmp cmp],
        Batteries.AssocList.LEHeadKey cmp s t → Batteries.AssocList.LTHeadKey cmp a t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (0) (Nat) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (Nat) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) _ (by
  simp)) (by
  decide +kernel)

-- Batteries.AssocList.ltHeadKey_of_leHeadKey, hypothesis 9: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_of_leHeadKey.h9 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {s : Batteries.AssocList α β} {β_1 : Type}
        {t : Batteries.AssocList α β_1} [inst : Std.TransCmp cmp],
        Batteries.AssocList.LTHeadKey cmp a s → Batteries.AssocList.LTHeadKey cmp a t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (0) (Nat) (Batteries.AssocList.nil) (Nat) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) _ (by
  decide)) (by
  decide +kernel)

-- Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 5: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.inst : Not
      (@Std.TransCmp Nat fun (x1 x2 : Nat) =>
        @compareOfLessAndEq Nat x1 x2 (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b)
          ((fun (a b : Nat) => a.decLe b) x1 x2) instDecidableEqNat) := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (0 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.prem0 : ∀ {x y z : Nat}, @LE.le Nat instLENat x y → @LE.le Nat instLENat y z → @LE.le Nat instLENat x z := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.prem1 : ∀ {x y : Nat}, Not (@LE.le Nat instLENat x y) → @LE.le Nat instLENat y x := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.prem2 : ∀ {x y : Nat}, @LE.le Nat instLENat x y → @LE.le Nat instLENat y x → @Eq Nat x y := by
  omega
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : @DecidableLT α inst] [inst_3 : DecidableEq α],
        (∀ {x y z : α}, @LT.lt α inst x y → @LT.lt α inst y z → @LT.lt α inst x z) →
          (∀ {x y : α}, Not (@LT.lt α inst x y) → @LE.le α inst_1 y x) →
            (∀ {x y : α}, @LE.le α inst_1 x y → @LE.le α inst_1 y x → @Eq α x y) →
              @Std.TransCmp α fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_2 x1 x2) inst_3) := fun hc_h => HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.inst (@hc_h (Nat) (@LT.mk Nat fun (a b : Nat) => @LE.le Nat instLENat a b) (instLENat) (fun (a b : Nat) => a.decLe b) (instDecidableEqNat) HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.prem0 HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.prem1 HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h5.prem2)

-- Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h6 : ¬∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : DecidableLT α] [inst_3 : DecidableEq α],
        (∀ (x : α), ¬x < x) →
          (∀ {x y : α}, ¬x < y → y ≤ x) →
            (∀ {x y : α}, x ≤ y → y ≤ x → x = y) → Std.TransCmp fun (x1 x2 : α) => compareOfLessAndEq x1 x2 := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≠ b⟩ : LT Nat) (instLENat) (fun (a b : Nat) => instDecidableNot) (instDecidableEqNat) (by
  simp) (by
  simp) (by
  omega)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.inst : Not
      (@Std.TransCmp Nat fun (x1 x2 : Nat) =>
        @compareOfLessAndEq Nat x1 x2
          (@LT.mk Nat fun (a b : Nat) =>
            @LT.lt Nat instLTNat
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          ((fun (a b : Nat) =>
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
                (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            x1 x2)
          instDecidableEqNat) := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (2 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem0 : ∀ (x : Nat),
      Not
        (@LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem1 : ∀ {x y z : Nat},
      @LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem2 : ∀ {x y : Nat}, @LE.le Nat instLENat x y → @LE.le Nat instLENat y x → @Eq Nat x y := by
  omega
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : @DecidableLT α inst] [inst_3 : DecidableEq α],
        (∀ (x : α), Not (@LT.lt α inst x x)) →
          (∀ {x y z : α}, @LT.lt α inst x y → @LT.lt α inst y z → @LT.lt α inst x z) →
            (∀ {x y : α}, @LE.le α inst_1 x y → @LE.le α inst_1 y x → @Eq α x y) →
              @Std.TransCmp α fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_2 x1 x2) inst_3) := fun hc_h => HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.inst (@hc_h (Nat) (@LT.mk Nat fun (a b : Nat) =>
      @LT.lt Nat instLTNat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (instLENat) (fun (a b : Nat) =>
      (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (instDecidableEqNat) HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem0 HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem1 HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h7.prem2)

-- Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.inst : Not
      (@Std.TransCmp Nat fun (x1 x2 : Nat) =>
        @compareOfLessAndEq Nat x1 x2
          (@LT.mk Nat fun (a b : Nat) =>
            @LT.lt Nat instLTNat
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          ((fun (a b : Nat) =>
              (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
                (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            x1 x2)
          instDecidableEqNat) := by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (2 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel))
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem0 : ∀ (x : Nat),
      Not
        (@LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  simp
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem1 : ∀ {x y z : Nat},
      @LT.lt Nat instLTNat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          @LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) z (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  omega
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem2 : ∀ {x y : Nat},
      Not
          (@LT.lt Nat instLTNat
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
        @LE.le Nat instLENat
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) y (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) x (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  simp
theorem HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8 : Not
      (∀ {α : Type} [inst : LT α] [inst_1 : LE α] [inst_2 : @DecidableLT α inst] [inst_3 : DecidableEq α],
        (∀ (x : α), Not (@LT.lt α inst x x)) →
          (∀ {x y z : α}, @LT.lt α inst x y → @LT.lt α inst y z → @LT.lt α inst x z) →
            (∀ {x y : α}, Not (@LT.lt α inst x y) → @LE.le α inst_1 y x) →
              @Std.TransCmp α fun (x1 x2 : α) => @compareOfLessAndEq α x1 x2 inst (inst_2 x1 x2) inst_3) := fun hc_h => HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.inst (@hc_h (Nat) (@LT.mk Nat fun (a b : Nat) =>
      @LT.lt Nat instLTNat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@LE.mk Nat fun (a b : Nat) =>
      @LE.le Nat instLENat
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (fun (a b : Nat) =>
      (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))).decLt
        (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) b (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (instDecidableEqNat) HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem0 HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem1 HypCheckProof.Std.TransCmp.compareOfLessAndEq_of_irrefl_of_trans_of_not_lt_of_antisymm.h8.prem2)

-- Array.scanlM.loop_toList, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.scanlM.loop_toList.h8 : Not
      (∀ {m : Type → Type} {β α : Type} {init : β} {as : Array α} {start : Nat} {acc : Array β} [inst : Monad m]
        {f : β → α → m β} {stop : Nat} (h : @LE.le Nat instLENat stop (@Array.size α as)),
        @Eq (m (List β))
          (@Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst)) (Array β) (List β) (@Array.toList β)
            (@Array.scanlM.loop m β α inst f init as start stop h acc))
          (@Bind.bind m (@Monad.toBind m inst) (List β) (List β)
            (@List.scanlM m β α inst f init
              (@List.take α (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) stop start)
                (@List.drop α start (@Array.toList α as))))
            fun (__do_lift : List β) =>
            @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List β)
              (@HAppend.hAppend (List β) (List β) (List β) (@instHAppendOfAppend (List β) (@List.instAppend β))
                (@Array.toList β acc) __do_lift))) := fun hc_h => absurd (fun hc_k0 => @hc_h (Option : Type → Type) (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.toArray Nat (@List.nil Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.toArray Nat (@List.nil Nat)) ({ pure := some, bind := fun _ _ => none } : Monad Option) (fun (a x : Nat) => @Option.none Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hc_k0) (by
  decide +kernel)

-- Array.scanlM.loop_toList, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.scanlM.loop_toList.h11 : ¬∀ {m : Type → Type} {β α : Type} {init : β} {as : Array α} {start : Nat} {acc : Array β} [inst : Monad m]
        [inst : LawfulMonad m] {f : β → α → m β} {stop : Nat}, stop ≤ as.size := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (0) (#[]) (0) (#[]) (instMonadOption) _ (fun (a x : Nat) => Option.none) (1)) (by
  decide +kernel)

-- Array.scanrM.loop_toList, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.scanrM.loop_toList.h8 : Not
      (∀ {m : Type → Type} {α β : Type} {init : β} {as : Array α} {stop : Nat} {acc : Array β} [inst : Monad m]
        {f : α → β → m β} {start : Nat} {h : @LE.le Nat instLENat start (@Array.size α as)},
        @Eq (m (List β))
          (@Functor.map m (@Applicative.toFunctor m (@Monad.toApplicative m inst)) (Array β) (List β) (@Array.toList β)
            (@Array.scanrM.loop m α β inst f init as start stop h acc))
          (@Bind.bind m (@Monad.toBind m inst) (List β) (List β)
            (@List.scanrM m α β inst f init
              (@List.take α (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) start stop)
                (@List.drop α stop (@Array.toList α as))))
            fun (__do_lift : List β) =>
            @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (List β)
              (@HAppend.hAppend (List β) (List β) (List β) (@instHAppendOfAppend (List β) (@List.instAppend β)) __do_lift
                (@List.reverse β (@Array.toList β acc))))) := fun hc_h => absurd (fun hc_k0 => @hc_h (Option : Type → Type) (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.toArray Nat (@List.nil Nat)) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.toArray Nat (@List.nil Nat)) ({ pure := some, bind := fun _ _ => none } : Monad Option) (fun (a x : Nat) => @Option.none Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) hc_k0) (by
  decide +kernel)

-- Array.scanrM.loop_toList, hypothesis 11: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.scanrM.loop_toList.h11 : ¬∀ {m : Type → Type} {α β : Type} {init : β} {as : Array α} {stop : Nat} {acc : Array β} [inst : Monad m]
        [inst : LawfulMonad m] {f : α → β → m β} {start : Nat}, start ≤ as.size := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (0) (#[]) (0) (#[]) (instMonadOption) _ (fun (a x : Nat) => Option.none) (1)) (by
  decide +kernel)

-- Batteries.AssocList.ltHeadKey_of_le, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_of_le.h6.inst : ¬Batteries.AssocList.LTHeadKey (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0
        (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_of_le.h6.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 1 ≠ Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_of_le.h6.prem1 : Batteries.AssocList.LTHeadKey (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 1
      (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) := by
  decide
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_of_le.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {x a : α} {β : Type} {t : Batteries.AssocList α β},
        cmp x a ≠ Ordering.gt → Batteries.AssocList.LTHeadKey cmp a t → Batteries.AssocList.LTHeadKey cmp x t := fun hc_h => HypCheckProof.Batteries.AssocList.ltHeadKey_of_le.h6.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (1) (Nat) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) HypCheckProof.Batteries.AssocList.ltHeadKey_of_le.h6.prem0 HypCheckProof.Batteries.AssocList.ltHeadKey_of_le.h6.prem1)

-- Batteries.AssocList.ltHeadKey_of_le, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_of_le.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {x a : α} {β : Type} {t : Batteries.AssocList α β} [inst : Std.TransCmp cmp],
        Batteries.AssocList.LTHeadKey cmp a t → Batteries.AssocList.LTHeadKey cmp x t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (1) (0) (Nat) (Batteries.AssocList.cons 1 0 Batteries.AssocList.nil) _ (by
  decide)) (by
  decide +kernel)

-- Batteries.AssocList.ltHeadKey_of_le, hypothesis 8: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_of_le.h8.inst : ¬Batteries.AssocList.LTHeadKey (fun (a b : Nat) => Ord.compare a b) 0
        (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_of_le.h8.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 ≠ Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Batteries.AssocList.ltHeadKey_of_le.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {x a : α} {β : Type} {t : Batteries.AssocList α β} [inst : Std.TransCmp cmp],
        cmp x a ≠ Ordering.gt → Batteries.AssocList.LTHeadKey cmp x t := fun hc_h => HypCheckProof.Batteries.AssocList.ltHeadKey_of_le.h8.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) (0) (0) (Nat) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) _ HypCheckProof.Batteries.AssocList.ltHeadKey_of_le.h8.prem0)

-- Batteries.AssocList.KeysOrdered.orderedInsert, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.KeysOrdered.orderedInsert.h8 : ¬∀ {α : Type} {cmp : α → α → Ordering} {β : Type} {l : Batteries.AssocList α β} {a : α} {b : β}
        [inst : Std.LawfulEqCmp cmp] [inst : Std.OrientedCmp cmp],
        Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.orderedInsert cmp l a b) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) (Batteries.AssocList.cons 0 0 (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil)) (0) (0) _ _) (by
  decide +kernel)

-- List.Perm.inter, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.inter.h7 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l₁ l₂ t₁ t₂ : List α}, t₁.Perm t₂ → (l₁ ∩ t₁).Perm (l₂ ∩ t₂) := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([0]) ([0]) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.Perm.inter, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.inter.h8 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l₁ l₂ t₁ t₂ : List α}, l₁.Perm l₂ → (l₁ ∩ t₁).Perm (l₂ ∩ t₂) := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([0]) ([0]) ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- String.firstDiffPos_loop_eq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.firstDiffPos_loop_eq.h6 : ¬∀ (l₁ l₂ r₁ r₂ : List Char) (stop p : Nat),
        p = String.utf8Len l₂ →
          stop = Min.min (String.utf8Len l₁ + String.utf8Len r₁) (String.utf8Len l₂ + String.utf8Len r₂) →
            String.firstDiffPos.loop (String.ofList (l₁ ++ r₁)) (String.ofList (l₂ ++ r₂))
                { byteIdx := stop : String.Pos.Raw } { byteIdx := p : String.Pos.Raw } =
              {
                byteIdx :=
                  p + String.utf8Len (List.takeWhile₂ (fun (x1 x2 : Char) => Decidable.decide (x1 = x2)) r₁ r₂).fst :
                String.Pos.Raw } := fun hc_h => absurd (@hc_h (['a']) ([]) ([]) (['a']) _ _ rfl rfl) (by
  decide +kernel)

-- String.firstDiffPos_loop_eq, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.firstDiffPos_loop_eq.h7 : ¬∀ (l₁ l₂ r₁ r₂ : List Char) (stop p : Nat),
        p = String.utf8Len l₁ →
          stop = Min.min (String.utf8Len l₁ + String.utf8Len r₁) (String.utf8Len l₂ + String.utf8Len r₂) →
            String.firstDiffPos.loop (String.ofList (l₁ ++ r₁)) (String.ofList (l₂ ++ r₂))
                { byteIdx := stop : String.Pos.Raw } { byteIdx := p : String.Pos.Raw } =
              {
                byteIdx :=
                  p + String.utf8Len (List.takeWhile₂ (fun (x1 x2 : Char) => Decidable.decide (x1 = x2)) r₁ r₂).fst :
                String.Pos.Raw } := fun hc_h => absurd (@hc_h ([]) (['a']) (['a']) ([]) _ _ rfl rfl) (by
  decide +kernel)

-- String.firstDiffPos_loop_eq, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.firstDiffPos_loop_eq.h8 : ¬∀ (l₁ l₂ r₁ r₂ : List Char) (stop p : Nat),
        p = String.utf8Len l₁ →
          p = String.utf8Len l₂ →
            String.firstDiffPos.loop (String.ofList (l₁ ++ r₁)) (String.ofList (l₂ ++ r₂))
                { byteIdx := stop : String.Pos.Raw } { byteIdx := p : String.Pos.Raw } =
              {
                byteIdx :=
                  p + String.utf8Len (List.takeWhile₂ (fun (x1 x2 : Char) => Decidable.decide (x1 = x2)) r₁ r₂).fst :
                String.Pos.Raw } := fun hc_h => absurd (@hc_h ([]) ([]) ([]) ([]) (1) _ rfl (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- List.IsChain.cons_of_imp_of_imp, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons_of_imp_of_imp.h6 : ¬∀ {α : Type} {R S : α → α → Prop} {a : α} {l : List α} {b : α},
        (∀ ⦃c : α⦄, R a c → S b c) → List.IsChain R (a :: l) → List.IsChain S (b :: l) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a ≠ b : Nat → Nat → Prop) (fun a b => a < b : Nat → Nat → Prop) (0) ([1, 0]) (0) (by
  omega) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.cons_of_imp_of_imp, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons_of_imp_of_imp.h7 : ¬∀ {α : Type} {R S : α → α → Prop} {a : α} {l : List α} {b : α},
        (∀ ⦃a b : α⦄, R a b → S a b) → List.IsChain R (a :: l) → List.IsChain S (b :: l) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (fun a b => a < b : Nat → Nat → Prop) (0) ([1]) (1) (by
  simp) (by
  decide)) (by
  decide +kernel)

-- List.IsChain.cons_of_imp_of_imp, hypothesis 8: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.cons_of_imp_of_imp.h8 : ¬∀ {α : Type} {R S : α → α → Prop} {a : α} {l : List α} {b : α},
        (∀ ⦃a b : α⦄, R a b → S a b) → (∀ ⦃c : α⦄, R a c → S b c) → List.IsChain S (b :: l) := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) (fun a b => a < b : Nat → Nat → Prop) (0) ([0]) (0) (by
  simp) (by
  simp)) (by
  decide +kernel)

-- Batteries.BinaryHeap.max_ge_all, hypothesis 6: necessary
/- FAILED: 12:92: failed to synthesize instance of type class
  LT (Array α)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 64:22: Application type mismatch: The argument
  α
has type
  Type
of sort `Type 1` but is expected to have type
  Batteries.BinaryHeap.size ?m.3 > 0
of sort `Prop` in the application
  (fun {α} [Ord α] {heap} h_ne =>
      of_eq_true
        (Eq.trans
          (congrFun'
            (congrArg Eq (congrArg Option.isSome (getElem?_pos heap.arr 0 (id (Eq.mp gt_iff_lt._simp_1 h_ne))))) true)
          (eq_self true)))
    α | 3:163: `grind` failed
case grind
α : Type
y : α
inst : Ord α
inst_1 : Std.TransOrd α
heap : Batteries.BinaryHeap α
h : heap.max.isSome = false
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] Std.TransCmp compare
    [prop] heap.max.isSome = false
  [eqc] True propositions
    [prop] Std.TransCmp compare
  [eqc] Equivalence classes
    [eqc] {false, heap.max.isSome}
  [ematch] E-matching patterns
    [thm] Std.compare_ne_eq: [@compare #7 #6 #1 #0, Ordering.eq]
    [thm] Std.compare_ | 7:199: `grind` failed
case grind
α : Type
y : α
inst : Ord α
inst_1 : Std.TransOrd α
heap : Batteries.BinaryHeap α
h : heap.max.isSome = false
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] Std.TransCmp compare
    [prop] heap.max.isSome = false
  [eqc] True propositions
    [prop] Std.TransCmp compare
  [eqc] Equivalence classes
    [eqc] {false, heap.max.isSome}
  [ematch] E-matching patterns
    [thm] Std.compare_ne_eq: [@compare #7 #6 #1 #0, Ordering.eq]
    [thm] Std.compare_ | 11:90: failed to synthesize instance of type class
  LT (Array α)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. | 74:20: Application type mismatch: The argument
  Nat
has type
  Type
of sort `Type 1` but is expected to have type
  Batteries.BinaryHeap.size ?m.3 > 0
of sort `Prop` in the application
  (fun {α} [Ord α] {heap} h_ne =>
      of_eq_true
        (Eq.trans
          (congrFun'
            (congrArg Eq (congrArg Option.isSome (getElem?_pos heap.arr 0 (id (Eq.mp gt_iff_lt._simp_1 h_ne))))) true)
          (eq_self true)))
    Nat | 7:163: `grind` failed
case grind
α : Type
y : α
inst : Ord α
inst_1 : Std.TransOrd α
heap : Batteries.BinaryHeap α
h : heap.max.isSome = false
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] Std.TransCmp compare
    [prop] heap.max.isSome = false
  [eqc] True propositions
    [prop] Std.TransCmp compare
  [eqc] Equivalence classes
    [eqc] {false, heap.max.isSome}
  [ematch] E-matching patterns
    [thm] Std.compare_ne_eq: [@compare #7 #6 #1 #0, Ordering.eq]
    [thm] Std.compare_ | 29:199: `grind` failed
case grind
α : Type
y : α
inst : Ord α
inst_1 : Std.TransOrd α
heap : Batteries.BinaryHeap α
h : heap.max.isSome = false
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] Std.TransCmp compare
    [prop] heap.max.isSome = false
  [eqc] True propositions
    [prop] Std.TransCmp compare
  [eqc] Equivalence classes
    [eqc] {false, heap.max.isSome}
  [ematch] E-matching patterns
    [thm] Std.compare_ne_eq: [@compare #7 #6 #1 #0, Ordering.eq]
    [thm] Std.compare_
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.max_ge_all.h6 : ¬∀ {α : Type} {y : α} [inst : Ord α] [inst_1 : Std.TransOrd α] {heap : Batteries.BinaryHeap α},
        heap.WF →
          ∀ (h_ne : heap.size > 0),
            (Ord.compare
                  (heap.max.get
                    ((fun {α : Type} [Ord α] {heap : Batteries.BinaryHeap α} (h_ne : heap.size > 0) =>
                        of_eq_true
                          (Eq.trans
                            (congrFun'
                              (congrArg Eq
                                (congrArg Option.isSome (getElem?_pos heap.arr 0 (id (Eq.mp gt_iff_lt._simp_1 h_ne)))))
                              Bool.true)
                            (eq_self Bool.true)))
                      h_ne))
                  y).isGE =
              Bool.true := fun hc_h => absurd (fun hc_k0 hc_k1 => @hc_h (Nat) (1) (instOrdNat) _ ({ arr := #[0] : Batteries.BinaryHeap Nat }) hc_k0 hc_k1) (by
  decide +kernel)
-/

-- Batteries.OrderedAssocList.ext, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.ext.h7 : Not
      (∀ {α : Type} {cmp : α → α → Ordering} {β : Type} [inst : @Std.LawfulEqCmp α cmp] [inst : @Std.TransCmp α cmp]
        {l₁ l₂ : @Batteries.OrderedAssocList α cmp β}, @Eq (@Batteries.OrderedAssocList α cmp β) l₁ l₂) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (Nat) _ _ (@Batteries.OrderedAssocList.mk Nat (fun (a b : Nat) => @Ord.compare Nat instOrdNat a b) Nat
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

-- List.IsPrefix.interleave, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.interleave.h5 : ¬∀ {α : Type} {l₁ l₃ l₂ l₄ : List α}, l₁ <+: l₃ → l₂ <+: l₄ → l₁.interleave l₂ <+: l₃.interleave l₄ := fun hc_h => absurd (@hc_h (Nat) ([]) ([1]) ([0]) ([0]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.IsPrefix.interleave, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.interleave.h6 : ¬∀ {α : Type} {l₁ l₃ l₂ l₄ : List α},
        l₁.length = l₂.length ∨ l₁.length = l₂.length + 1 → l₂ <+: l₄ → l₁.interleave l₂ <+: l₃.interleave l₄ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([]) ([]) ([]) (by
  decide) (by
  decide)) (by
  decide +kernel)

-- List.IsPrefix.interleave, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsPrefix.interleave.h7 : ¬∀ {α : Type} {l₁ l₃ l₂ l₄ : List α},
        l₁.length = l₂.length ∨ l₁.length = l₂.length + 1 → l₁ <+: l₃ → l₁.interleave l₂ <+: l₃.interleave l₄ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([0]) ([0]) ([]) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)) (by
  decide)) (by
  decide +kernel)

-- Batteries.OrderedAssocList.filterMapVal_filterMapVal, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.filterMapVal_filterMapVal.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} {γ δ β : Type} [inst : Std.LawfulEqCmp cmp] {f : α → γ → Option δ}
        {g : α → β → Option γ} {l : Batteries.OrderedAssocList cmp β}, Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (Nat) (Nat) (Nat) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (fun (a x : Nat) => Option.none) (fun (a x : Nat) => Option.none) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat })) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.TransCmp.lt_of_lt_of_le, hypothesis 2: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h2.inst : ¬(fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 0 = Ordering.lt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h2.prem0 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 0 1 = Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h2.prem1 : (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) 1 0 ≠ Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} {x y z : α},
        cmp x y = Ordering.lt → cmp y z ≠ Ordering.gt → cmp x z = Ordering.lt := fun hc_h => HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h2.inst (@hc_h (Nat) (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) (0) (1) (0) HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h2.prem0 HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h2.prem1)

-- Std.TransCmp.lt_of_lt_of_le, hypothesis 6: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h6.inst : ¬(fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.lt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h6.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 0 ≠ Ordering.gt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {x y z : α},
        cmp y z ≠ Ordering.gt → cmp x z = Ordering.lt := fun hc_h => HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h6.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (0) (0) (0) HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h6.prem0)

-- Std.TransCmp.lt_of_lt_of_le, hypothesis 7: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h7.inst : ¬(fun (a b : Nat) => Ord.compare a b) 0 0 = Ordering.lt := by
  decide +kernel
set_option maxHeartbeats 300 in
theorem HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h7.prem0 : (fun (a b : Nat) => Ord.compare a b) 0 1 = Ordering.lt := by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide)
theorem HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {x y z : α},
        cmp x y = Ordering.lt → cmp x z = Ordering.lt := fun hc_h => HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h7.inst (@hc_h (Nat) (fun (a b : Nat) => Ord.compare a b) _ (0) (1) (0) HypCheckProof.Std.TransCmp.lt_of_lt_of_le.h7.prem0)

-- List.getElem_partialProds, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_partialProds.h7 : ¬∀ {α : Type} {i : Nat} [inst : Mul α] [inst_1 : One α] [inst_2 : Std.Associative fun (x1 x2 : α) => x1 * x2]
        [inst_3 : Std.LawfulIdentity (fun (x1 x2 : α) => x1 * x2) 1] {l : List α}, i < l.partialProds.length := fun hc_h => absurd (@hc_h (Nat) (1) (instMulNat) (One.ofOfNat1) _ _ ([])) (by
  decide +kernel)

-- Batteries.OrderedAssocList.contains_insert_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.contains_insert_self.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {β : Type} (l : Batteries.OrderedAssocList cmp β)
        (a : α) (b : β), Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (x x_1 : Bool) => Ordering.eq) Nat }) (Bool.false) (0)) (by
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

-- Batteries.OrderedAssocList.contains_insert_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.contains_insert_self.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {β : Type} (l : Batteries.OrderedAssocList cmp β)
        (a : α) (b : β), Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat }) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.OrderedAssocList.length_insert_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.length_insert_ne_zero.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.OrientedCmp cmp] {β : Type} {a : α} {b : β}
        {l : Batteries.OrderedAssocList cmp β}, Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) (Bool.false) (0) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
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

-- Batteries.OrderedAssocList.length_insert_ne_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.length_insert_ne_zero.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {β : Type} {a : α} {b : β}
        {l : Batteries.OrderedAssocList cmp β}, Std.OrientedCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) (0) (0) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat })) (by
  exact fun hc_c =>
    absurd (hc_c.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.OrderedAssocList.getElem?_insert_self, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_insert_self.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.TransCmp cmp] {β : Type} (l : Batteries.OrderedAssocList cmp β)
        (a : α) (b : β), Std.LawfulEqCmp cmp := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) _ (Nat) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (x x_1 : Bool) => Ordering.eq) Nat }) (Bool.false) (0)) (by
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

-- Batteries.OrderedAssocList.getElem?_insert_self, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_insert_self.h3 : ¬∀ {α : Type} {cmp : α → α → Ordering} [inst : Std.LawfulEqCmp cmp] {β : Type} (l : Batteries.OrderedAssocList cmp β)
        (a : α) (b : β), Std.TransCmp cmp := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (@Std.LawfulEqCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (@Std.ReflCmp.mk (Nat) (fun (a b : Nat) => @ite Ordering (@Eq Nat a b) (instDecidableEqNat a b) Ordering.eq Ordering.lt) (by (try dsimp only);   (intros; simp_all; done))) (by (try dsimp only);   (intros; simp_all; done))) (Nat) ({ toAssocList := Batteries.AssocList.nil, keysOrdered := of_decide_eq_true (id (Eq.refl Bool.true)) :
      Batteries.OrderedAssocList (fun (a b : Nat) => if a = b then Ordering.eq else Ordering.lt) Nat }) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Batteries.OrderedAssocList.contains_mk_cons_self, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.contains_mk_cons_self.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {b : β} {t : Batteries.AssocList α β}
        {h : Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons a b t)},
        { toAssocList := Batteries.AssocList.cons a b t, keysOrdered := h : Batteries.OrderedAssocList cmp β }.contains a =
          Bool.true := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Bool.false) (Nat) (0) (Batteries.AssocList.nil) hc_k0) (by
  decide +kernel)

-- Batteries.OrderedAssocList.contains_mk_cons_self, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.contains_mk_cons_self.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {b : β} {t : Batteries.AssocList α β}
        [inst : Std.OrientedCmp cmp], Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons a b t) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (0) (Nat) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) _) (by
  decide +kernel)

-- List.idxOfNth_eq_idxOfNth_of_ge_countP_ge_countP, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_eq_idxOfNth_of_ge_countP_ge_countP.h6 : ¬∀ {α : Type} {x : α} {n m : Nat} [inst : BEq α] {xs : List α},
        List.count x xs ≤ m → List.idxOfNth x xs n = List.idxOfNth x xs m := fun hc_h => absurd (@hc_h (Nat) (0) (0) (1) (instBEqOfDecidableEq) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.idxOfNth_eq_idxOfNth_of_ge_countP_ge_countP, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_eq_idxOfNth_of_ge_countP_ge_countP.h7 : ¬∀ {α : Type} {x : α} {n m : Nat} [inst : BEq α] {xs : List α},
        List.count x xs ≤ n → List.idxOfNth x xs n = List.idxOfNth x xs m := fun hc_h => absurd (@hc_h (Nat) (0) (1) (0) (instBEqOfDecidableEq) ([0]) (by
  decide)) (by
  decide +kernel)

-- Batteries.OrderedAssocList.getElem?_mk_cons_self, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_mk_cons_self.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {b : β} {t : Batteries.AssocList α β}
        {h : Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons a b t)},
        { toAssocList := Batteries.AssocList.cons a b t, keysOrdered := h : Batteries.OrderedAssocList cmp β }[a]? =
          Option.some b := fun hc_h => absurd (fun hc_k0 => @hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Bool.false) (Nat) (0) (Batteries.AssocList.nil) hc_k0) (by
  decide +kernel)

-- Batteries.OrderedAssocList.getElem?_mk_cons_self, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.getElem?_mk_cons_self.h7 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {b : β} {t : Batteries.AssocList α β}
        [inst : Std.OrientedCmp cmp], Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons a b t) := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (0) (Nat) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) _) (by
  decide +kernel)

-- List.Subperm.idxInj_inj, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.idxInj_inj.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α} {h : xs.Subperm ys} (i j : Fin xs.length), LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) ([0]) (by
  decide) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
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

-- List.Subperm.idxInj_inj, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.idxInj_inj.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {xs ys : List α} (i j : Fin xs.length), xs.Subperm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([0]) ([]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.getElem_getElem_idxsOf_sub_of_lawful, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_getElem_idxsOf_sub_of_lawful.h5 : ¬∀ {α : Type} {i : Nat} {xs : List α} {x : α} [inst : BEq α] (s : Nat) (h : i < (List.idxsOf x xs s).length),
        GetElem.getElem xs (GetElem.getElem (List.idxsOf x xs s) i h - s) (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = x := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (0) ([0]) (1) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) (0) hc_k0) (by
  decide +kernel)

-- List.getElem_getElem_idxsOf_sub_of_lawful, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_getElem_idxsOf_sub_of_lawful.h7 : ¬∀ {α : Type} {i : Nat} {xs : List α} {x : α} [inst : BEq α] [inst_1 : LawfulBEq α] (s : Nat),
        i < (List.idxsOf x xs s).length := fun hc_h => absurd (@hc_h (Nat) (0) ([]) (0) (instBEqOfDecidableEq) _ (0)) (by
  decide +kernel)

-- List.Sublist.erase_diff_erase_sublist, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.erase_diff_erase_sublist.h2 : ¬∀ {α : Type} [inst : BEq α] {a : α} {l₁ l₂ : List α},
        l₁.Sublist l₂ → ((l₂.erase a).diff (l₁.erase a)).Sublist (l₂.diff l₁) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : BEq Nat) (1) ([0]) ([1, 0]) (by
  decide)) (by
  decide +kernel)

-- List.Sublist.diff_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.diff_right.h2 : ¬∀ {α : Type} [inst : BEq α] {l₁ l₂ l₃ : List α}, l₁.Sublist l₂ → (l₁.diff l₃).Sublist (l₂.diff l₃) := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : BEq Nat) ([0]) ([0, 1]) ([1]) (by
  decide)) (by
  decide +kernel)

-- List.Sublist.diff_right, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Sublist.diff_right.h6 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l₁ l₂ l₃ : List α}, (l₁.diff l₃).Sublist (l₂.diff l₃) := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([0]) ([]) ([])) (by
  decide +kernel)

-- Batteries.BinomialHeap.Imp.Heap.rankGT.of_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinomialHeap.Imp.Heap.rankGT.of_le.h4 : ¬∀ {α : Type} {s : Batteries.BinomialHeap.Imp.Heap α} {n n' : Nat}, n' ≤ n → s.rankGT n' := fun hc_h => absurd (@hc_h (Nat) (Batteries.BinomialHeap.Imp.Heap.cons 0 0 Batteries.BinomialHeap.Imp.HeapNode.nil Batteries.BinomialHeap.Imp.Heap.nil) (0) (0) (by
  decide)) (by
  decide +kernel)

-- Batteries.BinomialHeap.Imp.Heap.rankGT.of_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinomialHeap.Imp.Heap.rankGT.of_le.h5 : ¬∀ {α : Type} {s : Batteries.BinomialHeap.Imp.Heap α} {n n' : Nat}, s.rankGT n → s.rankGT n' := fun hc_h => absurd (@hc_h (Nat) (Batteries.BinomialHeap.Imp.Heap.cons 1 0 Batteries.BinomialHeap.Imp.HeapNode.nil Batteries.BinomialHeap.Imp.Heap.nil) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Fin.eq_false_of_findRev?_eq_some_of_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.eq_false_of_findRev?_eq_some_of_lt.h3 : ¬∀ {n : Nat} {i : Fin n} {p : Fin n → Bool} (j : Fin n), i < j → p j = Bool.false := fun hc_h => absurd (@hc_h (2) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (fun (a : Fin 2) => Bool.true) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide)) (by
  decide +kernel)

-- Fin.eq_false_of_findRev?_eq_some_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.eq_false_of_findRev?_eq_some_of_lt.h5 : ¬∀ {n : Nat} {i : Fin n} {p : Fin n → Bool}, Fin.findRev? p = Option.some i → ∀ (j : Fin n), p j = Bool.false := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (fun (a : Fin 1) => Bool.true) (by
  decide) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- List.IsChain.getElem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.getElem.h3 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} (i : Nat) (hi : i + 1 < l.length), R l[i] l[i + 1] := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) ([1, 0]) (0) hc_k0) (by
  decide +kernel)

-- List.IsChain.getElem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.getElem.h5 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α}, List.IsChain R l → ∀ (i : Nat), i + 1 < l.length := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) ([]) (by
  decide) (0)) (by
  decide +kernel)

-- Batteries.PairingHeapImp.Heap.size_tail?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.PairingHeapImp.Heap.size_tail?.h4 : ¬∀ {α : Type} {le : α → α → Bool} {s' s : Batteries.PairingHeapImp.Heap α},
        Batteries.PairingHeapImp.Heap.tail? le s = Option.some s' → s.size = s'.size + 1 := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (Batteries.PairingHeapImp.Heap.nil) (Batteries.PairingHeapImp.Heap.node 0 Batteries.PairingHeapImp.Heap.nil
      (Batteries.PairingHeapImp.Heap.node 0 Batteries.PairingHeapImp.Heap.nil Batteries.PairingHeapImp.Heap.nil)) (by
  rfl)) (by
  decide +kernel)

-- Batteries.PairingHeapImp.Heap.size_tail?, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.PairingHeapImp.Heap.size_tail?.h5 : ¬∀ {α : Type} {le : α → α → Bool} {s' s : Batteries.PairingHeapImp.Heap α}, s.NoSibling → s.size = s'.size + 1 := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (Batteries.PairingHeapImp.Heap.nil) (Batteries.PairingHeapImp.Heap.nil) (by
  decide)) (by
  decide +kernel)

-- List.count_getElem_take_succ, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.count_getElem_take_succ.h2 : ¬∀ {α : Type} [inst : BEq α] {xs : List α} {i : Nat} {hi : i < xs.length},
        List.count xs[i] (List.take (i + 1) xs) = List.count xs[i] (List.take i xs) + 1 := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (⟨fun a b => a != b⟩ : BEq Nat) ([0]) (0) hc_k0) (by
  decide +kernel)

-- List.count_getElem_take_succ, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.count_getElem_take_succ.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : EquivBEq α] {xs : List α} {i : Nat}, i < xs.length := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) (0)) (by
  decide +kernel)

-- List.swap_eq_of_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.swap_eq_of_lt.h4 : ¬∀ {α : Type} {i j : Nat} {xs : List α}, j < xs.length → i < xs.length := fun hc_h => absurd (@hc_h (Nat) (1) (0) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.swap_eq_of_lt, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.swap_eq_of_lt.h5 : ¬∀ {α : Type} {i j : Nat} {xs : List α}, i < xs.length → j < xs.length := fun hc_h => absurd (@hc_h (Nat) (0) (1) ([0]) (by
  decide)) (by
  decide +kernel)

-- List.countBefore_lt_count_getElem, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countBefore_lt_count_getElem.h3 : ¬∀ {α : Type} {i : Nat} [inst : BEq α] {xs : List α} {h : i < xs.length},
        List.countBefore xs[i] xs i < List.count xs[i] xs := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (0) (⟨fun a b => a != b⟩ : BEq Nat) ([0]) hc_k0) (by
  decide +kernel)

-- List.countBefore_lt_count_getElem, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countBefore_lt_count_getElem.h5 : ¬∀ {α : Type} {i : Nat} [inst : BEq α] [inst : ReflBEq α] {xs : List α}, i < xs.length := fun hc_h => absurd (@hc_h (Nat) (0) (instBEqOfDecidableEq) _ ([])) (by
  decide +kernel)

-- List.Subperm.trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.trans.h4 : ¬∀ {α : Type} {l₁ l₂ l₃ : List α}, l₂.Subperm l₃ → l₁.Subperm l₃ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.Subperm.trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.trans.h5 : ¬∀ {α : Type} {l₁ l₂ l₃ : List α}, l₁.Subperm l₂ → l₁.Subperm l₃ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([0]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.subperm_append_diff_self_of_count_le, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.subperm_append_diff_self_of_count_le.h2 : ¬∀ {α : Type} [inst : BEq α] {l₁ l₂ : List α},
        (∀ (x : α), x ∈ l₁ → List.count x l₁ ≤ List.count x l₂) → (l₁ ++ l₂.diff l₁).Perm l₂ := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([0]) ([1]) (by
  decide)) (by
  decide +kernel)

-- List.subperm_append_diff_self_of_count_le, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.subperm_append_diff_self_of_count_le.h5 : ¬∀ {α : Type} [inst : BEq α] [inst_1 : LawfulBEq α] {l₁ l₂ : List α}, (l₁ ++ l₂.diff l₁).Perm l₂ := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([0]) ([])) (by
  decide +kernel)

-- List.disjoint_take_drop, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.disjoint_take_drop.h5 : ¬∀ {α : Type} {m n : Nat} {l : List α}, l.Nodup → (List.take m l).Disjoint (List.drop n l) := fun hc_h => absurd (@hc_h (Nat) (1) (0) ([0]) (by
  decide)) (by
  simp)

-- List.findIdxNth_countPBefore_of_lt_length_of_pos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdxNth_countPBefore_of_lt_length_of_pos.h4 : ¬∀ {α : Type} {i : Nat} {p : α → Bool} {xs : List α}, i < xs.length := fun hc_h => absurd (@hc_h (Nat) (0) (fun n => n % 2 == 0 : Nat → Bool) ([])) (by
  decide +kernel)

-- List.findIdxNth_countPBefore_of_lt_length_of_pos, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.findIdxNth_countPBefore_of_lt_length_of_pos.h5 : ¬∀ {α : Type} {i : Nat} {p : α → Bool} {xs : List α} {h : i < xs.length},
        List.findIdxNth p xs (List.countPBefore p xs i) = i := fun hc_h => absurd (@hc_h (Nat) (0) (fun n => n % 2 == 0 : Nat → Bool) ([1]) (by
  decide)) (by
  decide +kernel)

-- Std.OrientedOrd.isGE_of_isLT, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.OrientedOrd.isGE_of_isLT.h2 : ¬∀ {α : Type} [inst : Ord α] {a b : α}, (Ord.compare b a).isLT = Bool.true → (Ord.compare a b).isGE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (0) (1) (by
  decide)) (by
  decide +kernel)

-- Std.OrientedOrd.isGE_of_isLT, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.OrientedOrd.isGE_of_isLT.h5 : ¬∀ {α : Type} [inst : Ord α] [inst_1 : Std.OrientedOrd α] {a b : α}, (Ord.compare a b).isGE = Bool.true := fun hc_h => absurd (@hc_h (Nat) (instOrdNat) _ (0) (1)) (by
  decide +kernel)

-- List.count_getElem_take_lt_count, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.count_getElem_take_lt_count.h2 : ¬∀ {α : Type} [inst : BEq α] {xs : List α} {i : Nat} {hi : i < xs.length},
        List.count xs[i] (List.take i xs) < List.count xs[i] xs := fun hc_h => absurd (fun hc_k0 => @hc_h (Nat) (⟨fun a b => a != b⟩ : BEq Nat) ([0]) (0) hc_k0) (by
  decide +kernel)

-- List.count_getElem_take_lt_count, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.count_getElem_take_lt_count.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : EquivBEq α] {xs : List α} {i : Nat}, i < xs.length := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) (0)) (by
  decide +kernel)

-- Substring.Raw.Valid.prev, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.prev.h5 : ¬∀ {m₁ : List Char} {c : Char} {m₂ : List Char} {s : Substring.Raw},
        s.Valid →
          s.prev { byteIdx := String.utf8Len m₁ + c.utf8Size : String.Pos.Raw } =
            { byteIdx := String.utf8Len m₁ : String.Pos.Raw } := fun hc_h => absurd (@hc_h ([]) ('é') ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) ((@Substring.Raw.Valid.mk ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   decide)))) (by
  decide +kernel)

-- List.Perm.idxBij_injective, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_injective.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α}, xs.Perm ys → LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) ([]) (by
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

-- List.Perm.idxBij_injective, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_injective.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {xs ys : List α}, xs.Perm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([0])) (by
  decide +kernel)

-- List.sum_flatten, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.sum_flatten.h3 : ¬∀ {α : Type} [inst : Add α] [inst_1 : Zero α] [inst_2 : Std.Associative fun (x1 x2 : α) => x1 + x2]
        {l : List (List α)}, l.flatten.sum = (List.map List.sum l).sum := fun hc_h => absurd (@hc_h (Nat) (instAddNat) (⟨1⟩ : Zero Nat) _ ([[]])) (by
  decide +kernel)

-- List.Perm.idxBij_rightInverse_idxBij_symm, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_rightInverse_idxBij_symm.h2 : ¬∀ {α : Type} [inst : BEq α] {xs ys : List α}, xs.Perm ys → LawfulBEq α := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a / 2 == b / 2⟩ : BEq Nat) ([]) ([]) (by
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

-- List.Perm.idxBij_rightInverse_idxBij_symm, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.idxBij_rightInverse_idxBij_symm.h5 : ¬∀ {α : Type} [inst : BEq α] [inst : LawfulBEq α] {xs ys : List α}, xs.Perm ys := fun hc_h => absurd (@hc_h (Nat) (instBEqOfDecidableEq) _ ([]) ([0])) (by
  decide +kernel)

-- Substring.Raw.Valid.nextn, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.nextn.h3 : ¬∀ {m₁ m₂ : List Char} {s : Substring.Raw},
        s.toString.toList = m₁ ++ m₂ →
          ∀ (n : Nat),
            s.nextn n { byteIdx := String.utf8Len m₁ : String.Pos.Raw } =
              { byteIdx := String.utf8Len m₁ + String.utf8Len (List.take n m₂) : String.Pos.Raw } := fun hc_h => absurd (@hc_h ([]) ([]) ({ str := "", startPos := { byteIdx := 1 : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) (by
  decide) (1)) (by
  decide +kernel)

-- Substring.Raw.Valid.nextn, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.nextn.h4 : ¬∀ {m₁ m₂ : List Char} {s : Substring.Raw},
        s.Valid →
          ∀ (n : Nat),
            s.nextn n { byteIdx := String.utf8Len m₁ : String.Pos.Raw } =
              { byteIdx := String.utf8Len m₁ + String.utf8Len (List.take n m₂) : String.Pos.Raw } := fun hc_h => absurd (@hc_h ([]) (['a']) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) ((@Substring.Raw.Valid.mk ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   (intros; simp_all; done)) (by (try dsimp only);   decide))) (1)) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.nextn, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.nextn.h3 : ¬∀ {l r : List Char} {it : String.Legacy.Iterator} (n : Nat),
        n ≤ r.length → String.Legacy.Iterator.ValidFor ((List.take n r).reverse ++ l) (List.drop n r) (it.nextn n) := fun hc_h => absurd (@hc_h ([]) ([]) ({ s := "", i := { byteIdx := 1 : String.Pos.Raw } : String.Legacy.Iterator }) (0) (by
  decide)) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.nextn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.nextn.h5 : ¬∀ {l r : List Char} {it : String.Legacy.Iterator},
        String.Legacy.Iterator.ValidFor l r it →
          ∀ (n : Nat), String.Legacy.Iterator.ValidFor ((List.take n r).reverse ++ l) (List.drop n r) (it.nextn n) := fun hc_h => absurd (@hc_h ([]) ([]) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator }) (by
  decide) (1)) (by
  decide +kernel)

-- Batteries.UnionFind.Equiv.trans, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.Equiv.trans.h4 : ¬∀ {self : Batteries.UnionFind} {a b c : Nat}, self.Equiv b c → self.Equiv a c := fun hc_h => absurd (@hc_h (Batteries.UnionFind.empty : Batteries.UnionFind) (1) (0) (0) (by
  rfl)) (by
  simp)

-- Batteries.UnionFind.Equiv.trans, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.Equiv.trans.h5 : ¬∀ {self : Batteries.UnionFind} {a b c : Nat}, self.Equiv a b → self.Equiv a c := fun hc_h => absurd (@hc_h (Batteries.UnionFind.empty : Batteries.UnionFind) (0) (0) (1) (by
  rfl)) (by
  simp)

-- ByteArray.get_set_ne, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ByteArray.get_set_ne.h4 : ¬∀ {j : Nat} (a : ByteArray) (i : Fin a.size) (v : UInt8), ↑i ≠ j → j < a.size := fun hc_h => absurd (@hc_h (1) ({ data := #[UInt8.ofNat 0] : ByteArray }) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (UInt8.ofNat 0) (by
  (simp only [Array.perm_iff_toList_perm, Vector.perm_iff_toList_perm] <;> decide))) (by
  decide +kernel)

-- ByteArray.get_set_ne, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ByteArray.get_set_ne.h5 : ¬∀ {j : Nat} (a : ByteArray) (i : Fin a.size) (v : UInt8) (hj : j < a.size),
        GetElem.getElem (a.set (↑i) v (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)) j (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind) = GetElem.getElem a j hj := fun hc_h => absurd (fun hc_k0 => @hc_h (0) ({ data := #[UInt8.ofNat 0] : ByteArray }) ((⟨0, (by first | assumption | infer_instance | rfl | decide | omega | get_elem_tactic | (simp_all; done) | grind)⟩ : Fin 1)) (UInt8.ofNat 1) hc_k0) (by
  decide +kernel)

-- ForInStep.bindList_cons', hypothesis 4: necessary
set_option maxHeartbeats 300 in
theorem HypCheckProof.ForInStep.bindList_cons'.h4.inst : Not
      (@Eq (Option (ForInStep Nat))
        (@ForInStep.bindList Option Nat Nat
          (@Monad.mk Option
            (@Applicative.mk Option instFunctorOption (@Pure.mk Option fun {α : Type} => @Option.some α)
              (@Applicative.toSeq Option (@Alternative.toApplicative Option instAlternativeOption))
              (@Applicative.toSeqLeft Option (@Alternative.toApplicative Option instAlternativeOption))
              (@Applicative.toSeqRight Option (@Alternative.toApplicative Option instAlternativeOption)))
            (@Bind.mk Option fun {α β : Type} (x : Option α) (x_1 : α → Option β) => @Option.none β))
          (fun (a a_1 : Nat) => @Option.none (ForInStep Nat))
          (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))
          (@ForInStep.done Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@Option.none (ForInStep Nat))) := by
  decide +kernel
theorem HypCheckProof.ForInStep.bindList_cons'.h4 : Not
      (∀ {m : Type → Type} {α β : Type} [inst : Monad m] (f : α → β → m (ForInStep β)) (s : ForInStep β) (a : α)
        (l : List α),
        @Eq (m (ForInStep β)) (@ForInStep.bindList m α β inst f (@List.cons α a l) s)
          (@Bind.bind m (@Monad.toBind m inst) (ForInStep β) (ForInStep β) (@ForInStep.bind m β inst s (f a))
            fun (x : ForInStep β) => @ForInStep.bindList m α β inst f l x)) := fun hc_h => HypCheckProof.ForInStep.bindList_cons'.h4.inst (@hc_h (Option) (Nat) (Nat) (@Monad.mk Option
      (@Applicative.mk Option instFunctorOption (@Pure.mk Option fun {α : Type} => @Option.some α)
        (@Applicative.toSeq Option (@Alternative.toApplicative Option instAlternativeOption))
        (@Applicative.toSeqLeft Option (@Alternative.toApplicative Option instAlternativeOption))
        (@Applicative.toSeqRight Option (@Alternative.toApplicative Option instAlternativeOption)))
      (@Bind.mk Option fun {α β : Type} (x : Option α) (x_1 : α → Option β) => @Option.none β)) (fun (a a_1 : Nat) => @Option.none (ForInStep Nat)) (@ForInStep.done Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat))

-- Vector.toArray_scanrM, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.toArray_scanrM.h6 : ¬∀ {m : Type → Type} {α β : Type} {n : Nat} {init : β} [inst : Monad m] {f : α → β → m β} {as : Vector α n},
        Vector.toArray <$> Vector.scanrM f init as = Array.scanrM f init as.toArray := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) (0) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (#v[])) (by
  decide +kernel)

-- Vector.scanlM_reverse, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.scanlM_reverse.h6 : ¬∀ {m : Type → Type} {β α : Type} {n : Nat} {init : β} [inst : Monad m] {f : β → α → m β} {as : Vector α n},
        Vector.scanlM f init as.reverse = Vector.reverse <$> Vector.scanrM (flip f) init as := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) (0) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (#v[])) (by
  decide +kernel)

-- Array.scanlM_eq_scanlM_toList, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.scanlM_eq_scanlM_toList.h5 : ¬∀ {m : Type → Type} {β α : Type} {init : β} [inst : Monad m] {f : β → α → m β} {as : Array α},
        Array.scanlM f init as = List.toArray <$> List.scanlM f init as.toList := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (#[])) (by
  decide +kernel)

-- Array.scanrM_pure, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.scanrM_pure.h5 : Not
      (∀ {m : Type → Type} {α β : Type} {init : β} [inst : Monad m] {f : α → β → β} {as : Array α},
        @Eq (m (Array β))
          (@Array.scanrM m α β inst
            (fun (x1 : α) (x2 : β) => @Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) β (f x1 x2)) init
            as (@Array.size α as) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Pure.pure m (@Applicative.toPure m (@Monad.toApplicative m inst)) (Array β)
            (@Array.scanr α β f init as (@Array.size α as) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) := fun hc_h => absurd (@hc_h (Option : Type → Type) (Nat) (Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ({ pure := some, bind := fun _ _ => none } : Monad Option) (fun a b => a - b : Nat → Nat → Nat) (@List.toArray Nat (@List.cons Nat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.nil Nat)))) (by
  decide +kernel)

-- Array.toList_scanrM, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Array.toList_scanrM.h5 : ¬∀ {m : Type → Type} {α β : Type} {init : β} [inst : Monad m] {f : α → β → m β} {as : Array α},
        Array.toList <$> Array.scanrM f init as = List.scanrM f init as.toList := fun hc_h => absurd (@hc_h (fun α => Nat × α : Type → Type) (Nat) (Nat) (0) ({ pure := fun a => (0, a), bind := fun x f => ((f x.2).1 + x.1 + 1, (f x.2).2) } : Monad fun (α : Type) => Nat × α) (fun (a a_1 : Nat) => (0, 0)) (#[])) (by
  decide +kernel)

-- Batteries.BinaryHeap.toSortedArray_sorted, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.toSortedArray_sorted.h4 : ¬∀ {α : Type} [inst : Ord α] [inst_1 : Std.TransOrd α] {heap : Batteries.BinaryHeap α},
        List.Pairwise (fun (x1 x2 : α) => (Ord.compare x1 x2).isGE = Bool.true) heap.toSortedArray.toList := fun hc_h => absurd (@hc_h (Nat) (instOrdNat) _ ({ arr := #[0, 1] : Batteries.BinaryHeap Nat })) (by
  decide +kernel)

-- Std.instTransCmpCompareLex_batteries, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.instTransCmpCompareLex_batteries.h3 : ¬∀ {α : Type} {cmp₁ cmp₂ : α → α → Ordering} [inst₂ : Std.TransCmp cmp₂], Std.TransCmp (compareLex cmp₁ cmp₂) := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (fun a b => compare a b : Nat → Nat → Ordering) _) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.instTransCmpCompareLex_batteries, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.instTransCmpCompareLex_batteries.h4 : ¬∀ {α : Type} {cmp₁ cmp₂ : α → α → Ordering} [inst₁ : Std.TransCmp cmp₁], Std.TransCmp (compareLex cmp₁ cmp₂) := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (fun _ _ => .lt : Bool → Bool → Ordering) _) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (Bool.false : Bool)) (b := (Bool.false : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.Subperm.antisymm, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.antisymm.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₂.Subperm l₁ → l₁.Perm l₂ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([]) (by
  decide)) (by
  decide +kernel)

-- List.Subperm.antisymm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.antisymm.h4 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.Subperm l₂ → l₁.Perm l₂ := fun hc_h => absurd (@hc_h (Nat) ([]) ([0]) (by
  decide)) (by
  decide +kernel)

-- Std.instOrientedCmpCompareLex_batteries, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.instOrientedCmpCompareLex_batteries.h3 : ¬∀ {α : Type} {cmp₁ cmp₂ : α → α → Ordering} [inst₂ : Std.OrientedCmp cmp₂], Std.OrientedCmp (compareLex cmp₁ cmp₂) := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering) (fun a b => compare a b : Nat → Nat → Ordering) _) (by
  exact fun hc_c =>
    absurd (hc_c.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Std.instOrientedCmpCompareLex_batteries, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.instOrientedCmpCompareLex_batteries.h4 : ¬∀ {α : Type} {cmp₁ cmp₂ : α → α → Ordering} [inst₁ : Std.OrientedCmp cmp₁], Std.OrientedCmp (compareLex cmp₁ cmp₂) := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .eq : Bool → Bool → Ordering) (fun _ _ => .lt : Bool → Bool → Ordering) _) (by
  exact fun hc_c =>
    absurd (hc_c.eq_swap (a := (Bool.false : Bool)) (b := (Bool.false : Bool)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Substring.Raw.ValidFor.foldl, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.foldl.h7 : ¬∀ {α : Type} {l : List Char} {m : List Char} {r : List Char} (f : α → Char → α) (init : α) {s : Substring.Raw},
        Substring.Raw.Legacy.foldl f init s = List.foldl f init m := fun hc_h => absurd (@hc_h (Nat) ([]) (['a']) ([]) (fun (a : Nat) (a_1 : Char) => 0) (1) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Substring.Raw.ValidFor.foldr, hypothesis 7: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.foldr.h7 : ¬∀ {α : Type} {l : List Char} {m : List Char} {r : List Char} (f : Char → α → α) (init : α) {s : Substring.Raw},
        Substring.Raw.Legacy.foldr f init s = List.foldr f init m := fun hc_h => absurd (@hc_h (Nat) ([]) (['a']) ([]) (fun (a : Char) (n : Nat) => n + 1) (0) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Batteries.UnionFind.root_link, hypothesis 4: necessary
/- FAILED: 2:254: Application type mismatch: The argument
  ⟨1, ⋯⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨1, of_decide_eq_true (id (Eq.refl true))⟩ | 5:179: Application type mismatch: The argument
  ⟨1, ⋯⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨1, of_decide_eq_true (id (Eq.refl true))⟩ | 2:254: Application type mismatch: The argument
  ⟨1, ?m.19⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨1, ?m.19⟩ | 5:179: Application type mismatch: The argument
  ⟨1, ?m.8⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨1, ?m.8⟩ | 9:277: Application type mismatch: The argument
  ⟨1, ⋯⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨1, of_decide_eq_true (id (Eq.refl true))⟩ | 9:12: Application type mismatch: The argument
  ⟨0, ⋯⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  ↑⟨0, ⋯⟩ | 7:277: Application type mismatch: The argument
  ⟨1, ?m.17⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  @hc_h (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨1, ?m.17⟩ | 9:12: Application type mismatch: The argument
  ⟨0, ?m.1⟩
has type
  Fin 2
but is expected to have type
  Fin (Batteries.UnionFind.empty.push.push.union! 0 1).size
in the application
  ↑⟨0, ?m.1⟩
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.root_link.h4 : ¬∀ {self : Batteries.UnionFind} {x y : Fin self.size}, self.parent ↑x = ↑x → self.parent ↑y = ↑y := fun hc_h => absurd (@hc_h (Batteries.UnionFind.empty.push.push.union! 0 1 : Batteries.UnionFind) ((⟨1, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (by
  decide +kernel)) (by
  decide +kernel)
-/

-- List.idxOfNth_mono, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_mono.h6 : ¬∀ {α : Type} {n m : Nat} {x : α} [inst : BEq α] {xs : List α}, List.idxOfNth x xs n ≤ List.idxOfNth x xs m := fun hc_h => absurd (@hc_h (Nat) (1) (0) (0) (instBEqOfDecidableEq) ([0])) (by
  decide +kernel)

-- Fin.foldr_assoc, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.foldr_assoc.h3 : ¬∀ {α : Type} {n : Nat} {op : α → α → α} {f : Fin n → α} {a₁ a₂ : α},
        Fin.foldr n (fun (i : Fin n) (x : α) => op (f i) x) (op a₁ a₂) =
          op (Fin.foldr n (fun (i : Fin n) (x : α) => op (f i) x) a₁) a₂ := fun hc_h => absurd (@hc_h (Bool) (1) (fun a b => !a || b : Bool → Bool → Bool) (fun (a : Fin 1) => Bool.false) (Bool.false) (Bool.false)) (by
  decide +kernel)

-- Batteries.OrderedAssocList.headKey?_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.headKey?_cons.h6 : Not
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

-- List.idxOfNth_cons_succ_of_beq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.idxOfNth_cons_succ_of_beq.h6 : ¬∀ {α : Type} {x : α} {xs : List α} {n : Nat} {a : α} [inst : BEq α],
        List.idxOfNth x (a :: xs) (n + 1) = List.idxOfNth x xs n + 1 := fun hc_h => absurd (@hc_h (Nat) (0) ([0]) (0) (1) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- List.ge_of_mem_idxsOf, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.ge_of_mem_idxsOf.h6 : ¬∀ {α : Type} {xs : List α} {x : α} {s : Nat} [inst : BEq α] (y : Nat), s ≤ y := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (1) (instBEqOfDecidableEq) (0)) (by
  decide +kernel)

-- Batteries.AssocList.KeysOrdered.tail, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.AssocList.KeysOrdered.tail.h6 : ¬∀ {α : Type} {cmp : α → α → Ordering} {a : α} {β : Type} {b : β} {t : Batteries.AssocList α β},
        Batteries.AssocList.KeysOrdered cmp t := fun hc_h => absurd (@hc_h (Nat) (fun a b => compare a b : Nat → Nat → Ordering) (0) (Nat) (0) (Batteries.AssocList.cons 0 0 (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil))) (by
  decide +kernel)

-- List.le_getElem_idxsOf, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.le_getElem_idxsOf.h6 : ¬∀ {α : Type} {i : Nat} {xs : List α} {x : α} {s : Nat} [inst : BEq α], i < (List.idxsOf x xs s).length := fun hc_h => absurd (@hc_h (Nat) (0) ([]) (0) (0) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- Batteries.OrderedAssocList.headKey?_mk_cons, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.OrderedAssocList.headKey?_mk_cons.h6 : ¬∀ {α : Type} {a : α} {β : Type} {b : β} {t : Batteries.AssocList α β} {cmp : α → α → Ordering},
        Batteries.AssocList.KeysOrdered cmp (Batteries.AssocList.cons a b t) := fun hc_h => absurd (@hc_h (Nat) (0) (Nat) (0) (Batteries.AssocList.cons 0 0 Batteries.AssocList.nil) (fun a b => compare a b : Nat → Nat → Ordering)) (by
  decide +kernel)

-- List.countBefore_cons_succ_of_beq, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.countBefore_cons_succ_of_beq.h6 : ¬∀ {α : Type} {x : α} {xs : List α} {i : Nat} {a : α} [inst : BEq α],
        List.countBefore x (a :: xs) (i + 1) = List.countBefore x xs i + 1 := fun hc_h => absurd (@hc_h (Nat) (0) ([]) (0) (1) (instBEqOfDecidableEq)) (by
  decide +kernel)

-- Substring.Raw.ValidFor.next, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.next.h6 : ¬∀ {l : List Char} {m₁ : List Char} {c : Char} {m₂ r : List Char} {s : Substring.Raw},
        s.next { byteIdx := String.utf8Len m₁ : String.Pos.Raw } =
          { byteIdx := String.utf8Len m₁ + c.utf8Size : String.Pos.Raw } := fun hc_h => absurd (@hc_h ([]) ([]) ('a') ([]) ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Std.LawfulCmp.isLE_iff_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.LawfulCmp.isLE_iff_le.h4 : ¬∀ {α : Type} {inst : LE α} {inst_1 : LT α} {cmp : α → α → Ordering} {x y : α}, (cmp x y).isLE = Bool.true ↔ x ≤ y := fun hc_h => absurd (@hc_h (Nat) (instLENat) (instLTNat) (fun a b => compare (a / 2) (b / 2) : Nat → Nat → Ordering) (1) (0)) (by
  decide +kernel)

-- List.getElem_getElem_idxsOf_sub, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_getElem_idxsOf_sub.h6 : ¬∀ {α : Type} {i : Nat} {xs : List α} {x : α} [inst : BEq α] (s : Nat), i < (List.idxsOf x xs s).length := fun hc_h => absurd (@hc_h (Nat) (0) ([]) (0) (instBEqOfDecidableEq) (0)) (by
  decide +kernel)

-- Substring.Raw.ValidFor.get, hypothesis 6: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.get.h6 : ¬∀ {l : List Char} {m₁ : List Char} {c : Char} {m₂ r : List Char} {s : Substring.Raw},
        s.get { byteIdx := String.utf8Len m₁ : String.Pos.Raw } = c := fun hc_h => absurd (@hc_h ([]) ([]) ('a') ([]) ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Substring.Raw.ValidFor.nextn, hypothesis 5: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.nextn.h5 : ¬∀ {l : List Char} {m₁ m₂ : List Char} {r : List Char} {s : Substring.Raw} (n : Nat),
        s.nextn n { byteIdx := String.utf8Len m₁ : String.Pos.Raw } =
          { byteIdx := String.utf8Len m₁ + String.utf8Len (List.take n m₂) : String.Pos.Raw } := fun hc_h => absurd (@hc_h ([]) ([]) (['a']) ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) (1)) (by
  decide +kernel)

-- List.disjoint_of_disjoint_cons_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.disjoint_of_disjoint_cons_left.h4 : ¬∀ {α : Type} {a : α} {l₁ l₂ : List α}, l₁.Disjoint l₂ := fun hc_h => absurd (@hc_h (Nat) (0) ([0]) ([0])) (by
  simp)

-- List.Subperm.filter, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.filter.h4 : ¬∀ {α : Type} (p : α → Bool) ⦃l l' : List α⦄, (List.filter p l).Subperm (List.filter p l') := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) ([0]) ([])) (by
  decide +kernel)

-- List.Subperm.countP_le, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.countP_le.h4 : ¬∀ {α : Type} (p : α → Bool) {l₁ l₂ : List α}, List.countP p l₁ ≤ List.countP p l₂ := fun hc_h => absurd (@hc_h (Nat) (fun n => n % 2 == 0 : Nat → Bool) ([0]) ([])) (by
  decide +kernel)

-- List.Perm.subperm_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Perm.subperm_left.h4 : ¬∀ {α : Type} {l l₁ l₂ : List α}, l.Subperm l₁ ↔ l.Subperm l₂ := fun hc_h => absurd (@hc_h (Nat) ([0]) ([]) ([0])) (by
  decide +kernel)

-- Batteries.BinaryHeap.size_replaceMax_of_empty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.size_replaceMax_of_empty.h3 : ¬∀ {α : Type} [inst : Ord α] {heap : Batteries.BinaryHeap α} (x : α), (heap.replaceMax x).snd.size = 1 := fun hc_h => absurd (@hc_h (Nat) (instOrdNat) ({ arr := #[0, 1] : Batteries.BinaryHeap Nat }) (0)) (by
  decide +kernel)

-- ByteArray.get_extract, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ByteArray.get_extract.h4 : ¬∀ {i : Nat} {a : ByteArray} {start stop : Nat}, i < (a.extract start stop).size := fun hc_h => absurd (@hc_h (0) ({ data := #[] : ByteArray }) (0) (0)) (by
  decide +kernel)

-- Std.OrientedCmp.le_iff_ge, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.OrientedCmp.le_iff_ge.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering} {x y : α}, cmp x y ≠ Ordering.gt ↔ cmp y x ≠ Ordering.lt := fun hc_h => absurd (@hc_h (Bool) (fun _ _ => .lt : Bool → Bool → Ordering) (Bool.false) (Bool.false)) (by
  decide +kernel)

-- Nat.toFinDigitsFixed_add, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toFinDigitsFixed_add.h4 : ¬∀ {base : Nat} {n prec k : Nat}, NeZero base := fun hc_h => absurd (@hc_h (0) (0) (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.replaceF_cons_of_none, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.replaceF_cons_of_none.h4 : ¬∀ {α : Type} {a : α} {l : List α} (p : α → Option α), List.replaceF p (a :: l) = a :: List.replaceF p l := fun hc_h => absurd (@hc_h (Nat) (0) ([]) (fun n => some (n + 1) : Nat → Option Nat)) (by
  decide +kernel)

-- Batteries.TotalBLE.total, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.TotalBLE.total.h2 : ¬∀ {α : Type} {le : α → α → Bool} {a b : α}, le a b = Bool.true ∨ le b a = Bool.true := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (0) (0)) (by
  decide +kernel)

-- Std.instTransCmpCompareOnOfTransOrd_batteries, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.instTransCmpCompareOnOfTransOrd_batteries.h3 : ¬∀ {β α : Type} [inst : Ord β] (f : α → β), Std.TransCmp (compareOn f) := fun hc_h => absurd (@hc_h (Nat) (Nat) (⟨fun a b => if a = b then .eq else .lt⟩ : Ord Nat) (fun n => n + 1 : Nat → Nat)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- List.IsChain.pairwise, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.IsChain.pairwise.h4 : ¬∀ {α : Type} {R : α → α → Prop} {l : List α} [inst : Trans R R R], List.Pairwise R l := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Prop) ([1, 0]) (Nat.instTransLt)) (by
  decide +kernel)

-- Batteries.PairingHeapImp.Heap.size_tail?_lt, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.PairingHeapImp.Heap.size_tail?_lt.h4 : ¬∀ {α : Type} {le : α → α → Bool} {s' s : Batteries.PairingHeapImp.Heap α}, s'.size < s.size := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (Batteries.PairingHeapImp.Heap.nil) (Batteries.PairingHeapImp.Heap.nil)) (by
  decide +kernel)

-- Batteries.PairingHeapImp.Heap.noSibling_tail?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.PairingHeapImp.Heap.noSibling_tail?.h4 : ¬∀ {α : Type} {le : α → α → Bool} {s' : Batteries.PairingHeapImp.Heap α} {s : Batteries.PairingHeapImp.Heap α},
        s'.NoSibling := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (Batteries.PairingHeapImp.Heap.node 0 Batteries.PairingHeapImp.Heap.nil
      (Batteries.PairingHeapImp.Heap.node 0 Batteries.PairingHeapImp.Heap.nil Batteries.PairingHeapImp.Heap.nil)) (Batteries.PairingHeapImp.Heap.nil)) (by
  decide +kernel)

-- Batteries.BinaryHeap.insertExtractMax_fst_of_empty, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinaryHeap.insertExtractMax_fst_of_empty.h3 : ¬∀ {α : Type} [inst : Ord α] {heap : Batteries.BinaryHeap α} (x : α), (heap.insertExtractMax x).fst = x := fun hc_h => absurd (@hc_h (Nat) (instOrdNat) ({ arr := #[1] : Batteries.BinaryHeap Nat }) (0)) (by
  decide +kernel)

-- List.getElem_swap_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_swap_right.h4 : ¬∀ {α : Type} {xs : List α} {i j : Nat}, j < (xs.swap i j).length := fun hc_h => absurd (@hc_h (Nat) ([]) (0) (0)) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.setCurr, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.setCurr.h4 : ¬∀ {l : List Char} {c : Char} {r : List Char} {it : String.Legacy.Iterator},
        String.Legacy.Iterator.ValidFor l (c :: r) (it.setCurr c) := fun hc_h => absurd (@hc_h ([]) ('a') ([]) ({ s := "", i := { : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- Substring.Raw.ValidFor.isEmpty, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.isEmpty.h4 : ¬∀ {l : List Char} {m : List Char} {r : List Char} {s : Substring.Raw}, s.isEmpty = Bool.true ↔ m = [] := fun hc_h => absurd (@hc_h ([]) (['a']) ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Fin.exists_eq_some_of_findSome?_eq_some, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.exists_eq_some_of_findSome?_eq_some.h4 : ¬∀ {n : Nat} {α : Type} {x : α} {f : Fin n → Option α}, ∃ (i : Fin n), f i = Option.some x := fun hc_h => absurd (@hc_h (0) (Nat) (0) (fun (a : Fin 0) => Option.none)) (by
  decide +kernel)

-- String.Legacy.length_eq_of_map_eq, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.length_eq_of_map_eq.h4 : ¬∀ {a b : String} {f g : Char → Char}, a.length = b.length := fun hc_h => absurd (@hc_h ("") ("a") (fun (a : Char) => 'a') (fun (a : Char) => 'a')) (by
  decide +kernel)

-- List.getElem_findIdxs_eq_findIdxNth, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_findIdxs_eq_findIdxNth.h4 : ¬∀ {α : Type} {n : Nat} {p : α → Bool} {xs : List α}, n < (List.findIdxs p xs).length := fun hc_h => absurd (@hc_h (Nat) (0) (fun n => n % 2 == 0 : Nat → Bool) ([])) (by
  decide +kernel)

-- String.utf8GetAux_of_valid, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.utf8GetAux_of_valid.h4 : ¬∀ (cs cs' : List Char) {i p : Nat},
        String.Pos.Raw.utf8GetAux (cs ++ cs') { byteIdx := i : String.Pos.Raw } { byteIdx := p : String.Pos.Raw } =
          cs'.headD Inhabited.default := fun hc_h => absurd (@hc_h (['a']) ([]) (0) (0)) (by
  decide +kernel)

-- Vector.swap_last_pop_perm, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.swap_last_pop_perm.h4 : ¬∀ {α : Type} {n : Nat} {v : Vector α (n + 1)} {i : Fin (n + 1)}, ↑i < n := fun hc_h => absurd (@hc_h (Nat) (0) (#v[0]) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- Substring.Raw.ValidFor.startPos, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.ValidFor.startPos.h4 : ¬∀ {l : List Char} {m r : List Char} {s : Substring.Raw}, s.startPos = { byteIdx := String.utf8Len l : String.Pos.Raw } := fun hc_h => absurd (@hc_h (['a']) ([]) ([]) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- List.disjoint_of_disjoint_append_left_left, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.disjoint_of_disjoint_append_left_left.h4 : ¬∀ {α : Type} {l₁ : List α} {l₂ : List α} {l : List α}, l₁.Disjoint l := fun hc_h => absurd (@hc_h (Nat) ([0]) ([]) ([0])) (by
  simp)

-- Batteries.UnionFind.rankD_set, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.rankD_set.h4 : ¬∀ {arr : Array Batteries.UFNode} {x : Nat} {v : Batteries.UFNode} {i : Nat}, x < arr.size := fun hc_h => absurd (@hc_h (#[]) (0) ({ parent := 0, rank := 0 : Batteries.UFNode }) (0)) (by
  decide +kernel)

-- Batteries.UnionFind.parentD_set, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.parentD_set.h4 : ¬∀ {arr : Array Batteries.UFNode} {x : Nat} {v : Batteries.UFNode} {i : Nat}, x < arr.size := fun hc_h => absurd (@hc_h (#[]) (0) ({ parent := 0, rank := 0 : Batteries.UFNode }) (0)) (by
  decide +kernel)

-- Batteries.UnionFind.parent_link, hypothesis 3: necessary
/- FAILED: 2:262: Application type mismatch: The argument
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
  @hc_h (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨0, of_decide_eq_true (id (Eq.refl true))⟩ | 2:262: Application type mismatch: The argument
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
  @hc_h (Batteries.UnionFind.empty.push.push.union! 0 1) ⟨0, ?m.8⟩ | 5:287: Application type mismatch: The argument
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
  ↑⟨0, ⋯⟩ | 4:287: Application type mismatch: The argument
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
theorem HypCheckProof.Batteries.UnionFind.parent_link.h3 : ¬∀ {self : Batteries.UnionFind} {x : Fin self.size} {y : Fin self.size} {i : Nat}, self.parent ↑y = ↑y := fun hc_h => absurd (@hc_h (Batteries.UnionFind.empty.push.push.union! 0 1 : Batteries.UnionFind) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2)) (0)) (by
  decide +kernel)
-/

-- Eq.congr_right, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Eq.congr_right.h4 : ¬∀ {α : Type} {x y z : α}, z = x ↔ z = y := fun hc_h => absurd (@hc_h (Nat) (0) (1) (0)) (by
  decide +kernel)

-- Batteries.BinomialHeap.Imp.Heap.realSize_tail?, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.BinomialHeap.Imp.Heap.realSize_tail?.h4 : ¬∀ {α : Type} {le : α → α → Bool} {s' s : Batteries.BinomialHeap.Imp.Heap α}, s.realSize = s'.realSize + 1 := fun hc_h => absurd (@hc_h (Nat) (fun a b => a < b : Nat → Nat → Bool) (Batteries.BinomialHeap.Imp.Heap.nil) (Batteries.BinomialHeap.Imp.Heap.nil)) (by
  decide +kernel)

-- Std.ReflCmp.compareOfLessAndEq_of_lt_irrefl, hypothesis 4: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.ReflCmp.compareOfLessAndEq_of_lt_irrefl.h4 : ¬∀ {α : Type} [inst : LT α] [inst_1 : DecidableLT α] [inst_2 : DecidableEq α],
        Std.ReflCmp fun (x1 x2 : α) => compareOfLessAndEq x1 x2 := fun hc_h => absurd (@hc_h (Nat) (⟨fun a b => a ≤ b⟩ : LT Nat) (fun (a b : Nat) => a.decLe b) (instDecidableEqNat)) (by
  exact fun hc_c =>
    absurd (hc_c.compare_self (a := (0 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Fin.findSome?_succ_of_isSome, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.findSome?_succ_of_isSome.h3 : ¬∀ {n : Nat} {α : Type} {f : Fin (n + 1) → Option α}, Fin.findSome? f = f 0 := fun hc_h => absurd (@hc_h (1) (Nat) (fun (a : Fin (1 + 1)) =>
      if a = (⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 2) then Option.none else Option.some 0)) (by
  decide +kernel)

-- Fin.eq_true_of_findRev?_eq_some, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.eq_true_of_findRev?_eq_some.h3 : ¬∀ {n : Nat} {i : Fin n} {p : Fin n → Bool}, p i = Bool.true := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (fun (a : Fin 1) => Bool.false)) (by
  decide +kernel)

-- List.getElem_flatten, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_flatten.h3 : ¬∀ {α : Type} (L : List (List α)) (i : Nat), i < L.flatten.length := fun hc_h => absurd (@hc_h (Nat) ([]) (0)) (by
  decide +kernel)

-- Int.testBit_ofBits_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Int.testBit_ofBits_lt.h3 : ¬∀ {n i : Nat} {f : Fin n → Bool}, i < n := fun hc_h => absurd (@hc_h (0) (0) (fun (a : Fin 0) => Bool.false)) (by
  decide +kernel)

-- Fin.exists_isSome_of_isSome_findSomeRev?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.exists_isSome_of_isSome_findSomeRev?.h3 : ¬∀ {n : Nat} {α : Type} {f : Fin n → Option α}, ∃ (i : Fin n), (f i).isSome = Bool.true := fun hc_h => absurd (@hc_h (0) (Nat) (fun (a : Fin 0) => Option.none)) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.pos_eq_zero, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.pos_eq_zero.h3 : ¬∀ {l : List Char} {r : List Char} {it : String.Legacy.Iterator}, it.i = 0 ↔ l = [] := fun hc_h => absurd (@hc_h ([]) ([]) ({ s := "", i := { byteIdx := 1 : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.hasPrev, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.hasPrev.h3 : ¬∀ {l : List Char} {r : List Char} {it : String.Legacy.Iterator}, it.hasPrev = Bool.true ↔ l ≠ [] := fun hc_h => absurd (@hc_h ([]) ([]) ({ s := "", i := { byteIdx := 1 : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- Fin.eq_false_of_find?_eq_none, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.eq_false_of_find?_eq_none.h2 : ¬∀ {n : Nat} {p : Fin n → Bool} (i : Fin n), p i = Bool.false := fun hc_h => absurd (@hc_h (1) (fun (a : Fin 1) => Bool.true) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1))) (by
  decide +kernel)

-- String.Legacy.Iterator.ValidFor.out', hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Legacy.Iterator.ValidFor.out'.h3 : ¬∀ {l r : List Char} {it : String.Legacy.Iterator},
        it =
          { s := String.ofList (l.reverse ++ r), i := { byteIdx := String.utf8Len l.reverse : String.Pos.Raw } :
            String.Legacy.Iterator } := fun hc_h => absurd (@hc_h ([]) ([]) ({ s := "", i := { byteIdx := 1 : String.Pos.Raw } : String.Legacy.Iterator })) (by
  decide +kernel)

-- List.getElem_zero_findIdxs_eq_findIdx, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_zero_findIdxs_eq_findIdx.h3 : ¬∀ {α : Type} {xs : List α} {p : α → Bool}, 0 < (List.findIdxs p xs).length := fun hc_h => absurd (@hc_h (Nat) ([]) (fun n => n % 2 == 0 : Nat → Bool)) (by
  decide +kernel)

-- ByteArray.get_push_lt, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ByteArray.get_push_lt.h3 : ¬∀ (a : ByteArray) (x : UInt8) (i : Nat), i < a.size := fun hc_h => absurd (@hc_h ({ data := #[] : ByteArray }) (UInt8.ofNat 0) (0)) (by
  decide +kernel)

-- Fin.exists_isSome_of_isSome_findSome?, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.exists_isSome_of_isSome_findSome?.h3 : ¬∀ {n : Nat} {α : Type} {f : Fin n → Option α}, ∃ (i : Fin n), (f i).isSome = Bool.true := fun hc_h => absurd (@hc_h (0) (Nat) (fun (a : Fin 0) => Option.none)) (by
  decide +kernel)

-- Fin.isSome_find?_of_eq_true, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.isSome_find?_of_eq_true.h3 : ¬∀ {n : Nat} {i : Fin n} {p : Fin n → Bool}, (Fin.find? p).isSome = Bool.true := fun hc_h => absurd (@hc_h (1) ((⟨0, of_decide_eq_true (id (Eq.refl Bool.true))⟩ : Fin 1)) (fun (a : Fin 1) => Bool.false)) (by
  decide +kernel)

-- List.reverse_interleave_of_length_eq_length_add_one, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.reverse_interleave_of_length_eq_length_add_one.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, (l₁.interleave l₂).reverse = l₁.reverse.interleave l₂.reverse := fun hc_h => absurd (@hc_h (Nat) ([0]) ([1])) (by
  decide +kernel)

-- List.Subperm.length_le, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.Subperm.length_le.h3 : ¬∀ {α : Type} {l₁ l₂ : List α}, l₁.length ≤ l₂.length := fun hc_h => absurd (@hc_h (Nat) ([0]) ([])) (by
  decide +kernel)

-- List.getElem_flatten_aux₂, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.List.getElem_flatten_aux₂.h3 : ¬∀ {α : Type} (L : List (List α)) (i : Nat), i < L.flatten.length := fun hc_h => absurd (@hc_h (Nat) ([]) (0)) (by
  decide +kernel)

-- ByteArray.getElem_ofFn, hypothesis 3: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.ByteArray.getElem_ofFn.h3 : ¬∀ {n : Nat} (f : Fin n → UInt8) (i : Nat), i < (ByteArray.ofFn f).size := fun hc_h => absurd (@hc_h (0) (fun (a : Fin 0) => UInt8.ofNat 0) (0)) (by
  decide +kernel)

-- Vector.tail_eq_of_ne_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Vector.tail_eq_of_ne_zero.h2 : ¬∀ {n : Nat} {α : Type} {v : Vector α n}, NeZero n := fun hc_h => absurd (@hc_h (0) (Nat) (#v[])) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.avg_le_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.avg_le_right.h2 : ¬∀ {a b : Nat}, a.avg b ≤ b := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

-- Char.eq_false_of_any_eq_false, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.eq_false_of_any_eq_false.h1 : ¬∀ {p : Char → Bool} (c : Char), p c = Bool.false := fun hc_h => absurd (@hc_h (fun (a : Char) => Bool.true) ('a')) (by
  decide +kernel)

-- Substring.Raw.Valid.all, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.all.h2 : ¬∀ (f : Char → Bool) {s : Substring.Raw}, Substring.Raw.Legacy.all s f = s.toString.toList.all f := fun hc_h => absurd (@hc_h (fun (a : Char) => Bool.false) ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { byteIdx := 1 : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Nat.le_add_one_of_avg_eq_right, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_add_one_of_avg_eq_right.h2 : ¬∀ {a b : Nat}, a ≤ b + 1 := fun hc_h => absurd (@hc_h (2) (0)) (by
  decide +kernel)

-- Substring.Raw.Valid.nextn_stop, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.nextn_stop.h1 : ¬∀ {s : Substring.Raw} (n : Nat),
        s.nextn n { byteIdx := s.bsize : String.Pos.Raw } = { byteIdx := s.bsize : String.Pos.Raw } := fun hc_h => absurd (@hc_h ({ str := "", startPos := { byteIdx := 1 : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw }) (1)) (by
  decide +kernel)

-- Nat.le_avg_left, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.le_avg_left.h2 : ¬∀ {a b : Nat}, a ≤ a.avg b := fun hc_h => absurd (@hc_h (1) (0)) (by
  decide +kernel)

-- Batteries.UnionFind.rankD_lt, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Batteries.UnionFind.rankD_lt.h2 : ¬∀ (self : Batteries.UnionFind) {i : Nat},
        Batteries.UnionFind.rankD self.arr i < Batteries.UnionFind.rankD self.arr (Batteries.UnionFind.parentD self.arr i) := fun hc_h => absurd (@hc_h (Batteries.UnionFind.empty : Batteries.UnionFind) (0)) (by
  decide +kernel)

-- Fin.exists_eq_true_of_isSome_findRev?, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.exists_eq_true_of_isSome_findRev?.h2 : ¬∀ {n : Nat} {p : Fin n → Bool}, ∃ (i : Fin n), p i = Bool.true := fun hc_h => absurd (@hc_h (0) (fun (a : Fin 0) => Bool.false)) (by
  decide +kernel)

-- Nat.ofFinDigits_toFinDigits, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.ofFinDigits_toFinDigits.h2 : ¬∀ {base n : Nat}, Nat.ofFinDigits (n.toFinDigits base) = n := fun hc_h => absurd (@hc_h (0) (1)) (by
  decide +kernel)

-- Nat.toFinDigitsFixed_ofFinDigits, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toFinDigitsFixed_ofFinDigits.h1 : ¬∀ {base : Nat} {l : List (Fin base)}, NeZero base := fun hc_h => absurd (@hc_h (0) ([])) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Classical.exists_not_of_not_forall, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Classical.exists_not_of_not_forall.h2 : ¬∀ {α : Type} {p : α → Prop}, ∃ (x : α), ¬p x := fun hc_h => absurd (@hc_h (Nat) (fun _ => True : Nat → Prop)) (by
  simp)

-- subsingleton_of_forall_eq, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.subsingleton_of_forall_eq.h2 : ¬∀ {α : Type} (x : α), Subsingleton α := fun hc_h => absurd (@hc_h (Nat) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.allEq (0 : Nat) (1 : Nat))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Nat.toFinDigitsFixed_zero, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Nat.toFinDigitsFixed_zero.h2 : ¬∀ {base : Nat} {n : Nat}, NeZero base := fun hc_h => absurd (@hc_h (0) (0)) (by
  exact fun hc_c =>
    absurd (hc_c.out)
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- USize.ext, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.USize.ext.h2 : ¬∀ {x y : USize}, x = y := fun hc_h => absurd (@hc_h (USize.ofNat 0) (USize.ofNat 1)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- String.Pos.Raw.Valid.exists, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.String.Pos.Raw.Valid.exists.h2 : ¬∀ {s : String} {p : String.Pos.Raw},
        ∃ (cs : List Char),
          ∃ (cs' : List Char), String.ofList (cs ++ cs') = s ∧ p = { byteIdx := String.utf8Len cs : String.Pos.Raw } := fun hc_h => absurd (@hc_h ("") ({ byteIdx := 1 : String.Pos.Raw })) (by
  simp)

-- Fin.get_findRev?_eq_true, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Fin.get_findRev?_eq_true.h2 : ¬∀ {n : Nat} {p : Fin n → Bool}, (Fin.findRev? p).isSome = Bool.true := fun hc_h => absurd (@hc_h (0) (fun (a : Fin 0) => Bool.false)) (by
  decide +kernel)

-- UInt16.ext, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.UInt16.ext.h2 : ¬∀ {x y : UInt16}, x = y := fun hc_h => absurd (@hc_h (UInt16.ofNat 0) (UInt16.ofNat 1)) (by
  decide +kernel)

-- Std.instTransCmpFlipOrdering_batteries, hypothesis 2: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.instTransCmpFlipOrdering_batteries.h2 : ¬∀ {α : Type} {cmp : α → α → Ordering}, Std.TransCmp (flip cmp) := fun hc_h => absurd (@hc_h (Nat) (fun a b => if a = b then .eq else .lt : Nat → Nat → Ordering)) (by
  exact fun hc_c =>
    absurd (hc_c.toOrientedCmp.eq_swap (a := (0 : Nat)) (b := (1 : Nat)))
      (by
        first
        | decide +kernel
        | (dsimp only <;> decide +kernel)))

-- Char.toUpper_eq_of_not_isLower, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.toUpper_eq_of_not_isLower.h1 : ¬∀ {c : Char}, c.toUpper = c := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- Char.exists_eq_false_of_all_eq_false, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.exists_eq_false_of_all_eq_false.h1 : ¬∀ {p : Char → Bool}, ∃ (c : Char), p c = Bool.false := fun hc_h => absurd (@hc_h (fun (a : Char) => Bool.true)) (by
  simp)

-- Char.isAscii_of_isWhitespace, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.isAscii_of_isWhitespace.h1 : ¬∀ {c : Char}, c.isAscii = Bool.true := fun hc_h => absurd (@hc_h ('é')) (by
  decide +kernel)

-- USize.pred_toNat, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.USize.pred_toNat.h1 : ¬∀ {i : USize}, (i - 1).toNat = i.toNat - 1 := fun hc_h => absurd (@hc_h (USize.ofNat 0)) (by
  (rcases System.Platform.numBits_eq with hc_nb | hc_nb <;>
        simp_all [USize.size, ISize.size, USize.toNat_ofNat, ← USize.toNat_inj, USize.toBitVec_ofNat, ← BitVec.toNat_inj,
          BitVec.toNat_ofNat, USize.toNat_toBitVec, ← ISize.toInt_inj, ISize.toInt_ofInt, USize.toNat_add,
          USize.toNat_mul, USize.toNat_sub, USize.toNat_div, USize.toNat_mod, USize.toNat_toUInt32, USize.toNat_toUInt64,
          ← UInt32.toNat_inj, ← UInt64.toNat_inj, USize.le_iff_toNat_le] <;>
      first
      | done
      | omega
      | decide))

-- Substring.Raw.Valid.isEmpty, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.isEmpty.h1 : ¬∀ {s : Substring.Raw}, s.isEmpty = Bool.true ↔ s.toString = "" := fun hc_h => absurd (@hc_h ({ str := "", startPos := { : String.Pos.Raw }, stopPos := { byteIdx := 1 : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Char.isAscii_of_isUpper, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.isAscii_of_isUpper.h1 : ¬∀ {c : Char}, c.isAscii = Bool.true := fun hc_h => absurd (@hc_h ('é')) (by
  decide +kernel)

-- Char.isAscii_of_isDigit, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.isAscii_of_isDigit.h1 : ¬∀ {c : Char}, c.isAscii = Bool.true := fun hc_h => absurd (@hc_h ('é')) (by
  decide +kernel)

-- Char.toLower_eq_of_not_isUpper, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.toLower_eq_of_not_isUpper.h1 : ¬∀ {c : Char}, c.toLower = c := fun hc_h => absurd (@hc_h ('A')) (by
  decide +kernel)

-- Char.not_isUpper_of_isLower, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.not_isUpper_of_isLower.h1 : ¬∀ {c : Char}, ¬c.isUpper = Bool.true := fun hc_h => absurd (@hc_h ('A')) (by
  decide +kernel)

-- Char.toLower_eq_of_isUpper, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.toLower_eq_of_isUpper.h1 : ¬∀ {c : Char}, c.toLower = Char.ofNat (c.toNat + 32) := fun hc_h => absurd (@hc_h ('a')) (by
  decide +kernel)

-- Std.Legacy.Range.size_stop_le_start, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Std.Legacy.Range.size_stop_le_start.h1 : ¬∀ (r : Std.Legacy.Range), r.size = 0 := fun hc_h => absurd (@hc_h ([:1])) (by
  decide +kernel)

-- Substring.Raw.Valid.next_stop, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Substring.Raw.Valid.next_stop.h1 : ¬∀ {s : Substring.Raw}, s.next { byteIdx := s.bsize : String.Pos.Raw } = { byteIdx := s.bsize : String.Pos.Raw } := fun hc_h => absurd (@hc_h ({ str := "", startPos := { byteIdx := 1 : String.Pos.Raw }, stopPos := { : String.Pos.Raw } : Substring.Raw })) (by
  decide +kernel)

-- Char.isAscii_of_isLower, hypothesis 1: necessary
set_option maxHeartbeats 6000 in
theorem HypCheckProof.Char.isAscii_of_isLower.h1 : ¬∀ {c : Char}, c.isAscii = Bool.true := fun hc_h => absurd (@hc_h ('é')) (by
  decide +kernel)

